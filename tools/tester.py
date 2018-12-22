#!/usr/bin/env python3

import argparse
import glob
import os
import sys
import subprocess
import shutil

class Configuration:
    def __init__(self, xic, testdir, spim, workdir, registers_description, plugin):
        self.xic = xic
        self.testdir = testdir
        self.spim = spim
        self.workdir = workdir
        self.registers_description = registers_description
        self.plugin = plugin

    def printself(self):
        print('Configuration:')
        print(' - xic:     ', self.xic)
        print(' - testdir: ', self.testdir)
        print(' - spim:    ', self.spim)
        print(' - workdir: ', self.workdir)
        if self.registers_description is not None:
            print(' - regdescr:', self.registers_description)
        if self.plugin:
            print(' - plugin:', self.plugin)

class TestOutput:
    class Status:
        COMPILER_FAILURE = 0
        COMPILER_SUCCES = 1
        SPIM_FAILURE = 2 
        SPIM_SUCCESS = 3

    def __init__(self):
        self.status = None
        self.compiler_stdout = None
        self.compiler_stderr = None
        self.compiler_ok = None
        self.spim_stdout = None
        self.spim_stderr = None
        self.spim_ok = None


class TestInstrumentation:
    def __init__(self, test):
        self.test = test
        self.instrumented = False
        self.expected_output = []
        self.should_parse = True
        self.stop_after = None
        self.should_typecheck = True
        self.typechecking_errors = []
        self.selftest = None
        self.env = {}

        self.parse()
        self.validate()

    def content(self):
        # get content of all comments started with //@
        lines = open(self.test).readlines()
        lines = [ line.strip() for line in lines ]
        lines = [ line for line in lines if line.startswith("//@") ]
        lines = [ line[3:] for line in lines ]
        return lines

    def parse(self):
        content = self.content()
        self.instrumented = "PRACOWNIA" in content
        if not self.instrumented:
            raise Exception('Test instrumentation is missing: %s' % self.test)

        for line in content:
            if line.startswith("out "):
                self.expected_output.append(line[4:])
            elif line == "should_not_parse":
                self.should_parse = False
            elif line == "should_not_typecheck":
                self.should_typecheck = False
            elif line.startswith("tcError "):
                self.typechecking_errors.append(line[len("tcError "):])
            elif line.startswith("stop_after"):
                self.stop_after = line[len("stop_after "):]
            elif line.startswith("env"):
                keyvalue = line[len("env "):]
                keyvalue = keyvalue.split('=')
                self.env[keyvalue[0]] = keyvalue[1]
            elif line.startswith('selftest'):
                arg = line[len('selftest'):].strip()
                if arg == 'pass':
                    self.selftest = True
                elif arg == 'fail':
                    self.selftest = False
                else:
                    raise Exception("invalid @selftest directive")

            elif line == "PRACOWNIA":
                pass
            else:
                raise Exception("invalid test instrumentation: unknown directive: " + line)

    def validate(self):
        if not self.instrumented:
            return 

        if not self.should_parse:
            if len(self.expected_output) > 0:
                raise Exception("test %s marked as @should_not_parse, but expected runtime output is specified (@out)" % self.test)
            if len(self.typechecking_errors) > 0:
                raise Exception("test %s marked as @should_not_parse, but expected typechecking errors are specified (@tcError)" % self.test)
            if not self.should_typecheck:
                raise Exception("test %s marked as @should_not_parse, but expected typechecking failure is marked (@should_not_typecheck)" % self.test)

        if not self.should_typecheck:
            if len(self.expected_output) > 0:
                raise Exception("test %s expects typechecking failure, but expected runtime output is specified (@out)" % self.test)

        if len(self.typechecking_errors):
            if len(self.expected_output) > 0:
                raise Exception("test %s expects typechecking errors, but expected runtime output is specified (@out)" % self.test)
            self.should_typecheck = False

class Test:
    def __init__(self, test, instrumentation):
        self.test = test
        self.instrumentation = instrumentation

    def expecting_parsing_error(self):
        return not self.instrumentation.should_parse

    def expecting_typechecking_error(self):
        return not self.instrumentation.should_typecheck

    def expecting_compilation_failure(self):
        return self.expecting_parsing_error() or self.expecting_typechecking_error()

    def expecting_runtime_output(self):
        return not self.expecting_compilation_failure() and not self.instrumentation.stop_after

class ExpectationMatcher:
    def __init__(self, test , output):
        self.test = test
        self.output = output 

    def __match_output(self, stdout, expected):
        actual = list(reversed(stdout))
        expected = list(reversed(expected))

        for i in range(0, len(expected)):
            if len(actual) <= i:
                # nie sprawdzam tego przed petla bo chcialbym aby najpierw zmatchowal te linijki
                # co sie rzeczywiscie na stdout pojawily
                return False, "program output is too short, it contains %u lines, while expected out has %u" % (len(actual), len(expected))

            expected_line = expected[i]
            actual_line = actual[i]
            if expected_line != actual_line:
                explanation = "mismatch on line (counting from bottom): %u\nexpected: %s\nactual: %s" % (i + 1, expected_line, actual_line)
                return False, explanation
        return True, ""

    def __real_match(self):
        # print('self.test.expecting_compilation_failure()', self.test.expecting_compilation_failure())
        # print('self.test.instrumentation.should_typecheck', self.test.instrumentation.should_typecheck)
        # print('self.output.compiler_ok', self.output.compiler_ok)
        if self.test.expecting_compilation_failure():
            xic_stderr = self.output.compiler_stderr.decode('utf8')
            xic_stderr = xic_stderr.splitlines()
            if len(xic_stderr) == 0:
                xic_last_line_stderr = None
            else:
                xic_last_line_stderr = xic_stderr[-1].strip()
            if self.output.compiler_ok:
                return False, "expected compiler failure"
            if self.test.expecting_parsing_error():
                if xic_last_line_stderr == "Failed: parser":
                    return True, ""
                return False, "expected parsing error"
            if self.test.expecting_typechecking_error():
                if xic_last_line_stderr == "Failed: typechecker":
                    return True, ""
                return False, "expected typchecking error"
        else:
            if not self.output.compiler_ok:
                return False, "program should be compiled, but compiler failed"

        if self.test.instrumentation.stop_after:
            return True, ""

        if len(self.output.spim_stderr) > 0:
            return False, "spim's stderr is not empty, execute program manually"


        if self.test.expecting_runtime_output():
            if not self.output.spim_ok:
                return False, "spim was not executed properly"

            if len(self.test.instrumentation.expected_output) > 0:
                spim_stdout = self.output.spim_stdout.decode('utf8')
                spim_stdout = spim_stdout.splitlines()
                spim_stdout = [ line.strip() for line in spim_stdout ]
                return self.__match_output(spim_stdout,self.test.instrumentation.expected_output)

            return True, ""

        return None, "cannot match test expectations"

    def match(self):
        x_result, x_explanation = self.__real_match()

        if self.test.instrumentation.selftest == None:
            result, explanation = x_result, x_explanation
        else:
            result = x_result == self.test.instrumentation.selftest
            if result:
                explanation = ""
            else:
                explanation = "selftest failed: expected %s, got: %s, %s" % (self.test.instrumentation.selftest, x_result, x_explanation)
        
        return result, explanation

class TestRawExecutor:

    def __init__(self, conf, test, env, run_spim, stop_point):
        self.conf = conf
        self.test = test
        self.env = env
        self.output_file = os.path.join(conf.workdir, 'main.s')
        self.test_output = TestOutput()
        self.run_spim = run_spim
        self.stop_point = stop_point

    def execute(self):
        self.prepare_env()
        ok, stdout, stderr = self.compile_program() 
        self.test_output.compiler_stdout = stdout
        self.test_output.compiler_stderr = stderr
        self.test_output.compiler_ok = ok
        if not ok or not self.run_spim or self.stop_point:
            self.clean_env()
            return self.test_output

        ok, stdout, stderr = self.execute_program()
        self.test_output.spim_stdout = stdout
        self.test_output.spim_stderr = stderr
        self.test_output.spim_ok = ok
        self.clean_env()

        return self.test_output

    def compile_program(self):
        xs = [self.conf.xic, '-o', self.output_file]
        if self.stop_point:
            xs.append('--stop-after')
            xs.append(self.stop_point)
        if self.conf.registers_description is not None:
            xs.append('--registers-description')
            xs.append(self.conf.registers_description)
        if self.conf.plugin is not None:
            xs.append('--plugin')
            xs.append(self.conf.plugin)

        xs.append('--xi-log')
        xs.append(os.path.join(self.conf.workdir, 'xilog'))
        xs.append(self.test)
        env = dict(self.env)
        return self.__call(xs, env)

    def execute_program(self):
        return self.__call([self.conf.spim, '-file', self.output_file])

    def prepare_env(self):
        shutil.rmtree(self.conf.workdir, ignore_errors=True)
        os.makedirs(self.conf.workdir)

    def clean_env(self):
        shutil.rmtree(self.conf.workdir, ignore_errors=True)

    def __call(self, xs, extenv={}):
        env = os.environ
        for k in extenv:
            env[k] = extenv[k]

        try:
            p = subprocess.Popen(xs, stdin=None, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)
            stdin, stdout = p.communicate(timeout=5)
            status = p.returncode == 0
            return (status, stdin, stdout)
        except subprocess.TimeoutExpired:
            return (False, [], [])
        except Exception:
            # potem cos tu doklepie aby wykonywarka testow mogla sie kapnac, ze to nie test wykryl blad
            # a cos innego
            return (False, [], [])

class TestExecutor:
    def __init__(self, test, conf):
        self.test = test
        self.conf = conf
    
    def execute(self):
        try:
            run_spim = self.test.expecting_runtime_output()
            stop_point = None
            if not run_spim:
                if self.test.expecting_parsing_error():
                    stop_point = "parser"
                elif self.test.expecting_typechecking_error():
                    stop_point = "typechecker"
                elif self.test.instrumentation.stop_after:
                    stop_point = self.test.instrumentation.stop_after

            rawExecutor = TestRawExecutor(self.conf, self.test.test, self.test.instrumentation.env, run_spim, stop_point)
            test_output = rawExecutor.execute()
            matcher = ExpectationMatcher(self.test, test_output)
            return matcher.match()
        except Exception as e:
            raise e
            return None, "internal error: " + str(e)


class TestRepository:
    def __init__(self, testdirs):
        self.tests = []
        self.collect_tests(testdirs)

    def collect_tests(self, testdirs):
        testfiles = []
        for testdir in testdirs:
            for path, _, files in os.walk(testdir):
                for file in files:
                    if file.endswith(".xi"):
                        testfiles.append(os.path.join(path, file))
        testfiles = list(sorted(testfiles))

        for testfile in testfiles:
            instrumentation = TestInstrumentation(testfile)
            test = Test(testfile, instrumentation)
            self.tests.append(test)

    def gen(self):
        for t in self.tests:
            yield t

class Application:
    def __init__(self):
        args = self.create_argparse().parse_args()
        self.conf = Configuration(xic=args.xic,
                                  testdir=args.testdir,
                                  spim=args.spim,
                                  workdir=args.workdir,
                                  registers_description=args.registers_description,
                                  plugin=args.plugin)


    def create_argparse(self):
        parser = argparse.ArgumentParser(description='Xi tester')
        parser.add_argument('--xic', help='path to xi binary', default='./_build/install/default/bin/xi', type=str)
        parser.add_argument('--spim', help='path to spim binary', default='spim', type=str)
        parser.add_argument('--testdir', help='path to test directory', default='./tests', type=str)
        parser.add_argument('--workdir', help='working directory', default='workdir', type=str)
        parser.add_argument('--registers-description', help='xi --registers-description', default=None, type=str)
        parser.add_argument('--plugin', help='xi --plugin', type=str)
        return parser

    def run(self):
        print('Xi tester')
        self.conf.printself()
        self.test_repository = TestRepository([self.conf.testdir])
        passed_tests = []
        failed_tests = []
        inconclusive_tests = []
        for test in self.test_repository.gen():
            print('==> running test', test.test)
            executor = TestExecutor(test, self.conf)
            result, explanation = executor.execute()

            if result == None:
                inconclusive_tests.append(test)
                status = "inconclusive: " + explanation
            elif result:
                passed_tests.append(test)
                status = "pass"
            elif not result:
                failed_tests.append(test)
                status = "fail: " + explanation

            print('--- result:', status)
            
        total = len(passed_tests) + len(failed_tests) + len(inconclusive_tests)

        print('===================')
        print('Total: ', total)
        print('Passed:', len(passed_tests))
        print('Inconc:', len(inconclusive_tests))
        print('Failed:', len(failed_tests))
        for test in failed_tests:
            print(' -', test.test)


Application().run()
