open Xi_lib
open Iface

module type PARAMS = sig
    val stop_point : string
    val output: string
end

module Make(Steps:COMPILER_STEPS)(Params:PARAMS) = struct

  module Hack = Xi_lib.Analysis

  open Params
  module Toolbox = Steps.Toolbox

  module Parser_wrapper = Parser_wrapper.Make(Steps.LexerAndParser)

  let check_stop_point name cont x =
    if name = stop_point then Ok ()
    else cont x


  let describe_register_mapping mapping =
    let describe_map k v xs =
      let entry = Format.sprintf "%s -> %s" (Ir_utils.string_of_reg k) (Ir_utils.string_of_reg v) in
      entry :: xs
    in
    String.concat "\n" @@ Hashtbl.fold describe_map mapping []

  let dump_register_mapping proc_ir mapping =
    Logger.dump_string "regmapping" @@ describe_register_mapping mapping

  let dump_schedule proc_ir schedule = 
    let title = Format.sprintf "%s.schedule" (Ir_utils.string_of_procid proc_ir) in
    let output = Ir_utils.string_of_labellist schedule in
    Logger.dump_string title output

  let dump_node2type node2type =
    let title = "types" in 
    let f k v xs =
      let line = Format.sprintf "%s -> %s"
        (Ast.string_of_node_tag k)
        (Types.string_of_normal_type v) in
      line :: xs
    in
    let lines = Hashtbl.fold f node2type [] in
    Logger.dump_string title @@ String.concat "\n" @@ List.sort compare lines

  module IrPhases = struct

    let regalloc proc =
      let register_mapping = Steps.RegisterAllocator.regalloc proc in
      dump_register_mapping proc register_mapping;
      Ir_utils.remap_registers_proc register_mapping proc

    let scale_to_program f name ir =
      let handle_proc proc =
        Logger.new_phase_proc @@ Ir.procid_of_procedure proc;
        Measure.measure name (fun () -> f proc);
        Logger.dump_ir_proc "final.irproc" proc
      in
      Measure.measure ("whole " ^ name) (fun () ->
        List.iter handle_proc  @@ Ir.procedures_of_program ir;
        Logger.close_phase_proc ()
      );
      Logger.dump_ir_program "final.ir" ir

    let ir_phases =
      [ "jump_threading", scale_to_program Steps.JumpThreading.jump_threading
      ; "hi_lower", scale_to_program Steps.HiLower.lower
      ; "constant_folding", scale_to_program Steps.ConstantFolding.fold_constants 
      ; "dead_code_elimination", scale_to_program Steps.DeadCodeElimination.eliminate_dead_code
      ; "callconv", scale_to_program Steps.CallConv.callconv
      ; "mips_lower", scale_to_program Steps.MipsLower.lower
      ; "regalloc", scale_to_program regalloc
      ; "dead_code_elimination", scale_to_program Steps.DeadCodeElimination.eliminate_dead_code
      ]


    let rec execute_ir_phases ir = function
      | [] ->
        ()
      | (name, f)::rest ->
        Logger.new_phase name;
        f name ir;
        execute_ir_phases ir rest

    let transform_ir ir =
      execute_ir_phases ir ir_phases

  end

  let finish result =
    Format.printf "done\n";
    let out = open_out output in 
    output_string out result;
    output_string out "\n";
    close_out out;
    Ok ()

  let codegen ir =
    Logger.new_phase "codegen";
    let schedule = Toolbox.Scheduler.schedule ir in
    Hashtbl.iter dump_schedule schedule;
    let assembler = Steps.Codegen.codegen schedule ir in
    let result = Hardcoded.preamble ^ Mips32.string_of_program assembler in
    Logger.dump_string "final" result;
    finish result

  let translate (ast, node2type) =
    Logger.new_phase "translate";
    let ir = Steps.Translator.translate_module ast node2type in
    Logger.dump_ir_program "translated.ir" ir;
    IrPhases.transform_ir ir;
    codegen ir

  let type_check ast = 
    Logger.new_phase "typechecking";
    match Steps.Typechecker.check_module ast with
    | Error xs ->
      let xs = List.map Typechecker_errors.string_of_type_checking_error xs in 
      List.iter prerr_endline xs;
      Error "typechecker"
    | Ok (node2type) ->
      dump_node2type node2type;
      if Invariants.AllExpressionsAreTypecheck.verify_module_definition node2type ast then
        check_stop_point "typechecker" translate (ast, node2type)
      else
        Error "typechecker"


  let parse_step source =
    Logger.new_phase "parsing";
    match Parser_wrapper.parse_file source with
    | Error (loc, descr) ->
      Format.printf "%s: %s\n%!" (Ast.string_of_location loc) descr;
      Error "parser"

    | Ok ok ->
      let ast_str = Ast_printer.show_module_definition ok in 
      Logger.dump_string "ast" ast_str;
      let ast_str = Ast_rawprinter.show_module_definition ok in 
      Logger.dump_string "raw.ast" ast_str;
      check_stop_point "parser" type_check ok


  let compile = 
      parse_step
end
