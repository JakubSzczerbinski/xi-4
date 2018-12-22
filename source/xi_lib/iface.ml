
type node2type = (Ast.node_tag, Types.normal_type) Hashtbl.t

type schedule = (Ir.procid, Ir.label list) Hashtbl.t

type register_mapping = (Ir.reg, Ir.reg) Hashtbl.t


module type LEXER = sig

  type token

  val token: Lexing.lexbuf -> token

end

module type PARSER = sig

  type token

  exception Error

  val file: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> Ast.module_definition

end

module type LEXER_AND_PARSER = sig

  type token

  module Lexer: LEXER with type token = token

  module Parser: PARSER with type token = token

end

module type TYPECHECKER = sig

  val check_module: Ast.module_definition -> (node2type, Typechecker_errors.type_checking_error list) result

end

module type TRANSLATOR = sig

  val translate_module: Ast.module_definition -> node2type -> Ir.program

end

module type HI_LOWER = sig

  val lower: Ir.procedure -> unit

end

module type MIPS_LOWER = sig

  val lower: Ir.procedure -> unit

end

module type CALLCONV = sig

  val callconv: Ir.procedure -> unit

end

module type REGISTER_COALESCING = sig

  val coalesce: Ir.procedure -> Ir.RegGraph.t -> Ir.reg list -> bool

end

module type REGISTER_ALLOCATOR = sig

  val regalloc: Ir.procedure -> register_mapping

end

module type CODEGEN = sig

  val codegen: schedule -> Ir.program -> Mips32.program

end

module type LIVE_VARIABLES_ANALYSIS = sig

  val analyse: Ir.ControlFlowGraph.t -> Analysis_domain.LiveVariables.table
end

module type REACHABILITY_ANALYSIS = sig

  val analyse: Ir.ControlFlowGraph.t -> Analysis_domain.ReachabilityAnalysis.table

end

module type CONSTANT_FOLDING_ANALYSIS = sig

  val analyse: Ir.procedure -> Analysis_domain.ConstantFolding.table

end

module type JUMP_THREADING = sig

  val jump_threading: Ir.procedure -> unit

end

module type CONSTANT_FOLDING = sig

  val fold_constants: Ir.procedure -> unit

end

module type DEAD_CODE_ELIMINATION = sig

  val eliminate_dead_code: Ir.procedure -> unit

end

module type DOMINATORS_ANALYSIS = sig

  val analyse: Ir.ControlFlowGraph.t -> Analysis_domain.DominatorsAnalysis.table

end

module type NATURAL_LOOPS_ANALYSIS = sig

  val analyse: Ir.ControlFlowGraph.t -> Analysis_domain.DominatorsAnalysis.table -> Analysis_domain.NaturalLoops.table

end

module type SCHEDULER = sig

  val schedule: Ir.program -> schedule

end

module type SPILL_COSTS_ANALYSIS = sig

  val analyse: Ir.ControlFlowGraph.t -> Analysis_domain.NaturalLoops.table -> (Ir.reg, int) Hashtbl.t

end

module type INTERFERENCE_GRAPH_ANALYSIS = sig

  val analyse: Ir.ControlFlowGraph.t ->  Analysis_domain.LiveVariables.table -> Ir.RegGraph.t

end

module type SPILLING = sig

  val spill: Ir.procedure -> Ir.reg list -> unit

end

module type COMPILER_TOOLBOX = sig

  module LiveVariablesAnalysis : LIVE_VARIABLES_ANALYSIS

  module DominatorsAnalysis : DOMINATORS_ANALYSIS

  module NaturalLoopsAnalysis : NATURAL_LOOPS_ANALYSIS

  module SpillCostsAnalysis : SPILL_COSTS_ANALYSIS

  module Scheduler: SCHEDULER

  module RegistersDescription : Ir_arch.REGISTERS_DESCRIPTION

  module ConstantFoldingAnalysis : CONSTANT_FOLDING_ANALYSIS

  module InterferenceGraphAnalysis : INTERFERENCE_GRAPH_ANALYSIS

  module Spilling : SPILLING

  module ReachabilityAnalysis : REACHABILITY_ANALYSIS

  module RegisterCoalescing: REGISTER_COALESCING
end


module type COMPILER_STEPS = sig

  module Toolbox: COMPILER_TOOLBOX

  module LexerAndParser: LEXER_AND_PARSER

  module Typechecker: TYPECHECKER

  module Translator: TRANSLATOR

  module JumpThreading: JUMP_THREADING

  module ConstantFolding: CONSTANT_FOLDING

  module HiLower: HI_LOWER

  module CallConv: CALLCONV

  module MipsLower: MIPS_LOWER

  module RegisterAllocator: REGISTER_ALLOCATOR

  module Codegen: CODEGEN

  module DeadCodeElimination: DEAD_CODE_ELIMINATION
end
