open Iface


module type MAKE_NATURAL_LOOPS_ANALYSIS = functor () -> NATURAL_LOOPS_ANALYSIS

module type MAKE_SPILL_COSTS_ANALYSIS = functor () -> SPILL_COSTS_ANALYSIS

module type MAKE_LIVE_VARIABLES_ANALYSIS = functor () -> LIVE_VARIABLES_ANALYSIS

module type MAKE_DOMINANCE_ANALYSIS = functor () -> DOMINATORS_ANALYSIS

module type MAKE_REACHABILITY_ANALYSIS = functor () -> REACHABILITY_ANALYSIS

module type MAKE_CONSTANT_FOLDING_ANALYSIS = functor () -> CONSTANT_FOLDING_ANALYSIS

module type MAKE_SCHEDULER = functor () -> SCHEDULER

module type MAKE_INTERFERENCE_GRAPH_ANALYSIS = functor () -> INTERFERENCE_GRAPH_ANALYSIS

module type MAKE_REGISTER_ALLOCATOR = functor (T:COMPILER_TOOLBOX) -> REGISTER_ALLOCATOR

module type MAKE_CALLCONV = functor (T:COMPILER_TOOLBOX) -> CALLCONV

module type MAKE_CONSTANT_FOLDING = functor (T:COMPILER_TOOLBOX) -> CONSTANT_FOLDING

module type MAKE_DEAD_CODE_ELIMINATION = functor (T:COMPILER_TOOLBOX) -> DEAD_CODE_ELIMINATION

module type MAKE_TYPECHECKER = functor () -> TYPECHECKER

module type MAKE_TRANSLATOR = functor () -> TRANSLATOR

module type MAKE_JUMP_THREADING = functor () -> JUMP_THREADING

module type MAKE_CODEGEN = functor (T:COMPILER_TOOLBOX) -> CODEGEN

module type MAKE_HI_LOWER = functor (T:COMPILER_TOOLBOX) -> HI_LOWER

module type MAKE_MIPS_LOWER = functor (T:COMPILER_TOOLBOX) -> MIPS_LOWER

module type MAKE_SPILLING = functor () -> SPILLING

module type MAKE_REGISTER_COALESCING = functor () -> REGISTER_COALESCING


module type PLUGIN = sig

  val version: string

  val make_live_variables_analysis : (module MAKE_LIVE_VARIABLES_ANALYSIS) option

  val make_dominators_analysis : (module MAKE_DOMINANCE_ANALYSIS) option

  val make_natural_loops_analysis : (module MAKE_NATURAL_LOOPS_ANALYSIS) option

  val make_spill_costs_analysis : (module MAKE_SPILL_COSTS_ANALYSIS) option

  val make_scheduler : (module MAKE_SCHEDULER) option

  val lexer_and_parser : (module LEXER_AND_PARSER) option

  val make_typechecker : (module MAKE_TYPECHECKER) option

  val make_translator : (module MAKE_TRANSLATOR) option

  val make_jump_threading : (module MAKE_JUMP_THREADING) option

  val make_constant_folding : (module MAKE_CONSTANT_FOLDING) option

  val make_hilower : (module MAKE_HI_LOWER) option

  val make_callconv : (module MAKE_CALLCONV) option

  val make_mipslower : (module MAKE_MIPS_LOWER) option

  val make_constant_folding_analysis : (module MAKE_CONSTANT_FOLDING_ANALYSIS) option

  val make_register_allocator : (module MAKE_REGISTER_ALLOCATOR) option

  val make_codegen : (module MAKE_CODEGEN) option

  val make_dead_code_elimination : (module MAKE_DEAD_CODE_ELIMINATION) option

  val make_interference_graph_analysis : (module MAKE_INTERFERENCE_GRAPH_ANALYSIS) option

  val make_spilling: (module MAKE_SPILLING) option

  val make_reachability_analysis: (module MAKE_REACHABILITY_ANALYSIS) option

  val make_register_coalescing: (module MAKE_REGISTER_COALESCING ) option
end