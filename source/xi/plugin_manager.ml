open Xi_lib
open Plugin_register

type plugin = string * (module Plugin.PLUGIN)

module Getters = struct

  let make_live_variables_analysis (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_live_variables_analysis with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_dominators_analysis (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_dominators_analysis with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_reachability_analysis (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_reachability_analysis with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_scheduler (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_scheduler with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_natural_loops_analysis (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_natural_loops_analysis with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_spill_costs_analysis (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_spill_costs_analysis with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let lexer_and_parser (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.lexer_and_parser with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_typechecker (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_typechecker with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_translator (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_translator with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_jump_threading (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_jump_threading with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_constant_folding (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_constant_folding with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_hilower (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_hilower with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_callconv (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_callconv with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_mipslower (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_mipslower with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_register_allocator (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_register_allocator with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_register_coalescing (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_register_coalescing with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None


  let make_dead_code_elimination (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_dead_code_elimination with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_codegen (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_codegen with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_constant_folding_analysis (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_constant_folding_analysis with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_interference_graph_analysis (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_interference_graph_analysis with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None

  let make_spilling (name, plugin) =
    let module Plugin = (val plugin : Plugin.PLUGIN) in
    match Plugin.make_spilling with
    | Some x -> Some (name, Plugin.version, x)
    | None -> None
end

module Resolver = struct

  let rec find_module name getter = function
    | [] ->
      failwith @@ Format.sprintf "Cannot find %s" name
    | x::xs ->
      match getter x with
      | Some (modname, version, impl) ->
        Format.eprintf "module %s=%s:%s\n%!" name modname version;
        impl
      | None -> 
        find_module name getter xs

  let make_live_variables_analysis = find_module "MakeLiveVariablesAnalysis" Getters.make_live_variables_analysis

  let make_dominators_analysis = find_module "MakeDominanceAnalysis" Getters.make_dominators_analysis

  let make_reachability_analysis = find_module "MakeReachabilityAnalysis" Getters.make_reachability_analysis

  let make_scheduler = find_module "MakeScheduler" Getters.make_scheduler

  let make_natural_loops_analysis = find_module "MakeNaturalLoopsAnalysis" Getters.make_natural_loops_analysis

  let make_spill_costs_analysis = find_module "MakeSpillCostsAnalysis" Getters.make_spill_costs_analysis

  let lexer_and_parser = find_module "LexerAndParser" Getters.lexer_and_parser

  let make_typechecker = find_module "MakeTypechecker" Getters.make_typechecker

  let make_translator = find_module "MakeTranslator" Getters.make_translator

  let make_jump_threading = find_module "MakeJumpThreading" Getters.make_jump_threading

  let make_constant_folding = find_module "MakeConstantFolding" Getters.make_constant_folding

  let make_hilower = find_module "MakeHiLower" Getters.make_hilower

  let make_callconv = find_module "MakeCallConv" Getters.make_callconv

  let make_mipslower = find_module "MakeMipsLower" Getters.make_mipslower

  let make_register_allocator = find_module "MakeRegisterAllocator" Getters.make_register_allocator

  let make_register_coalescing = find_module "MakeRegisterCoalescing" Getters.make_register_coalescing

  let make_dead_code_elimination = find_module "MakeDeadCodeElimination" Getters.make_dead_code_elimination

  let make_codegen = find_module "MakeCodegen" Getters.make_codegen

  let make_constant_folding_analysis = find_module "MakeConstantFoldingAnalysis" Getters.make_constant_folding_analysis

  let make_interference_graph_analysis = find_module "MakeInterferenceGraphAnalysis" Getters.make_interference_graph_analysis

  let make_spilling = find_module "MakeSpilling" Getters.make_spilling

end

let resolve_compiler_toolbox regdescr =
  let module MakeLiveVariablesAnalysis = (val Resolver.make_live_variables_analysis !register) in
  let module MakeDominatorsAnalysis = (val Resolver.make_dominators_analysis !register) in
  let module MakeNaturalLoopsAnalysis = (val Resolver.make_natural_loops_analysis !register) in
  let module MakeSpillCostsAnalysis = (val Resolver.make_spill_costs_analysis !register) in
  let module MakeScheduler = (val Resolver.make_scheduler !register) in
  let module MakeConstantFoldingAnalysis = (val Resolver.make_constant_folding_analysis !register) in
  let module MakeInterferenceGraphAnalysis = (val Resolver.make_interference_graph_analysis !register) in
  let module MakeSpilling = (val Resolver.make_spilling !register) in
  let module MakeReachabilityAnalysis = (val Resolver.make_reachability_analysis !register) in
  let module MakeRegisterCoalescing = (val Resolver.make_register_coalescing !register) in
  let module M = struct
    module LiveVariablesAnalysis = MakeLiveVariablesAnalysis()
    module DominatorsAnalysis = MakeDominatorsAnalysis()
    module Scheduler = MakeScheduler()
    module NaturalLoopsAnalysis = MakeNaturalLoopsAnalysis()
    module SpillCostsAnalysis = MakeSpillCostsAnalysis()
    module RegistersDescription = (val regdescr : Ir_arch.REGISTERS_DESCRIPTION)
    module ConstantFoldingAnalysis = MakeConstantFoldingAnalysis()
    module InterferenceGraphAnalysis = MakeInterferenceGraphAnalysis()
    module Spilling = MakeSpilling()
    module ReachabilityAnalysis = MakeReachabilityAnalysis()
    module RegisterCoalescing = MakeRegisterCoalescing()
  end in
  (module M : Iface.COMPILER_TOOLBOX)

let resolve_compiler_steps regdescr =
  let module CompilerToolbox = (val resolve_compiler_toolbox regdescr : Iface.COMPILER_TOOLBOX) in 
  let module LexerAndParser = (val Resolver.lexer_and_parser !register) in
  let module MakeTypechecker = (val Resolver.make_typechecker !register) in 
  let module MakeTranslator = (val Resolver.make_translator !register) in
  let module MakeJumpThreading = (val Resolver.make_jump_threading !register) in
  let module MakeConstantFolding = (val Resolver.make_constant_folding !register) in
  let module MakeHiLower = (val Resolver.make_hilower !register) in
  let module MakeCallConv = (val Resolver.make_callconv !register) in
  let module MakeMipsLower = (val Resolver.make_mipslower !register) in
  let module MakeRegisterAllocator = (val Resolver.make_register_allocator !register) in
  let module MakeDeadCodeElimination = (val Resolver.make_dead_code_elimination !register) in
  let module MakeCodegen = (val Resolver.make_codegen !register) in

  let module Steps = struct
    module Toolbox = CompilerToolbox
    module LexerAndParser = LexerAndParser
    module Typechecker = MakeTypechecker()
    module Translator = MakeTranslator()
    module JumpThreading = MakeJumpThreading()
    module HiLower = MakeHiLower(CompilerToolbox)
    module CallConv = MakeCallConv(CompilerToolbox)
    module MipsLower = MakeMipsLower(CompilerToolbox)
    module RegisterAllocator = MakeRegisterAllocator(CompilerToolbox)
    module ConstantFolding = MakeConstantFolding(CompilerToolbox)
    module DeadCodeElimination = MakeDeadCodeElimination(CompilerToolbox)
    module Codegen = MakeCodegen(CompilerToolbox)
  end in 

  (module Steps : Iface.COMPILER_STEPS)

let load_plugin path = 
  try 
    Plugin_register.current_file := Filename.basename path;
    Dynlink.loadfile path;
    Plugin_register.current_file := "";
  with Dynlink.Error e ->
    failwith @@ Format.sprintf "Cannot load plugin '%s': %s" path (Dynlink.error_message e)