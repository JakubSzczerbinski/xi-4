open Xi_lib
open Xi_lib.Measure
open Ir

let logf fmt = Logger.make_logf __MODULE__ fmt

module Make(Toolbox:Iface.COMPILER_TOOLBOX) = struct

  module Implementation(M:sig
    val cfg: ControlFlowGraph.t
    val proc: procedure
    end) = struct

    open M

    module Coalescencing = Toolbox.RegisterCoalescing

    (* Dostępne rejestry *)
    let available_registers = Toolbox.RegistersDescription.available_registers

    (* Liczba dostępnych kolorów *)
    let number_of_available_registers = List.length available_registers

    (* ------------------------------------------------------------------------
     *  Hashtablice z kolorami 
     *)

    (* wstępnie pokolorowane wierzchołki *)
    let base_register2color_assignment : (reg, int) Hashtbl.t = Hashtbl.create 13

    (* kolory wierzchołków *)
    let register2color_assignment : (reg, int) Hashtbl.t = Hashtbl.create 13

    (* pomocnicza tablica -- odwzorowuje kolor na rejestr sprzętowy *)
    let color2register_assignment : (int, reg) Hashtbl.t = Hashtbl.create 13

    (* ------------------------------------------------------------------------
     *  Wstępne kolorowanie
     *)

    let initialize_colors () =
      let color i hard =
        Hashtbl.replace color2register_assignment i hard;
        Hashtbl.replace base_register2color_assignment hard i;
      in
      List.iteri color available_registers

    (* ------------------------------------------------------------------------
     *  Budowanie grafu interferencji 
     *)

    let build_infg () =
      logf "building interference graph";
      let lva = Toolbox.LiveVariablesAnalysis.analyse cfg in
      Logger.extra_debug begin fun () -> 
        Logger.dump_live_variables "before-inf-build" cfg lva;
      end;
      let infg = Toolbox.InterferenceGraphAnalysis.analyse cfg lva in
      Logger.extra_debug begin fun () ->
        Logger.dump_interference_graph "before-simplify" infg
      end;
      infg

    (* ------------------------------------------------------------------------
     *  Pomocnicze funkcje
     *)

    let loop name f = 
      let rec iter i = 
        logf "Starting iteration %s %u" name i;
        let r, should_restart = measure "iteration" f in
        if should_restart then
          iter (succ i)
        else
          r
      in
      iter 0

    (* ------------------------------------------------------------------------
     *  Spilling
     *)

    let compute_spill_costs infg =
      Logger.extra_debug begin fun () ->
        logf "Computing dominators"
      end;
      let dom = Toolbox.DominatorsAnalysis.analyse cfg in
      Logger.extra_debug begin fun () ->
        logf "Computing natural-loops"
      end;
      let nloops = Toolbox.NaturalLoopsAnalysis.analyse cfg dom in
      Logger.extra_debug begin fun () ->
        logf "Computing spill-costs"
      end;
      let spill_costs = Toolbox.SpillCostsAnalysis.analyse cfg nloops in
      Logger.extra_debug begin fun () ->
          Logger.dump_spill_costs spill_costs;
      end;
      spill_costs

    let spill actual_spills = 
      measure "spill" (fun () -> Toolbox.Spilling.spill proc actual_spills);
      actual_spills <> []

    (* ------------------------------------------------------------------------
     * Faza simplify
     *)


    let simplify =
      failwith "simplify not yet implemented"

    (* ------------------------------------------------------------------------
     *  Faza Select
     *)

    let select = 
      failwith "select not yet implemented"

    (* ------------------------------------------------------------------------
     *  Pętla build-coalesce
     *)

    let build_coalescence () =
      let infg = measure "build" (fun () -> build_infg ()) in
      let changed = measure "coalescence" (fun () ->  Coalescencing.coalesce proc infg available_registers) in
      infg, changed

    let build_coalescence_loop () = 
      loop "build-coalescence" build_coalescence

    (* ------------------------------------------------------------------------
     *  Pętla build-coalesce
     *)

    let single_pass () =
      let init () = begin
          (* resetujemy robocze tablice *)
          Hashtbl.reset register2color_assignment;
          Hashtbl.replace_seq register2color_assignment @@ Hashtbl.to_seq base_register2color_assignment;
      end in
      Logger.extra_debug begin fun () ->
        Logger.dump_ir_proc "begin-loop" proc
      end;
      let init = measure "init" init in
      let infg = measure "build-coalescence " build_coalescence_loop in
      let spill_costs = measure "spillcosts" (fun () -> compute_spill_costs infg) in
      (* uruchom fazę simplify/select/spill *)

      (* unit na potrzeby interfejsu pomocniczej funkcji loop *)
      (), true

    (* ------------------------------------------------------------------------
     *  Budowanie mapowania rejestrów
     *)

    let build_register_assignment () =
      let register_assignment : (reg, reg) Hashtbl.t = Hashtbl.create 513 in 
      failwith "register assingnment not yet implemented";
      (* Przejdz tablice register2color_assignment i uzupełnij prawidłowo
       * tablicę register_assignment *)
      register_assignment

    (* ------------------------------------------------------------------------
     *  Main
     *)

    let regalloc () =
      logf "Starting register-allocation";
      initialize_colors ();
      loop "main-loop" single_pass;
      build_register_assignment ()

  end

  let regalloc proc = 
    let module Instance = Implementation(struct
      let cfg = cfg_of_procedure proc
      let proc = proc
      let available_registers = Toolbox.RegistersDescription.available_registers
      end)
    in
    Instance.regalloc ()

end
