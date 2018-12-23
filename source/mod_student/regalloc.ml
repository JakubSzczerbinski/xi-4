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
    
    let remove infg r r_to_ns =
      let ns = RegGraph.succ infg r in
      Hashtbl.add r_to_ns r ns;
      RegGraph.remove_vertex infg r

    let restore infg r r_to_ns =
      let ns = Hashtbl.find r_to_ns r 
      in 
      RegGraph.add_vertex infg r;
      List.iter (fun n -> RegGraph.add_edge infg r n) ns

    let get_tmp_reg_with_lowest_degree infg =
      RegGraph.fold_vertex (fun reg maybe_reg -> 
        match (reg, maybe_reg) with
        | (REG_Hard _), _ -> maybe_reg
        | (REG_Spec _), _ -> maybe_reg
        | r1, None -> Some r1
        | r1, (Some r2) -> 
            if RegGraph.in_degree infg r1 > RegGraph.in_degree infg r2 
            then Some r1 
            else Some r2
        )
      infg None

    let selectSpillCandidate infg spill_costs reg =
      let spillRate r =
        (Float.of_int (RegGraph.in_degree infg r)) /. (Float.of_int (Hashtbl.find spill_costs r))
      in
      RegGraph.fold_vertex (fun r1 r2 ->
        if (spillRate r1) > (spillRate r2) then
          r1
        else
          r2
      ) infg reg

    let is_some = function
      | Some _ -> true
      | None -> false

    let simplify infg spill_costs =
      let n = List.length available_registers in
      let reg = ref (get_tmp_reg_with_lowest_degree infg) in
      let stack = Stack.create () in
      let restoration_table = Hashtbl.create 513 in
      while is_some !reg do
        let r = match !reg with
          | Some r -> r
          | None -> failwith "What ???" 
        in
        let reg_degree = RegGraph.in_degree infg r in
        (if reg_degree >= n then
          let r = selectSpillCandidate infg spill_costs r in
          remove infg r restoration_table;
          Stack.push r stack
        else
          remove infg r restoration_table;
          Stack.push r stack);
        reg := get_tmp_reg_with_lowest_degree infg
      done;
      stack, restoration_table

    (* ------------------------------------------------------------------------
     *  Faza Select
     *)

    let selectColor reg infg =
      let notAvailbleColors = 
        (List.map (fun r -> Hashtbl.find register2color_assignment r)
        (List.filter (fun r -> Hashtbl.mem register2color_assignment r) (RegGraph.succ infg reg))) 
      in
      let colors = List.map (fun r -> Hashtbl.find register2color_assignment r) available_registers in
      let res = List.filter (fun c -> not (List.mem c notAvailbleColors)) colors in
      match res with
      | [] -> None
      | x::_ -> Hashtbl.add register2color_assignment reg x; Some x

    let rec select infg stack restoration_table =
      if Stack.is_empty stack then
        []
      else
        let r = Stack.pop stack in
        restore infg r restoration_table;
        match selectColor r infg with
        | None -> r::(select infg stack restoration_table)
        | _ -> select infg stack restoration_table

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
      let stack, restoration_table = simplify infg spill_costs in
      let actual_spills = select infg stack restoration_table in
      (), spill (List.rev actual_spills)
      (* unit na potrzeby interfejsu pomocniczej funkcji loop *)

    (* ------------------------------------------------------------------------
     *  Budowanie mapowania rejestrów
     *)

    let build_register_assignment () =
      let register_assignment : (reg, reg) Hashtbl.t = Hashtbl.create 513 in
      let seq = Hashtbl.to_seq register2color_assignment in
      Seq.iter (fun (reg, color) -> 
        Hashtbl.add 
          register_assignment 
          reg 
          (Hashtbl.find color2register_assignment color)
      ) seq;
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
