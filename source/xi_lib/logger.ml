module FS = struct

  let removedir =
    let rec rm path item =
      let p = (Filename.concat path item) in
      if Sys.is_directory p then
        let items = Sys.readdir p in
        Array.iter (rm p) items;
        Unix.rmdir p;
      else
        Sys.remove p
    in 
    fun item ->
      if Sys.file_exists item then
        rm "" item


  let xilog_dir = ref "xilog"

  let init xilog =
    xilog_dir := xilog;
    removedir xilog;
    Unix.mkdir xilog 0o777
end


module State = struct

  let extra_debug = ref false

  let counter = ref 0 

  let phase_name = ref ""

  let proc_name = ref ""

  let log_file_name  = ref ""

  let log_file_handle : out_channel option ref = ref None

  let get_lof_file_handle () =
    match !log_file_handle with
    | Some handle ->
      handle
    | None ->
      assert (!log_file_name <> "");
      let handle = open_out !log_file_name in
      log_file_handle := Some handle;
      handle

  let close_log_file () =
    match !log_file_handle with
      | None ->
        ()
      | Some handle ->
        close_out handle;
        log_file_name := "";
        log_file_handle := None

  let make_entry_name = function
    | () when !phase_name <> "" && !proc_name <> "" ->
      Format.sprintf "%03u.%s.%s" !counter !phase_name !proc_name
    | () when !phase_name <> "" ->
      Format.sprintf "%03u.%s" !counter !phase_name
    | _ ->
      Format.sprintf "%03u.unknown-phase" !counter

  let allocate_file_name title = 
    let r = Format.sprintf "%s/%s.%s" !FS.xilog_dir (make_entry_name ()) title in
    incr counter;
    r

  let set_new_phase name =
    phase_name := name;
    proc_name := "";
    close_log_file ();
    log_file_name := allocate_file_name "log"


  let set_proc_phase procid =
    proc_name := Ir_utils.string_of_procid procid;
    close_log_file ();
    log_file_name := allocate_file_name "log"


  let close_phase_proc () =
    proc_name := "";
    close_log_file ();
    log_file_name := allocate_file_name "log"

  let set_extra_debug v =
    extra_debug := v
end


let extra_debug f =
  if !State.extra_debug then
    f ()

let set_extra_debug = State.set_extra_debug

let new_phase name =
  State.set_new_phase name

let new_phase_proc procid =
  State.set_proc_phase procid

let close_phase_proc () =
  State.close_phase_proc ()

let make_logf mname fmt =
  let cont s =
    let h = State.get_lof_file_handle () in
    let entry = Format.sprintf "%s: %s\n" mname s in
    output_string h entry;
    flush h
  in
  Format.ksprintf cont fmt

let dump_string title buffer =
  let name = State.allocate_file_name title in
  make_logf __MODULE__ "Dumping %s" (Filename.basename name);
  let h = open_out name in
  output_string h buffer;
  output_string h "\n";
  close_out h

let dump_ir_program title ir =
  let buffer = Ir_utils.string_of_program ir in
  dump_string title buffer

let dump_ir_proc title irproc =
  let buffer = Ir_utils.string_of_procedure irproc in
  dump_string title buffer

let dump_spill_costs spill_costs =
  let f (k,v) = Format.sprintf "%s -> %u" (Ir_utils.string_of_reg k) v in 
  let seq = Hashtbl.to_seq spill_costs in
  let seq = Seq.map f seq in
  let seq = List.of_seq seq in
  let buf = String.concat "\n" @@ List.sort compare seq in
  dump_string "spill_costs" buf

let dump_spill_costs_f spill_costs =
  let f (k,v) = Format.sprintf "%s -> %f" (Ir_utils.string_of_reg k) v in 
  let seq = Hashtbl.to_seq spill_costs in
  let seq = Seq.map f seq in
  let seq = List.of_seq seq in
  let buf = String.concat "\n" @@ List.sort compare seq in
  dump_string "spill_costs" buf


let log_ir_proc mname irproc =
  let buffer = Ir_utils.string_of_procedure irproc in
  make_logf mname "%s" buffer

let dump_interference_graph title x =
  let buffer = Analysis_visualizer.visualize_interference_graph x in
  dump_string (title ^ ".infg.xdot") buffer

let dump_live_variables title cfg table =
  let buffer = Analysis_visualizer.visualize_live_variables cfg table in
  dump_string (title ^ ".lva.xdot") buffer

let dump_constant_folding title cfg table =
  let buffer = Analysis_visualizer.visualize_constant_folding cfg table in
  dump_string (title ^ ".cfa.xdot") buffer

let init xilog =
  FS.init xilog
