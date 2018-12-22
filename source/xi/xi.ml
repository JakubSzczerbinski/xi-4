open Xi_lib


module CommandLine = struct
  open Cmdliner

  let compile xi_log extra_debug mod_uwr plugin reg_descr stop_after output source = 
    Logger.init xi_log;
    Logger.set_extra_debug extra_debug;
    Plugin_manager.load_plugin mod_uwr;
    let reg_descr = match List.assoc_opt reg_descr Ir_arch.descriptions with
      | Some reg_descr -> reg_descr
      | None -> failwith "Unknown registers description" 
    in 
    begin match plugin with
    | Some path ->
      Plugin_manager.load_plugin path
    | None ->
      ()
    end;
    let module Steps = (val Plugin_manager.resolve_compiler_steps reg_descr) in 
    let module Params = struct 
        let output = output
        let stop_point = match stop_after with
          | Some s -> s
          | None -> ""
     end in
    let module Pipeline = Pipeline.Make(Steps)(Params) in
    match Pipeline.compile source with
      | Ok () ->
        0
      | Error xs ->
        Format.eprintf "Failed: %s\n%!" xs;
        1

  let stop_after =
    let doc = "Stops compiler after given phase" in
    Arg.(value & opt (some string) None & info ["stop-after"] ~doc)

  let mod_uwr =
    let doc = "Base module" in
    Arg.(value & opt string "xisdk/mod_uwr.cma" & info ["mod-uwr"] ~doc)

  let reg_descr =
    let doc = "EXPERIMENTAL: Registers description (see Ir_arch.descriptions)" in
    Arg.(value & opt string "normal" & info ["registers-description"] ~doc)

  let plugin =
    let doc = "Plugin module" in
    Arg.(value & opt (some string) None & info ["plugin"] ~doc)

  let output =
    let doc = "Output file" in
    Arg.(value & opt string "main.s" & info ["o"; "output"] ~doc)

  let xi_log =
    let doc = "Log directory" in
    Arg.(value & opt string "xilog" & info ["xi-log"] ~doc)

  let runtime =
    let doc = "Runtime" in
    Arg.(value & opt file "xisdk/runtime.s" & info ["runtime"] ~doc)

  let extra_debug =
    let doc = "Enables extra debug" in
    Arg.(value & flag & info ["extra-debug"] ~doc)

  let source_file =
    let doc = "Xi Source File" in
    Arg.(required & pos 0 (some file) None & info [] ~doc)


  let cmd =
    let doc = "Compile Xi Program" in
    let version = "pracownia4.1-0-ge52fd94" in
    Term.(const compile $ xi_log $ extra_debug $ mod_uwr $ plugin $ reg_descr $ stop_after $ output $ source_file),
    Term.info "xi" ~doc ~version


  let () = Term.(exit_status @@ eval cmd)

end
