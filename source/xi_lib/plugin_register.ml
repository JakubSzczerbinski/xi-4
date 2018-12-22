open Plugin

let register = ref []

let current_file = ref ""

let register_plugin plugin =
  register := (!current_file, plugin) :: !register

module RegisterPlugin(P:PLUGIN) = struct

  let handle = (module P : PLUGIN)

  let () = register_plugin handle

end