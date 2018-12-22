let logf fmt = Logger.make_logf __MODULE__ fmt

let measure name f =
  let t_start = Unix.gettimeofday () in 
  let r = f () in
  let t_end = Unix.gettimeofday () in
  logf "%s: execution time %f" name (t_end -. t_start);
  r