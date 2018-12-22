module Knowledge = struct

  type 'a t =
    { pre: 'a
    ; post: 'a
    }

  let pre t = t.pre

  let post t = t.post

  let alter ?pre ?post t =
    let t = match pre with
      | Some pre -> {t with pre = pre}
      | None -> t
    in
    let t = match post with
      | Some post -> {t with post = post}
      | None -> t
    in
    t

  let make pre post : 'a t = {pre; post}

  type 'a table = (Ir.label, 'a t) Hashtbl.t

end

module BlockKnowledge = struct

  type 'a t =
    | Simple of 'a Knowledge.t
    | Complex of
      { block: 'a Knowledge.t
      ; body: ('a Knowledge.t * Ir.instr) list
      ; terminator: 'a Knowledge.t * Ir.terminator
      }

  let block = function
    | Simple t -> t
    | Complex {block; _} -> block

  let pre t = Knowledge.pre @@ block t
  let post t = Knowledge.post @@ block t

  let terminator = function
    | Simple _ -> failwith "BlockKnowledge.terminator"
    | Complex t->  t.terminator

  let body =  function
    | Simple _ -> failwith "BlockKnowledge.body"
    | Complex t -> t.body

  let terminator_instr t = snd @@ terminator t

  let terminator_kw t = fst @@ terminator t

  let make_complex ~block ~body ~terminator = 
    Complex { block; body; terminator }

  let make_simple t = Simple t

  type 'a table = (Ir.label, 'a t) Hashtbl.t

  let alter_prepost ?pre ?post = function
    | Simple t ->
      Simple (Knowledge.alter ?pre ?post t)

    | Complex {block; body; terminator} ->
      let block = Knowledge.alter ?pre ?post block in
      Complex {block; body; terminator}

  let is_complex = function
    | Complex _ -> true
    | Simple _ -> false

end
