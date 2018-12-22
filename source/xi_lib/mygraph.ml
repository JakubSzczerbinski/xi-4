
(* Just to keep compatibility with Ocamlgraph *)
module type SElem = sig

  type t

  val compare: t -> t -> int

  val hash: t -> int

  val equal: t -> t -> bool

end

module MakeBidirectional(V:SElem) = struct

  type t = 
    { g_successors: (V.t, V.t Hashset.t) Hashtbl.t
    ; g_predecessors: (V.t, V.t Hashset.t) Hashtbl.t
    ; g_vertices : V.t Hashset.t
    }  

  let create () =
    { g_successors = Hashtbl.create 101
    ; g_predecessors = Hashtbl.create 101
    ; g_vertices = Hashset.create ()
    }

  let nb_vertex g = 
    Hashset.length g.g_vertices

  let _assert_mem g v =
    assert (Hashset.mem g.g_vertices v)

  let add_vertex g v =
    if not @@ Hashset.mem g.g_vertices v  then begin
      Hashset.add g.g_vertices v;
      Hashtbl.replace g.g_successors v @@ Hashset.create ();
      Hashtbl.replace g.g_predecessors v @@ Hashset.create ()
    end

  let _succ g v =
    Hashtbl.find g.g_successors v

  let _pred g v =
    Hashtbl.find g.g_predecessors v

  let remove_vertex g v =
    _assert_mem g v;
    Hashset.remove g.g_vertices v;
    let remove_pred w =
      let pred = _pred g w in
      Hashset.remove pred v
    in
    let succ = _succ g v in
    Hashset.iter remove_pred succ

  let add_edge g v w =
    add_vertex g v;
    add_vertex g w;
    let v_succ = _succ g v in
    let w_pred = _pred g w in
    Hashset.add v_succ w;
    Hashset.add w_pred v

  let fold_vertex f g acc =
    Hashset.fold f g.g_vertices acc

  let succ g v =
    _assert_mem g v;
    List.of_seq @@ Hashset.to_seq @@ _succ g v

  let pred g v =
    _assert_mem g v;
    List.of_seq @@ Hashset.to_seq @@ _pred g v

  let remove_edge g v w =
    _assert_mem g v;
    _assert_mem g w;
    let v_succ = _succ g v in
    let w_pred = _pred g w in
    Hashset.remove v_succ w;
    Hashset.remove w_pred v

end

module MakeUndirected(V:SElem) = struct

  type t = 
    { g_neighbours: (V.t, V.t Hashset.t) Hashtbl.t
    }  

  let create () =
    { g_neighbours = Hashtbl.create 101
    }

  let nb_vertex g = 
    Hashtbl.length g.g_neighbours

  let _assert_mem g v =
    assert (Hashtbl.mem g.g_neighbours v)

  let add_vertex g v =
    if not @@ Hashtbl.mem g.g_neighbours v  then begin
      Hashtbl.replace g.g_neighbours v @@ Hashset.create ();
    end

  let _nb g v =
    Hashtbl.find g.g_neighbours v

  let remove_vertex g v =
    _assert_mem g v;
    let remove_pred w =
      let pred = _nb g w in
      Hashset.remove pred v
    in
    let succ = _nb g v in
    Hashset.iter remove_pred succ;
    Hashtbl.remove g.g_neighbours v

  let add_edge g v w =
    add_vertex g v;
    add_vertex g w;
    let v_nb = _nb g v in
    let w_nb = _nb g w  in
    Hashset.add v_nb w;
    Hashset.add w_nb v

  let fold_vertex f g acc =
    let h k _ = f k in 
    Hashtbl.fold h g.g_neighbours acc

  let succ g v =
    _assert_mem g v;
    List.of_seq @@ Hashset.to_seq @@ _nb g v

  let fold_edges f g acc =
    let h v nb acc =
      let f' w acc = f w v acc in
      Hashset.fold f' nb acc
    in
    Hashtbl.fold h g.g_neighbours acc

  let iter_edges f g =
    let h v nb =
      let f' w = f w v in
      Hashset.iter f' nb 
    in
    Hashtbl.iter h g.g_neighbours 

  let out_degree g v =
    _assert_mem g v;
    Hashset.length @@ _nb g v

end