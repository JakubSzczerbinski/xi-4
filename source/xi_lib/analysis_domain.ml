
module MapWithTop(M:Map.S) = struct

  type 'v t =
    | Top
    | Map of 'v M.t

  let equal a b = match a,b with
    | Top, Top ->
      true
    | Top, _
    | _, Top ->
      false
    | Map a, Map b ->
      M.equal (=) a b

  let less_or_equal a b = match a,b with
    | _, Top ->
      true

    | Top, _ ->
      false

    | Map a, Map b ->
      let check (k, v) = 
        match M.find_opt k b with
        | Some v' -> v = v'
        | None -> false
      in
      let a_items = M.to_seq a in
      let checks = Seq.map check a_items in
      Seq.fold_left (&&) true checks

  let greater_or_equal a b = less_or_equal b a

  let unhask dfl = function 
    | Top -> dfl
    | Map m -> m

end

module SetWithTop(M:Set.S) = struct

  type t =
    | Top
    | Set of M.t

  let equal a b = match a,b with
    | Top, Top ->
      true
    | Top, _
    | _, Top ->
      false
    | Set a, Set b ->
      M.equal a b

  let less_or_equal a b = match a,b with
    | _, Top ->
      true

    | Top, _ ->
      false

    | Set a, Set b ->
      M.subset a b

  let greater_or_equal a b = less_or_equal b a

  let unhask dfl = function 
    | Top -> dfl
    | Set m -> m

end


module LiveVariables = struct

  type domain = Ir.RegSet.t

  type table = domain Analysis.BlockKnowledge.table

  type block_knowledge = domain Analysis.BlockKnowledge.t

  let string_of_domain x = Ir_utils.string_of_reglist @@ List.of_seq @@ Ir.RegSet.to_seq x
end

module InterferenceGraph = struct

  type graph = Ir.RegGraph.t

end

module ConstantFolding = struct

  type domain = Ir.expr option Ir.RegMap.t

  type table = domain Analysis.BlockKnowledge.table

  type block_knowledge = domain Analysis.BlockKnowledge.t

  let string_of_el = function
    | None -> "T"
    | Some a -> Ir_utils.string_of_expr a

  let string_of_domain dom =
    let f (k,v) = Format.sprintf "%s=%s" (Ir_utils.string_of_reg k) (string_of_el v) in
    let seq = Ir.RegMap.to_seq dom in
    let seq = Seq.map f seq in
    String.concat " " @@ List.of_seq seq

end

module DominatorsAnalysis = struct

  module D = SetWithTop(Ir.LabelSet)

  type t = D.t

  type table = t Analysis.BlockKnowledge.table

  let unhask = D.unhask Ir.LabelSet.empty

end

module NaturalLoops = struct

  type table = (Ir.label, Ir.LabelSet.t) Hashtbl.t

end

module ReachabilityAnalysis = struct

  type table = Ir.LabelSet.t Analysis.BlockKnowledge.table

end
