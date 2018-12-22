type reg
    (* rejestr tymczasowy *)
  = REG_Tmp of int
    (* rejestr sprzętowy *)
  | REG_Hard of int
    (* rejestr sprzętowy specjalnego przeznaczenia *)
  | REG_Spec of int


let is_spec_reg = function
  | REG_Spec _ -> true
  | _ -> false

let is_tmp_reg = function
  | REG_Tmp _ -> true
  | _ -> false

module RegSet = Set.Make(struct 
  type t = reg

  let compare = compare
  end)

module RegMap = Map.Make(struct 
  type t = reg

  let compare = compare
  end)


module RegGraph = Graph.Imperative.Graph.Concrete(struct 
(* module RegGraph = Mygraph.MakeUndirected(struct *)
  type t = reg

  let hash = Hashtbl.hash

  let equal a b = compare a b = 0

  let compare a b = compare a b
  end)

type expr
  = E_Reg of reg
  | E_Int of Int32.t


let reglist_of_expr = function
  | E_Reg r -> [r]
  | E_Int _ -> []

type label
  = Label of int

module LabelSet = Set.Make(struct 
  type t = label
  let compare = compare
  end)

type procid
  = Procid of string


type cond
  = COND_Eq
  | COND_Ne
  | COND_Lt
  | COND_Gt
  | COND_Le
  | COND_Ge


type instr
    (* dodaj *)
  = I_Add of reg * expr * expr
    (* odejmij *)
  | I_Sub of reg * expr * expr
    (* podziel *)
  | I_Div of reg * expr * expr
    (* reszta z dzielenia *)
  | I_Rem of reg * expr * expr
    (* pomnóż *)
  | I_Mul of reg * expr * expr
    (* bitowy and *)
  | I_And of reg * expr * expr
    (* bitowy or *)
  | I_Or of reg * expr * expr
    (* bitowy xor *)
  | I_Xor of reg * expr * expr
    (* LoadArray(r, xs, i) oznacza załaduj i-ty element tablicy xs do rejestru r *)
  | I_LoadArray of reg * expr * expr
    (* StoreArray(xs, i, e) oznacza zapisz do i-tego elementu tablicy xs atom e *)
  | I_StoreArray of expr * expr * expr
    (* LoadMem(r, xs, i) oznacza załaduj komórkę pamięci o adresie (xs+i) do rejestru r*)
  | I_LoadMem of reg * expr * expr
    (* StoreMem(xs, i, e) oznacza zapisz do komórki pamięci o adresie (xs+i) atom e *)
  | I_StoreMem of expr * expr * expr
    (* wysokopoziomowa instrukcja: konkatenacja tablic *)
  | I_Concat of reg * expr * expr
    (* zaneguj liczbę *)
  | I_Neg of reg * expr
    (* bitowy not *)
  | I_Not of reg * expr
    (* zapisz atom do rejestru *)
  | I_Move of reg * expr
    (* wysokopoziomowa instrukcja: zapisuje do rejestru długość tablicy *)
  | I_Length of reg * expr
    (* wysokopoziomowa instrukcja: zaalokuj tablicę o określonym rozmiarze *)
  | I_NewArray of reg * expr
    (* I_Call(rs, p, xs, ms) oznacza wywołaj p z argumentami xs, wyniki
     * funkcji znajdą się w rejestrach rs, dodatkowo zostaną zmodyfikowane rejestry ms *)
  | I_Call of reg list * procid * expr list * reg list
    (* I_Set(r, cond, a, b) zapisz do rejestru r wartość boolowską warunku cond(a,b) *)
  | I_Set of reg * cond * expr * expr
    (* załaduj do rejestru zmienną lokalną *)
  | I_LoadVar of reg * int
    (* zapisz atom do zmiennej lokalnej *)
  | I_StoreVar of int * expr
    (* załaduj do rejestru komórkę ze stosu *)
  | I_LoadStack of reg * int
    (* zapisz do komórki na stosie atom *)
  | I_StoreStack of int * expr
    (* przydziel stos *)
  | I_StackAlloc of Int32.t
    (* zwolnij stos *)
  | I_StackFree of Int32.t
    (* meta-instrukcja, podane rejestry będą uznawane za użyte *)
  | I_Use of reg list
    (* meta-instrukcja, podane rejestry będą uznane za zmodyfikowane *)
  | I_Def of reg list


type terminator =
    (* return *)
  | T_Return of expr list
    (* T_Branch(cond, a, b, then_bb, else_bb) oznacza skok warunkowy
     * if cond(a,b) then goto then_bb else goto else_bb *)
  | T_Branch of cond * expr * expr * label * label
    (* skok bezwarunkowy *)
  | T_Jump of label 

let labels_of_terminator = function
  | T_Branch (_, _, _, lt, lf) -> [lt; lf]
  | T_Jump l -> [l]
  | _ -> []

type block = instr list

module LabelGraph = Graph.Imperative.Digraph.ConcreteBidirectional(struct 
  type t = label
  let compare = compare
  let hash = Hashtbl.hash
  let equal a b = a = b
  end)

(* Reprezentacja ciała funkcji *)
module ControlFlowGraph = struct

  type graph = LabelGraph.t 

  type t = Cfg of
  { graph: graph
  ; blockmap: (label, block) Hashtbl.t
  ; terminatormap: (label, terminator) Hashtbl.t
  ; entry: label
  ; exit: label
  }

  let graph (Cfg {graph; _}) = graph

  let _allocate_block graph =
    let i = LabelGraph.nb_vertex graph in
    let l = Label i in
    LabelGraph.add_vertex graph l;
    l

  let remove (Cfg {graph; terminatormap; blockmap; _}) v =
    LabelGraph.remove_vertex graph v;
    Hashtbl.remove terminatormap v;
    Hashtbl.remove blockmap v

  let allocate_block (Cfg {graph; blockmap; terminatormap;  _}) =
    let i = LabelGraph.nb_vertex graph in
    let l = Label i in
    LabelGraph.add_vertex graph l;
    Hashtbl.replace blockmap l [];
    Hashtbl.replace terminatormap l (T_Return []);
    l

  let create () =
    let graph = LabelGraph.create () in
    let blockmap = Hashtbl.create 513 in
    let terminatormap = Hashtbl.create 513 in
    let entry = _allocate_block graph in
    let exit = _allocate_block graph in
    let _ = LabelGraph.add_vertex graph entry in 
    let _ = LabelGraph.add_vertex graph exit in 
    Cfg {graph; blockmap; terminatormap; entry; exit}

  let successors (Cfg {graph; _}) v = 
    LabelGraph.succ graph v

  let predecessors (Cfg {graph; _}) v = 
    LabelGraph.pred graph v

  let entry_label (Cfg {entry; _}) = entry

  let exit_label (Cfg {exit; _}) = exit

  let blockmap (Cfg {blockmap;_}) = blockmap

  let blocklist cfg =
    let blockmap = blockmap cfg in
    let f xs (k,v) = (k,v) :: xs in
    let blocks = Seq.fold_left f [] (Hashtbl.to_seq blockmap) in 
    let blocks = List.sort compare blocks in
    blocks

  let terminator (Cfg {terminatormap; entry; exit; _}) v =
    assert (entry <> v);
    assert (exit <> v);
    Hashtbl.find terminatormap v

  let blocklist2 cfg =
    let blockmap = blockmap cfg in
    let f xs (k,v) = (k,v,terminator cfg k) :: xs in
    let blocks = Seq.fold_left f [] (Hashtbl.to_seq blockmap) in 
    let blocks = List.sort compare blocks in
    blocks

  let blocklabels cfg =
    let blockmap = blockmap cfg in
    let f xs k = k :: xs in
    let blocks = Seq.fold_left f [] (Hashtbl.to_seq_keys blockmap) in 
    let blocks = List.sort compare blocks in
    blocks


  let block (Cfg {blockmap; entry; exit; _}) v =
    assert (entry <> v);
    assert (exit <> v);
    Hashtbl.find blockmap v

  let block_safe (Cfg {blockmap; entry; exit; _}) v =
    assert (entry <> v);
    assert (exit <> v);
    Hashtbl.find_opt blockmap v


  let terminator_safe (Cfg {terminatormap; entry; exit; _}) v =
    assert (entry <> v);
    assert (exit <> v);
    Hashtbl.find_opt terminatormap v

  let set_block (Cfg {blockmap; entry; exit; _}) v body =
    assert (entry <> v);
    assert (exit <> v);
    Hashtbl.replace blockmap v body

  let set_block2 (Cfg {blockmap; terminatormap; entry; exit; _}) v body terminator =
    assert (entry <> v);
    assert (exit <> v);
    Hashtbl.replace blockmap v body;
    Hashtbl.replace terminatormap v terminator

  let set_terminator (Cfg {terminatormap; entry; exit; _}) v body =
    assert (entry <> v);
    assert (exit <> v);
    Hashtbl.replace terminatormap v body

  let connect (Cfg {graph; exit; entry; _}) a b =
    assert (entry <> b);
    assert (exit <> a);
    LabelGraph.add_edge graph a b

  let labels (Cfg {graph; _}) = 
    LabelGraph.fold_vertex (fun x xs -> x::xs) graph []

end

(* Reprezentacja całej procedury *)
type procedure = Procedure of
    (* identyfikator *)
  { procid: procid
    (* graf sterowania *)
  ; cfg: ControlFlowGraph.t
    (* rozmiar rekordu aktywacji *)
  ; mutable frame_size: int
    (* ilość parametrów formalnych *)
  ; formal_parameters: int
    (* funkcja do przydzielania świeżych rejestrów wewnątrz danej proceduy *)
  ; allocate_register: unit -> reg
  }

let cfg_of_procedure (Procedure {cfg; _}) = cfg

let formal_parameters_of_procedure (Procedure {formal_parameters; _}) = formal_parameters

let allocate_register_of_procedure (Procedure {allocate_register; _}) = allocate_register

let allocate_frame_slot (Procedure procid) =
  let slot = procid.frame_size in
  procid.frame_size <- procid.frame_size + 1;
  slot


let procid_of_procedure (Procedure {procid; _}) = procid

let frame_size_of_procedure (Procedure {frame_size; _}) = frame_size


(* Reprezentacja programu *)
type program = Program of
    (* lista procedur *)
  { procedures: procedure list
    (* lista wszystkich symboli *)
  ; symbols: procid list
  }

let procedures_of_program (Program{procedures; _}) = procedures

let symbols_of_program (Program{symbols; _}) = symbols
