open Ir

let string_of_reg = function
  | REG_Tmp i -> Format.sprintf "%%tmp%u" i
  | REG_Hard i -> Format.sprintf "%%hard%u" i
  | REG_Spec i -> Format.sprintf "%%spec%u" i

let string_of_cond = function
  | COND_Eq -> "eq"
  | COND_Ne -> "ne"
  | COND_Lt -> "lt"
  | COND_Gt -> "gt"
  | COND_Le -> "le"
  | COND_Ge -> "ge"

let remap_register_reg sb r = 
  try
    Hashtbl.find sb r
  with Not_found ->
    r

let remap_register_expr sb = function
  | E_Reg r -> E_Reg (remap_register_reg sb r)
  | e -> e

let remap_register_instr sb = function
  | I_Add (r0, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_Add (r0, r1, r2)

  | I_Sub (r0, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_Sub (r0, r1, r2)

  | I_Div (r0, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_Div (r0, r1, r2)

  | I_Rem (r0, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_Rem (r0, r1, r2)

  | I_Mul(r0, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_Mul (r0, r1, r2)

  | I_And(r0, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_And(r0, r1, r2)

  | I_Or(r0, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_Or(r0, r1, r2)

  | I_Xor(r0, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_Xor(r0, r1, r2)

  | I_LoadArray(r0, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_LoadArray(r0, r1, r2)

  | I_StoreArray(r0, r1, r2) ->
    let r0 = remap_register_expr sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_StoreArray(r0, r1, r2)

  | I_LoadMem(r0, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_LoadMem(r0, r1, r2)

  | I_StoreMem(r0, r1, r2) ->
    let r0 = remap_register_expr sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_StoreMem(r0, r1, r2)

  | I_Concat(r0, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_Concat(r0, r1, r2)

  | I_Neg(r0, r1) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    I_Neg(r0, r1)

  | I_Not(r0, r1) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    I_Not(r0, r1)

  | I_Move(r0, r1) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    I_Move(r0, r1)

  | I_Length(r0, r1) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    I_Length(r0, r1)

  | I_NewArray(r0, r1) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    I_NewArray(r0, r1)

  | I_Set(r0, cond, r1, r2) ->
    let r0 = remap_register_reg sb r0 in
    let r1 = remap_register_expr sb r1 in
    let r2 = remap_register_expr sb r2 in
    I_Set(r0, cond, r1, r2)

  | I_LoadVar(r0, i) ->
    let r0 = remap_register_reg sb r0 in
    I_LoadVar(r0, i)

  | I_StoreVar(i, r0) ->
    let r0 = remap_register_expr sb r0 in
    I_StoreVar(i, r0)

  | I_LoadStack(r0, i) ->
    let r0 = remap_register_reg sb r0 in
    I_LoadStack(r0, i)

  | I_StoreStack(i, r0) ->
    let r0 = remap_register_expr sb r0 in
    I_StoreStack(i, r0)

  | I_StackAlloc i ->
    I_StackAlloc i

  | I_StackFree i ->
    I_StackFree i

  | I_Use rs ->
    I_Use (List.map (remap_register_reg sb) rs)

  | I_Def rs ->
    I_Def (List.map (remap_register_reg sb) rs)

  | I_Call (rs, procid, args, kills) ->
    let rs = List.map (remap_register_reg sb) rs in
    let args = List.map (remap_register_expr sb) args in
    let kills = List.map (remap_register_reg sb) kills in
    I_Call (rs, procid, args, kills)

let subst_expr rmap = function
  | (E_Reg r) as e ->
    begin match RegMap.find_opt r rmap with
    | None -> e
    | Some e -> e
    end
  | e -> e

let subst_expr_instr sb = function
  | I_Add (r0, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_Add (r0, r1, r2)

  | I_Sub (r0, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_Sub (r0, r1, r2)

  | I_Div (r0, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_Div (r0, r1, r2)

  | I_Rem (r0, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_Rem (r0, r1, r2)

  | I_Mul(r0, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_Mul (r0, r1, r2)

  | I_And(r0, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_And(r0, r1, r2)

  | I_Or(r0, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_Or(r0, r1, r2)

  | I_Xor(r0, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_Xor(r0, r1, r2)

  | I_LoadArray(r0, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_LoadArray(r0, r1, r2)

  | I_StoreArray(r0, r1, r2) ->
    let r0 = subst_expr sb r0 in
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_StoreArray(r0, r1, r2)

  | I_LoadMem(r0, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_LoadMem(r0, r1, r2)

  | I_StoreMem(r0, r1, r2) ->
    let r0 = subst_expr sb r0 in
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_StoreMem(r0, r1, r2)

  | I_Concat(r0, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_Concat(r0, r1, r2)

  | I_Neg(r0, r1) ->
    let r1 = subst_expr sb r1 in
    I_Neg(r0, r1)

  | I_Not(r0, r1) ->
    let r1 = subst_expr sb r1 in
    I_Not(r0, r1)

  | I_Move(r0, r1) ->
    let r1 = subst_expr sb r1 in
    I_Move(r0, r1)

  | I_Length(r0, r1) ->
    let r1 = subst_expr sb r1 in
    I_Length(r0, r1)

  | I_NewArray(r0, r1) ->
    let r1 = subst_expr sb r1 in
    I_NewArray(r0, r1)

  | I_Set(r0, cond, r1, r2) ->
    let r1 = subst_expr sb r1 in
    let r2 = subst_expr sb r2 in
    I_Set(r0, cond, r1, r2)

  | I_LoadVar(r0, i) ->
    I_LoadVar(r0, i)

  | I_StoreVar(i, r0) ->
    let r0 = subst_expr sb r0 in
    I_StoreVar(i, r0)

  | I_LoadStack(r0, i) ->
    I_LoadStack(r0, i)

  | I_StoreStack(i, r0) ->
    let r0 = subst_expr sb r0 in
    I_StoreStack(i, r0)

  | I_StackAlloc i ->
    I_StackAlloc i

  | I_StackFree i ->
    I_StackFree i

  | I_Use rs ->
    I_Use rs

  | I_Def rs ->
    I_Def rs

  | I_Call (rs, procid, args, kills) ->
    let args = List.map (subst_expr sb) args in
    I_Call (rs, procid, args, kills)

let remap_label_label sb l =
  try
    Hashtbl.find sb l
  with Not_found ->
    l

let remap_label_terminator sb = function
  | T_Jump l ->
    T_Jump (remap_label_label sb l)

  | T_Branch (cond, r0, r1, lt, lf) ->
    T_Branch (cond, r0, r1, remap_label_label sb lt, remap_label_label sb lf)

  | t ->
    t

let remap_register_terminator sb = function
  | T_Return xs ->
    let xs = List.map (remap_register_expr sb) xs in
    T_Return xs

  | T_Branch (cond, r0, r1, l1, l2) ->
    let r0 = remap_register_expr sb r0 in
    let r1 = remap_register_expr sb r1 in
    T_Branch (cond, r0, r1, l1, l2)

  | T_Jump l ->
    T_Jump l

let subst_expr_terminator sb = function
  | T_Return xs ->
    let xs = List.map (subst_expr sb) xs in
    T_Return xs

  | T_Branch (cond, r0, r1, l1, l2) ->
    let r0 = subst_expr sb r0 in
    let r1 = subst_expr sb r1 in
    T_Branch (cond, r0, r1, l1, l2)

  | T_Jump l ->
    T_Jump l

let defined_registers_instr = function
  | I_Add (r0, _, _)
  | I_Sub (r0, _, _)
  | I_Div (r0, _, _)
  | I_Mul (r0, _, _)
  | I_And (r0, _, _)
  | I_Or (r0, _, _)
  | I_Xor (r0, _, _)
  | I_LoadArray (r0, _, _)
  | I_LoadMem (r0, _, _)
  | I_Concat (r0, _, _)
  | I_Not (r0, _)
  | I_Move (r0, _)
  | I_Length (r0, _)
  | I_NewArray (r0, _)
  | I_Neg (r0, _) 
  | I_Set  (r0, _, _, _) 
  | I_Rem (r0, _, _) 
  | I_LoadStack (r0, _) 
  | I_LoadVar (r0, _) ->
    [r0]


  | I_Call (outs, _, _, kills) ->
    outs @ kills

  | I_Use _
  | I_StoreVar _ 
  | I_StoreStack _
  | I_StackAlloc _ 
  | I_StackFree _
  | I_StoreMem _ 
  | I_StoreArray _ ->
    []

  | I_Def rs ->
    rs

let defined_registers_terminator _ = []

let used_registers_instr = function
  | I_Add (_, r0, r1)
  | I_Sub (_, r0, r1)
  | I_Div (_, r0, r1)
  | I_Mul (_, r0, r1)
  | I_And (_, r0, r1)
  | I_Or (_, r0, r1)
  | I_Xor (_, r0, r1)
  | I_LoadArray (_, r0, r1)
  | I_LoadMem (_, r0, r1)
  | I_Concat (_, r0, r1)
  | I_Set  (_, _, r0, r1)
  | I_Rem (_, r0, r1) ->
    List.flatten @@ List.map reglist_of_expr [r0;r1]

  | I_Not (_, r0)
  | I_Move (_, r0)
  | I_Length (_, r0)
  | I_NewArray (_, r0)
  | I_StoreVar (_, r0) 
  | I_StoreStack (_, r0) 
  | I_Neg (_, r0)  ->
    reglist_of_expr r0

  | I_Call (_, _, args, _) ->
    List.flatten @@ List.map reglist_of_expr args

  | I_Def _ 
  | I_StackAlloc _
  | I_StackFree _
  | I_LoadStack _
  | I_LoadVar _ ->
    []

  | I_StoreArray (r0, r1, r2) 
  | I_StoreMem (r0, r1, r2) ->
    List.flatten @@ List.map reglist_of_expr [r0; r1; r2]

  | I_Use rs ->
    rs

let used_registers_terminator = function
  | T_Branch (_, r0, r1, _, _) ->
    List.flatten @@ List.map reglist_of_expr [r0;r1]


  | T_Return args ->
    List.flatten @@ List.map reglist_of_expr args

  | T_Jump _ ->
    []

let remap_registers_proc sb proc =
  let cfg = (cfg_of_procedure proc) in 
  let remap_block (l, body, terminator) =
    let body = List.map (remap_register_instr sb) body in
    let terminator = remap_register_terminator sb terminator in
    (l, body, terminator)
  in
  let update_blocks (l, body, terminator) =
    ControlFlowGraph.set_block2 cfg l body terminator
  in

  let blocks = ControlFlowGraph.blocklist2 cfg in
  let blocks = List.map remap_block  blocks in
  List.iter update_blocks blocks

let string_of_expr = function
  | E_Reg r -> string_of_reg r
  | E_Int i -> Int32.to_string i

let string_of_label = function
  | Label i -> Format.sprintf "L%u" i

let string_of_procid = function
  | Procid l -> Format.sprintf "%s" l

let string_of_reglist xs =
  Format.sprintf "[%s]" (String.concat ", " @@ List.map string_of_reg xs)

let string_of_labellist xs =
  Format.sprintf "[%s]" (String.concat ", " @@ List.map string_of_label xs)

let string_of_exprlist xs =
  Format.sprintf "[%s]" (String.concat ", " @@ List.map string_of_expr xs)

let string_of_expr_regmap k =
  let f (k, v) = Format.sprintf "%s=%s" (string_of_reg k) (string_of_expr v) in 
  String.concat "; " @@ List.of_seq @@ Seq.map f @@ RegMap.to_seq k
let string_of_instr = function
  | I_Add (r0, e0, e1) ->
    Format.sprintf "add %s, %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_Sub (r0, e0, e1) ->
    Format.sprintf "sub %s, %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_Div (r0, e0, e1) ->
    Format.sprintf "div %s, %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_Rem (r0, e0, e1) ->
    Format.sprintf "rem %s, %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_Mul (r0, e0, e1) ->
    Format.sprintf "mul %s, %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_And (r0, e0, e1) ->
    Format.sprintf "and %s, %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_Or (r0, e0, e1) ->
    Format.sprintf "or %s, %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_Xor (r0, e0, e1) ->
    Format.sprintf "xor %s, %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_LoadArray (r0, e0, e1) ->
    Format.sprintf "loadarray %s, %s, %s // %s = %s[%s]"
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_LoadMem (r0, e0, e1) ->
    Format.sprintf "loadmem %s, %s, %s // %s = mem[%s + %s]"
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_StoreArray (r0, e0, e1) ->
    Format.sprintf "storearray %s, %s, %s // %s[%s] = %s"
      (string_of_expr r0)
      (string_of_expr e0)
      (string_of_expr e1)
      (string_of_expr r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_StoreMem (r0, e0, e1) ->
    Format.sprintf "storemem %s, %s, %s // mem[%s + %s] = %s"
      (string_of_expr r0)
      (string_of_expr e0)
      (string_of_expr e1)
      (string_of_expr r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_Concat (r0, e0, e1) ->
    Format.sprintf "concat %s, %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
      (string_of_expr e1)
  | I_Neg (r0, e0) ->
    Format.sprintf "neg %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
  | I_Not (r0, e0) ->
    Format.sprintf "not %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
  | I_Length (r0, e0) ->
    Format.sprintf "length %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
  | I_Move (r0, e0) ->
    Format.sprintf "move %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
  | I_NewArray (r0, e0) ->
    Format.sprintf "newarray %s, %s"
      (string_of_reg r0)
      (string_of_expr e0)
  | I_Call (rs, p, xs, kill) ->
    Format.sprintf "call %s, %s, %s, kill %s"
      (string_of_reglist rs)
      (string_of_procid p)
      (string_of_exprlist xs)
      (string_of_reglist kill)
  | I_Set (rr, cond, r0, r1) ->
    Format.sprintf "set %s, %s, %s, %s"
      (string_of_reg rr)
      (string_of_cond cond)
      (string_of_expr r0)
      (string_of_expr r1)
  | I_StoreVar (i0, e0) ->
    Format.sprintf "storevar %s, %s"
      (string_of_int i0)
      (string_of_expr e0)
  | I_LoadVar (r0, i0) ->
    Format.sprintf "loadvar %s, %s"
      (string_of_reg r0)
      (string_of_int i0)
  | I_StoreStack (i0, e0) ->
    Format.sprintf "storestack %s, %s"
      (string_of_int i0)
      (string_of_expr e0)
  | I_LoadStack (r0, i0) ->
    Format.sprintf "loadstack %s, %s"
      (string_of_reg r0)
      (string_of_int i0)
  | I_StackAlloc (i0) ->
    Format.sprintf "stackalloc %s"
      (Int32.to_string i0)
  | I_StackFree (i0) ->
    Format.sprintf "stackfree %s"
      (Int32.to_string i0)
  | I_Use rs ->
    Format.sprintf "use %s" (string_of_reglist rs)
  | I_Def rs ->
    Format.sprintf "def %s" (string_of_reglist rs)

let string_of_terminator = function
  | T_Branch (cond, r0, r1, l1, l2) ->
    Format.sprintf "branch %s, %s, %s, %s, %s"
      (string_of_cond cond)
      (string_of_expr r0)
      (string_of_expr r1)
      (string_of_label l1)
      (string_of_label l2)
  | T_Jump (l) ->
    Format.sprintf "jump %s"
      (string_of_label l)
  | T_Return xs ->
    Format.sprintf "return %s"
      (string_of_exprlist xs)

let indented_string_of_instr i = "    " ^ (string_of_instr i)
let indented_string_of_terminator i = "    " ^ (string_of_terminator i)

let string_of_block_body cfg label body =
  String.concat "\n"
    [ Format.sprintf "%s:" (string_of_label label) 
    ; Format.sprintf "    cfg successors: %s"
      (string_of_labellist @@ ControlFlowGraph.successors cfg label)
    ; Format.sprintf "    cfg predecessors: %s"
      (string_of_labellist @@ ControlFlowGraph.predecessors cfg label)
    ; String.concat "\n" (List.map indented_string_of_instr body)
    ]

let string_of_block cfg k v =
  let terminator = match ControlFlowGraph.terminator_safe cfg k with
    | None -> "<<no terminator>>"
    | Some t -> indented_string_of_terminator t
  in
  String.concat "\n"
    [ string_of_block_body cfg k v 
    ; terminator
    ]

let string_of_blockmap cfg =
  let f xs (k, v) = string_of_block cfg k v :: xs in
  let items = Seq.fold_left (fun xs x -> x::xs) [] (Hashtbl.to_seq @@ ControlFlowGraph.blockmap cfg) in
  let items = List.sort compare items in
  String.concat "\n" @@ List.rev @@ List.fold_left f  [] items

let string_of_cfg cfg =
  String.concat "\n"
    [ Format.sprintf "    cfg entry point: %s" (string_of_label @@ ControlFlowGraph.entry_label cfg)

    ; Format.sprintf "    cfg entry point successors: %s"
      (string_of_labellist @@ ControlFlowGraph.successors cfg @@ ControlFlowGraph.entry_label cfg)

    ; Format.sprintf "    cfg exit point: %s" (string_of_label @@ ControlFlowGraph.exit_label cfg)

    ; Format.sprintf "    cfg exit point predecessors : %s"
      (string_of_labellist @@ ControlFlowGraph.predecessors cfg @@ ControlFlowGraph.exit_label cfg)

    ; string_of_blockmap cfg
    ]

let string_of_procedure (Procedure {procid; cfg; frame_size; formal_parameters; _}) =
  String.concat "\n"
    [ "////////////////////////////////////// "
    ; Format.sprintf "procedure %s" (string_of_procid procid) 
    ; Format.sprintf "    frame size: %u" frame_size
    ; Format.sprintf "    formal parameters: %u" formal_parameters
    ; string_of_cfg cfg
    ]

let string_of_module_definition xs =
  String.concat "\n" @@ List.map string_of_procedure xs

let string_of_program (Program {procedures; _}) =
  String.concat "\n" @@ List.map string_of_procedure procedures
