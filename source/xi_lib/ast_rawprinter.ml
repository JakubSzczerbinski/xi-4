open Ast


let string_of_binop = function
  | BINOP_And -> "BINOP_And"
  | BINOP_Or -> "BINOP_Or"
  | BINOP_Add -> "BINOP_Add"
  | BINOP_Sub -> "BINOP_Sub"
  | BINOP_Mult -> "BINOP_Mult"
  | BINOP_Div -> "BINOP_Div"
  | BINOP_Rem -> "BINOP_Rem"

let string_of_relop = function
  | RELOP_Eq -> "RELOP_Eq"
  | RELOP_Ne -> "RELOP_Ne"
  | RELOP_Lt -> "RELOP_Lt"
  | RELOP_Gt -> "RELOP_Gt"
  | RELOP_Le -> "RELOP_Le"
  | RELOP_Ge -> "RELOP_Ge"

let string_of_unop = function
  | UNOP_Not -> "UNOP_Not"
  | UNOP_Neg -> "UNOP_Neg"

let indent x = "  " ^ x
let indentfmt fmt =
  let cont = Format.sprintf "   %s"  in 
  Format.ksprintf cont fmt

let indentxs = List.map indent 

type p =
  | P_String of string
  | P_Sequence of p list
  | P_List of p list
  | P_Dict of string * (string * p) list

type r =
  | R_String of string
  | R_Indent of r 
  | R_Break
  | R_Tab
  | R_Group of r list

let render_r = function
  | R_String s -> s
  | R_Tab -> "   "
  | R_Break -> "\n"
  | R_Group _ -> failwith "R_Group should be eliminated"
  | R_Indent _ -> failwith "R_Indent should be eliminated"

let rec insert_tabs tabs = function
  | R_Indent r ->
    insert_tabs (R_Tab::tabs) r
  | R_Break ->
    R_Group [R_Break; R_Group tabs]
  | R_Group rs ->
    R_Group (List.map (insert_tabs tabs) rs)
  | r ->
    r

let rec flatten = function
  | R_Indent _ -> failwith "R_Indent should be eliminated"
  | R_Group xs -> List.concat @@ List.map flatten xs
  | r -> [r]

let render_r r =
  String.concat "" @@ List.map render_r @@ flatten @@ insert_tabs [] r

let rec render_p = function
  | P_String s ->
    R_String s
  | P_List xs ->
    let rec f acc = function
      | [] ->
        R_Group (List.rev acc)

      | x::xs ->
        let entry = R_Group [render_p x; R_String ";"; R_Break] in
        f (entry::acc) xs
    in
    R_Group
      [ R_String "["
      ; R_Indent (R_Group [R_Break; f [] xs])
      ; R_String "]"
      ]

  | P_Dict (kind, items) ->
    let rec f acc = function
      | [] ->
        R_Group (List.rev acc)
      | (k,v)::xs ->
        let entry = R_Group [R_String k; R_String " = "; R_Indent (render_p v); R_String ";"; R_Break] in
        f (entry::acc) xs
    in
    R_Group 
      [ R_String kind
      ; R_String " "
      ; R_String "{"
      ; R_Indent (R_Group [R_Break; f [] items])
      ; R_String "}"
      ]
  
  | P_Sequence xs ->
    R_Group (List.map render_p xs)

let p_dict k items = P_Dict (k,items)

let p_identifier id = P_String (Format.sprintf "\"%s\"" @@ string_of_identifier id)
let p_string id = P_String (Format.sprintf "\"%s\"" id)
let p_location loc = P_String (string_of_location loc)
let p_node_tag tag = P_String (string_of_node_tag tag)
let p_i32 i = P_String (Int32.to_string i)
let p_char c = P_String (Format.sprintf "'%c'" c)
let p_bool b = P_String (string_of_bool b)

let p_opt f = function
  | None -> P_String "None"
  | Some x -> P_Sequence [P_String "Some "; f x]


let rec p_expression = function 
  | EXPR_Id {loc; tag; id} -> p_dict "EXPR_Id"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "id", p_identifier id
    ]
  
  | EXPR_Int {tag; loc; value} -> p_dict "EXPR_Int"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "value", p_i32 value
    ]
  
  | EXPR_Char {tag; loc; value} -> p_dict "EXPR_Char"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "value", p_char value
    ]

  | EXPR_String {tag; loc; value} -> p_dict "EXPR_String"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "value", p_string value
    ]

  | EXPR_Bool {tag; loc; value} -> p_dict "EXPR_Bool"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "value", p_bool value
    ]

  | EXPR_Relation {tag; loc; op; lhs; rhs} -> p_dict "EXPR_Relation"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "op", P_String (string_of_relop op)
    ; "lhs", p_expression lhs
    ; "rhs", p_expression rhs
    ]

  | EXPR_Binop {tag; loc; op; lhs; rhs} -> p_dict "EXPR_Binop"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "op", P_String (string_of_binop op)
    ; "lhs", p_expression lhs
    ; "rhs", p_expression rhs
    ]

  | EXPR_Unop {tag; loc; op; sub} -> p_dict "EXPR_Unop"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "op", P_String (string_of_unop op)
    ; "sub", p_expression sub
    ]
  
  | EXPR_Length {tag; loc; arg} -> p_dict "EXPR_Length"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "arg", p_expression arg
    ]

  | EXPR_Index {tag; loc; expr; index} -> p_dict "EXPR_Index"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "expr", p_expression expr
    ; "index", p_expression index
    ]

  | EXPR_Struct {tag; loc; elements} -> p_dict "EXPR_Struct"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "elements", P_List (List.map p_expression elements)
    ]

  | EXPR_Call call -> P_Sequence
    [ P_String "EXPR_Call "
    ; p_call call
    ]

and p_call = function
  | Call {tag; loc; callee; arguments} -> p_dict "Call"
    [ "loc", p_location loc
    ; "tag", p_node_tag tag
    ; "callee", p_identifier callee
    ; "arguments", P_List (List.map p_expression arguments)
    ]

let rec p_type_expression = function
  | TEXPR_Int {loc} -> p_dict "TEXPR_Int"
    [ "loc", p_location loc
    ]
  
  | TEXPR_Bool {loc} -> p_dict "TEXPR_Bool"
    [ "loc", p_location loc
    ]
  
  | TEXPR_Array {loc;sub;dim} -> p_dict "TPEXPR_Array"
    [ "loc", p_location loc
    ; "sub", p_type_expression sub
    ; "dim", p_opt p_expression dim
    ]

let p_lvalue = function
  | LVALUE_Id {loc; id} -> p_dict "LVALUE_Id"
    [ "loc", p_location loc
    ; "id", p_identifier id
    ]
  | LVALUE_Index {loc; sub; index} -> p_dict "LVALUE_Index"
    [ "loc", p_location loc
    ; "sub", p_expression sub
    ; "index", p_expression index
    ]

let p_var_declaration = function
  | VarDecl {loc;id;tp} -> p_dict "VarDecl"
    [ "loc", p_location loc
    ; "id",  p_identifier id
    ; "tp", p_type_expression tp
    ]

let rec p_statement = function
  | STMT_Call call -> P_Sequence
    [ P_String "STMT_Call "
    ; p_call call
    ]
  
  | STMT_Assign {loc; lhs; rhs} -> p_dict "STMT_Assign"
    [ "loc", p_location loc
    ; "lhs", p_lvalue lhs
    ; "rhs", p_expression rhs
    ]

  | STMT_VarDecl {var; init} -> p_dict "STMT_VarDecl"
    [ "var", p_var_declaration var
    ; "init", p_opt p_expression init
    ]

  | STMT_If {loc; cond; then_branch; else_branch} -> p_dict "STMT_If"
    [ "loc", p_location loc
    ; "cond", p_expression cond
    ; "then_branch", p_statement then_branch
    ; "else_branch", p_opt p_statement else_branch
    ]

  | STMT_While {loc; cond; body} -> p_dict "STMT_While"
    [ "loc", p_location loc
    ; "cond", p_expression cond
    ; "body", p_statement body
    ]
  
  | STMT_Block block -> P_Sequence
    [ P_String "STMT_Block "
    ; p_statement_block block
    ]
  
  | STMT_MultiVarDecl {loc; vars; init} -> p_dict "STMT_MultiVarDecl"
    [ "loc", p_location loc
    ; "vars", P_List (List.map (p_opt p_var_declaration) vars)
    ; "init", p_call init
    ]
  
  | STMT_Return {loc; values} -> p_dict "STMT_Return"
    [ "loc", p_location loc
    ; "values", P_List (List.map p_expression values)
    ]

and p_statement_block = function
  | STMTBlock {loc; body} -> p_dict "STMTBlock"
    [ "loc", p_location loc
    ; "body", P_List (List.map p_statement body)
    ]



let p_global_declaration = function
  | GDECL_Function {loc;id;formal_parameters; return_types; body} ->
    p_dict "GDECL_Function"
      [ "loc", p_location loc
      ; "id", p_identifier id
      ; "formal_parameters", P_List (List.map p_var_declaration formal_parameters)
      ; "return_types", P_List (List.map p_type_expression return_types)
      ; "body", p_opt p_statement_block body
      ]

let p_module_definition = function
  | ModuleDefinition {global_declarations} -> P_Sequence 
    [ P_String "ModuleDefinition "
    ; P_List (List.map p_global_declaration global_declarations)
    ]

let show_module_definition mdef =
  let p = p_module_definition mdef in
  render_r @@ render_p p
