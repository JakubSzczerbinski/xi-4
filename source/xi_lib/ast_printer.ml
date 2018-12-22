open Ast


let string_of_binop = function
  | BINOP_And -> "&"
  | BINOP_Or -> "|"
  | BINOP_Add -> "+"
  | BINOP_Sub -> "-"
  | BINOP_Mult -> "*"
  | BINOP_Div -> "/"
  | BINOP_Rem -> "%"

let string_of_relop = function
  | RELOP_Eq -> "=="
  | RELOP_Ne -> "!="
  | RELOP_Lt -> "<"
  | RELOP_Gt -> ">"
  | RELOP_Le -> "<="
  | RELOP_Ge -> ">="

let string_of_unop = function
  | UNOP_Not -> "!"
  | UNOP_Neg -> "-"

let indent x = "  " ^ x

let indentxs = List.map indent 

let rec show_expression = function
  | EXPR_Id {id; _} ->
    string_of_identifier id


  | EXPR_Int {value; _} ->
    Int32.to_string value

  | EXPR_Char {value; _} ->
    Format.sprintf "%c" value
 
  | EXPR_String {value; _} ->
    value
  
  | EXPR_Bool {value; _} ->
    string_of_bool value

  | EXPR_Binop {op; lhs; rhs; _} ->
    String.concat ""
      [ "("
      ; show_expression lhs
      ; " "
      ; string_of_binop op
      ; " "
      ; show_expression rhs
      ; ")"
      ]

  | EXPR_Relation {op; lhs; rhs; _} ->
    String.concat ""
      [ "("
      ; show_expression lhs
      ; " "
      ; string_of_relop op
      ; " "
      ; show_expression rhs
      ; ")"
      ]
  
  | EXPR_Length {arg; _} ->
    String.concat ""
      [ "length("
      ; show_expression arg
      ; ")"
      ]

  | EXPR_Unop {op; sub; _} ->
    String.concat ""
      [ string_of_unop op
      ; show_expression sub
      ]

  | EXPR_Call call ->
    show_call call

  | EXPR_Index {expr; index; _} ->
    String.concat ""
      [ show_expression expr
      ; "["
      ; show_expression index
      ; "]"
      ]

  | EXPR_Struct {elements; _} ->
    String.concat ""
      [ "{"
      ; String.concat ", " (List.map show_expression elements)
      ; "}"
      ]

and show_call (Call {callee; arguments; _}) =
  String.concat ""
    [ string_of_identifier callee
    ; "("
    ; String.concat ", " (List.map show_expression arguments)
    ; ")"
    ]

let rec show_type_expression = function
  | TEXPR_Int _ ->
    "int"

  | TEXPR_Bool _ ->
    "bool"

  | TEXPR_Array {sub;dim;_} ->
    String.concat ""
       [ show_type_expression sub
       ; "["
       ; (match dim with | None -> "" | Some e -> show_expression e)
       ; "]"
       ]

let show_var_declaration (VarDecl {id; tp; _}) =
  String.concat ""
    [ string_of_identifier id
    ; ":"
    ; show_type_expression tp
    ]

let show_var_declaration_opt = function
  | Some v -> show_var_declaration v
  | None -> "_"

let show_lvalue = function
  | LVALUE_Id {id; _} ->
    string_of_identifier id
  | LVALUE_Index {sub; index; _} ->
    String.concat ""
      [ show_expression sub
      ; "["
      ; show_expression index
      ; "]"
      ]


let rec showxs_statement = function
  | STMT_Call call ->
    [ show_call call
    ]
  
  | STMT_VarDecl {var; init=None} ->
    [ show_var_declaration var
    ]

  | STMT_VarDecl {var; init=Some v} ->
    [ String.concat " " 
      [ show_var_declaration var
      ; "="
      ; show_expression v
      ]
    ]

  | STMT_Return {values; _} ->
    [ String.concat " " 
      [ "return"
      ; String.concat ", " (List.map show_expression values)
      ]
    ]
  
  | STMT_Block blok ->
    showxs_block blok

  | STMT_While {cond; body; _} ->
    List.concat
      [ [ String.concat " "
        [ "while"
        ; "("
        ; show_expression cond
        ; ")"
        ] ]
      ; showxs_statement_as_block body
      ]

  | STMT_If {cond; then_branch; else_branch=None; _} ->
    List.concat
      [ [ String.concat " "
        [ "if"
        ; "("
        ; show_expression cond
        ; ")"
        ] ]
      ; showxs_statement_as_block then_branch
      ]

  | STMT_If {cond; then_branch; else_branch=Some else_branch; _} ->
    List.concat
      [ [ String.concat " "
        [ "if"
        ; "("
        ; show_expression cond
        ; ")"
        ] ]
      ; showxs_statement_as_block then_branch
      ; [ "else" ]
      ; showxs_statement_as_block else_branch
      ]
    | STMT_Assign {lhs; rhs; _} ->
      [ String.concat " "
        [ show_lvalue lhs
        ; "="
        ; show_expression rhs
        ]
      ]
    | STMT_MultiVarDecl {vars; init; _} ->
      [ String.concat " "
        [ String.concat ", " (List.map show_var_declaration_opt vars)
        ; "="
        ; show_call init
        ]
      ]

and showxs_block = function
  | STMTBlock {body; _} ->
    List.concat
    [ ["{"]
    ; indentxs @@ List.concat @@ List.map showxs_statement body
    ; ["}"]
    ]

and showxs_statement_as_block = function
  | STMT_Block blok ->
    showxs_block blok
  |  s ->
    List.concat
    [ ["{"]
    ; indentxs @@ showxs_statement s
    ; ["}"]
    ]

let show_formal_parameters params =
  String.concat ", " @@ List.map show_var_declaration params


let show_return_types = function
  | [] ->
    ""
  | return_types ->
    ": " ^ String.concat ", " (List.map show_type_expression return_types)

let showxs_global_declaration = function
  | GDECL_Function {id; body; formal_parameters; return_types; _} ->
    List.concat
      [ [ String.concat ""
        [ string_of_identifier id
        ; "("
        ; show_formal_parameters formal_parameters
        ; ")"
        ; show_return_types return_types
        ] ]
      ; match body with
        | Some body -> showxs_block body
        | None -> []
      ]

let showxs_module_definition (ModuleDefinition {global_declarations; _}) = 
  let f x =
    showxs_global_declaration x @ [""]
  in
  List.flatten (List.map f global_declarations)

let show_module_definition m =
  String.concat "\n" @@ showxs_module_definition m