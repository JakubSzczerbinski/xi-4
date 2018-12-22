
type location = Location of { line: int; column: int; file: string }

let string_of_location (Location {line;column;file}) =
  Format.sprintf "%s:%u:%u" file line column

type identifier
 = Identifier of string

let string_of_identifier (Identifier i) = i

type node_tag =
  NodeTag of int

let string_of_node_tag (NodeTag i) =
  Format.sprintf "%%node%i" i

type binop =
  | BINOP_And
  | BINOP_Or
  | BINOP_Add
  | BINOP_Sub
  | BINOP_Mult
  | BINOP_Div
  | BINOP_Rem

let string_of_binop = function
  | BINOP_And -> "&"
  | BINOP_Or -> "|"
  | BINOP_Add -> "+"
  | BINOP_Sub -> "-"
  | BINOP_Mult -> "*"
  | BINOP_Div -> "/"
  | BINOP_Rem -> "%"

type relop =
  | RELOP_Eq
  | RELOP_Ne
  | RELOP_Lt
  | RELOP_Gt
  | RELOP_Le
  | RELOP_Ge

let string_of_relop = function
  | RELOP_Eq -> "=="
  | RELOP_Ne -> "!="
  | RELOP_Lt -> "<"
  | RELOP_Gt -> ">"
  | RELOP_Ge -> ">="
  | RELOP_Le -> "<="

type unop =
  | UNOP_Not
  | UNOP_Neg

type type_expression =
  | TEXPR_Int of
    { loc:location
    }

  | TEXPR_Bool of
    { loc:location
    }

  | TEXPR_Array of
    { loc:location
    ; sub:type_expression
    ; dim:expression option
    }

and expression =
  | EXPR_Id of
    { tag:node_tag
    ; loc:location
    ; id:identifier
    }

  | EXPR_Int of 
    { tag:node_tag
    ; loc:location
    ; value:Int32.t
    }

  | EXPR_Char of 
    { tag:node_tag
    ; loc:location
    ; value:Char.t
    }

  | EXPR_String of
    { tag:node_tag
    ; loc:location
    ; value:string
    }

  | EXPR_Bool of 
    { tag:node_tag
    ; loc:location
    ; value:bool
    }

  | EXPR_Relation of
    { tag:node_tag
    ; loc:location
    ; op:relop
    ; lhs:expression
    ; rhs:expression
    }

  | EXPR_Binop of
    { tag:node_tag
    ; loc:location
    ; op:binop
    ; lhs:expression
    ; rhs:expression
    }

  | EXPR_Length of
    { tag:node_tag
    ; loc:location
    ; arg:expression
    }

  | EXPR_Unop of
    { tag:node_tag
    ; loc:location
    ; op:unop
    ; sub:expression
    }

  | EXPR_Call of
    call

  | EXPR_Index of
    { tag:node_tag
    ; loc:location
    ; expr:expression
    ; index:expression
    }

  | EXPR_Struct of
    { tag:node_tag
    ; loc:location
    ; elements: expression list
    }

and call =
  | Call of 
    { tag:node_tag
    ; loc:location
    ; callee:identifier
    ; arguments:expression list
    }


let location_of_expression = function
  | EXPR_Id {loc; _} -> loc
  | EXPR_Struct {loc; _} -> loc
  | EXPR_Index {loc; _} -> loc
  | EXPR_Call (Call {loc; _}) -> loc
  | EXPR_Unop {loc; _} -> loc
  | EXPR_Binop {loc; _} -> loc
  | EXPR_Relation {loc; _} -> loc
  | EXPR_Length {loc; _} -> loc
  | EXPR_Int {loc; _} -> loc
  | EXPR_Char {loc; _} -> loc
  | EXPR_Bool {loc; _} -> loc
  | EXPR_String {loc; _} -> loc

let tag_of_expression = function
  | EXPR_Id {tag; _} -> tag
  | EXPR_Struct {tag; _} -> tag
  | EXPR_Index {tag; _} -> tag
  | EXPR_Call (Call {tag; _}) -> tag
  | EXPR_Unop {tag; _} -> tag
  | EXPR_Binop {tag; _} -> tag
  | EXPR_Relation {tag; _} -> tag
  | EXPR_Length {tag; _} -> tag
  | EXPR_Int {tag; _} -> tag
  | EXPR_Char {tag; _} -> tag
  | EXPR_Bool {tag; _} -> tag
  | EXPR_String {tag; _} -> tag

let location_of_call (Call {loc; _}) = loc

let identifier_of_call (Call {callee; _}) = callee

type var_declaration =
  |  VarDecl of
    { loc:location
    ; id:identifier
    ; tp:type_expression
    }

let location_of_var_declaration (VarDecl {loc; _}) = loc
let identifier_of_var_declaration (VarDecl {id; _}) = id
let type_expression_of_var_declaration (VarDecl {tp; _}) = tp

module IdMap = Map.Make(struct
  type t = identifier

  let compare = compare
 end)

type lvalue =
  | LVALUE_Id of
    { loc:location
    ; id:identifier
    }

  | LVALUE_Index of
    { loc:location
    ; sub:expression
    ; index:expression
    }

type statement =
  | STMT_Call of
    call

  | STMT_Assign of
    { loc:location
    ; lhs:lvalue
    ; rhs:expression
    }

  | STMT_VarDecl of
    { var:var_declaration
    ; init:expression option
    }

  | STMT_If of
    { loc:location
    ; cond:expression
    ; then_branch: statement
    ; else_branch: statement option
    }

  | STMT_While of
    { loc:location
    ; cond:expression
    ; body: statement
    }

  | STMT_Return of
    { loc:location
    ; values:expression list
    }

  | STMT_MultiVarDecl of
    { loc:location 
    ; vars:var_declaration option list
    ; init:call
    }

  | STMT_Block of
    statement_block 

and statement_block =
  | STMTBlock of 
    { loc:location
    ; body: statement list
    }

let location_of_block (STMTBlock {loc; _}) = loc

let location_of_statement = function
  | STMT_Assign {loc; _} -> loc
  | STMT_While {loc; _} -> loc
  | STMT_Call call -> location_of_call call
  | STMT_Block block -> location_of_block block
  | STMT_Return {loc; _} -> loc 
  | STMT_VarDecl {var; _} -> location_of_var_declaration var
  | STMT_MultiVarDecl {loc; _} -> loc
  | STMT_If {loc; _} -> loc

type global_declaration =
  | GDECL_Function of 
    { loc:location
    ; id:identifier
    ; formal_parameters:var_declaration list
    ; return_types:type_expression list
    ; body:statement_block option
    }
  
type module_definition = ModuleDefinition of
  { global_declarations: global_declaration list
  }
