open Xi_lib
open Ast
open Types


module AllExpressionsAreTypecheck = struct

  exception MissingTypeInformation of location

  module Implementation(M:sig val node2type: (node_tag, normal_type) Hashtbl.t end) = struct

    open M

    let check_tag loc tag =
      match Hashtbl.find_opt node2type tag with
      | Some _ -> ()
      | None -> raise (MissingTypeInformation loc)

    let expr_subexpressions = function
      | EXPR_Id _ -> []
      | EXPR_Int _ -> []
      | EXPR_Char _ -> []
      | EXPR_String _ -> []
      | EXPR_Bool _ -> []

      | EXPR_Relation {lhs; rhs; _} ->
        [lhs; rhs]

      | EXPR_Binop {lhs; rhs; _} ->
        [lhs; rhs]

      | EXPR_Length {arg; _} ->
        [arg]

      | EXPR_Unop {sub; _} ->
        [sub]

      | EXPR_Call (Call {arguments; _}) ->
        arguments

      | EXPR_Index {expr; index; _} ->
        [expr; index]

      | EXPR_Struct {elements; _} ->
        elements

    let some2list = function 
      | Some x -> [x]
      | None -> []

    let block_substatements = function
      | STMTBlock {body; _} -> body

    let block_substatements_opt = function
      | Some (STMTBlock {body; _}) -> body
      | None -> []

    let stmt_subexpressions = function
      | STMT_Call (Call {arguments; _}) ->
        arguments

      | STMT_Assign {rhs; _} ->
        [rhs]

      | STMT_VarDecl {init=Some init; _} ->
        [init]

      | STMT_VarDecl {init=None; _} ->
        []

      | STMT_If {cond; _} ->
        [cond]

      | STMT_While {cond; _} ->
        [cond]

      | STMT_Return {values; _} ->
        values

      | STMT_MultiVarDecl {init=Call{arguments; _}; _} ->
        arguments

      | STMT_Block _ ->
        []

    let stmt_substatements = function
      | STMT_Call _ ->
        []

      | STMT_Assign _ ->
        []

      | STMT_VarDecl _ ->
        []

      | STMT_If {then_branch; else_branch; _} ->
        [then_branch] @ some2list else_branch

      | STMT_While {body; _} ->
        [body]

      | STMT_Return _ ->
        []

      | STMT_MultiVarDecl _ ->
        []

      | STMT_Block block ->
        block_substatements block


    let rec verify_expression e =
      check_tag (location_of_expression e) (tag_of_expression e);
      let sube = expr_subexpressions e in
      List.iter verify_expression sube

    let rec verify_statement s =
      let exprs = stmt_subexpressions s in
      let stmts = stmt_substatements s in
      List.iter verify_expression exprs;
      List.iter verify_statement stmts 

    let verify_block_opt s =
      let stmts = block_substatements_opt s in
      List.iter verify_statement stmts


    let verify_global_declaration = function
      | GDECL_Function {body; _} ->
        verify_block_opt body

    let verify_module_definition (ModuleDefinition {global_declarations}) =
      List.iter verify_global_declaration global_declarations

  end

  let verify_module_definition node2tag mdef =
    try
      let module Instance = Implementation(struct let node2type = node2tag end) in
      Instance.verify_module_definition mdef;
      true
    with MissingTypeInformation e ->
      Format.eprintf "Missing type information for expression %s\n%!" (string_of_location e);
      false

end