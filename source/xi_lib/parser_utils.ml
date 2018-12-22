exception InvalidToken of Ast.location * string

let mkLocation pos = 
    let line   = pos.Lexing.pos_lnum in
    let column = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 in
    let file   = pos.Lexing.pos_fname in
    Ast.Location {line; column; file}