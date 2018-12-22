open Xi_lib
open Iface

module Make(LP:LEXER_AND_PARSER) = struct

    module L = LP.Lexer

    module P = LP.Parser

    let open_file_lexbuf file = 
        let channel = open_in file in
        let lexbuf = Lexing.from_channel channel in
        (* Wpisujemy nazwe pliku (katalog ze ścieżki ucina Filename.basename)
         * do lexbuf. Dzięki temu Parser_utils.makeLocation będzie mógł lokacje
         * uzupełniać o prawidłową nazwę pliku.
         *)
        lexbuf.Lexing.lex_curr_p <- {
            lexbuf.Lexing.lex_curr_p with
            Lexing.pos_fname = Filename.basename file
            };
        lexbuf

    let parse_lexbuf f lexbuf =
        try
            Ok (P.file L.token lexbuf);
        with
        | P.Error ->
            let loc = Parser_utils.mkLocation lexbuf.Lexing.lex_curr_p in
            let token = Lexing.lexeme lexbuf in 
            let s = if String.length token > 0 
                then Printf.sprintf "syntax error: unexpected token: %s" token
                else Printf.sprintf "syntax error: unexpected end"
            in
            Error (loc, s)

        | Parser_utils.InvalidToken (loc, str) ->
            let s = Printf.sprintf "syntax error: invalid token: %s" str in
            Error (loc, s)

    let parse_file f = parse_lexbuf f (open_file_lexbuf f)
end

