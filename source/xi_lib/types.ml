type normal_type
  = TP_Int
  | TP_Bool
  | TP_Array of normal_type

let rec string_of_normal_type = function
  | TP_Int -> "int"
  | TP_Bool -> "bool"
  | TP_Array el -> string_of_normal_type el ^ "[]"

(* Rozszerzony typ
 * Lista 0 elementów - unit
 * Lista 1 element - normalny typ
 * Lista n elementów - krotka
 *)
type extended_type = normal_type list

let string_of_extended_type xs =
    String.concat ", " @@ List.map string_of_normal_type xs

type result_type
  = RT_Unit
  | RT_Void

type env_type
  = ENVTP_Var of normal_type
  | ENVTP_Fn of extended_type * extended_type

let string_of_env_type = function
  | ENVTP_Var t -> string_of_normal_type t
  | ENVTP_Fn (xs, []) -> Format.sprintf "fn(%s)"
    (string_of_extended_type xs)
  | ENVTP_Fn (xs, rs) -> Format.sprintf "fn(%s) -> (%s)"
    (string_of_extended_type xs)
    (string_of_extended_type rs)

module TypingEnvironment = struct

  (* W przeciwieństwie do specyfikacji nie trzymamy specjalnej zmiennej `ro`
    * oznaczającej return type. Trzymamy to w oddzielnym polu dla
    *  przejrzystości.
    *)

  type t = 
    { mapping: env_type Ast.IdMap.t
    ; return: extended_type option
    }

  (* Dodaj do środowiska.
    * Zwraca nowe środowisko oraz informację czy dany klucz `x` już nie był
    * w kontekście. Jak był to nic nie zwracamy, klient zapyta o starą wartość
    * by zgłosić komunikat o błędzie. Ta informacja o dodawaniu jest używana
    * aby wykrywać przykrywanie zmiennych.
    *)
  let add (x:Ast.identifier) (t:env_type) (env:t) =
    if Ast.IdMap.mem x env.mapping then
      env ,
      false
    else
      {env with mapping=Ast.IdMap.add x t env.mapping},
      true

  (* Pobranie, zwraca option *)
  let lookup x (t : t) = Ast.IdMap.find_opt x t.mapping

  (* Gdy wiemy że klucz jest w bazie i nie chce nam się rozpatrywać czy było
    * Some czy None *)
  let lookup_unsafe x t = 
    match lookup x t with
    | None -> failwith "TypingEnvironment.lookup_unsafe failed"
    | Some x -> x

  let empty : t = { mapping=Ast.IdMap.empty; return=None}

  let set_return t r = {t with return=Some r}

  let get_return t = t.return
end