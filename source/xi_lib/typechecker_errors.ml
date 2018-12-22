open Ast
open Types

type type_checking_error =

    (* Ogólny błąd, że oczekiwany typ się nie zgadza z rzeczywistym *)
  | TCERR_TypeMismatch of
    { loc: location
    ; expected: normal_type
    ; actual: normal_type
    }

    (* Błąd typu przy multireturn *)
  | TCERR_BindingTypeMismatch of
    { loc: location
    ; expected: normal_type
    ; actual: normal_type
    ; id: identifier
    }

    (* Wywołaliśmy procedurę/funkcję ze złą liczbą argumentów *)
  | TCERR_BadNumberOfActualArguments of
    { loc: location
    ; expected: int
    ; actual: int
    }

    (* Return dostał złą liczbę parametrów *)
  | TCERR_BadNumberOfReturnValues of
    { loc: location
    ; expected: int
    ; actual: int
    }

    (* Nieznany identyfikator *)
  | TCERR_UnknownIdentifier of
    { loc: location
    ; id: identifier
    }

    (* Identyfikator nie jest zmienną (a np jest funkcją) *)
  | TCERR_IdentifierIsNotVariable of
    { loc: location
    ; id: identifier
    }

    (* Generyczny błąd gdyby inne nie pasowały *)
  | TCERR_OtherError of
    { loc: location
    ; descr: string
    }

    (* Wywołujemy identyfikator, który nie jest funkcją/procedurą *)
  | TCERR_IdentifierIsNotCallable of
    { loc: location
    ; id: identifier
    }

    (* Brakuje return gdzieś *)
  | TCERR_NotAllControlPathsReturnValue of
    { loc: location
    ; id: identifier
    }

    (* Użyliśmy w wyrażeniu multireturnowej funkcji *)
  | TCERR_ExpectedFunctionReturningOneValue of
    { loc: location
    ; id: identifier
    }

    (* Użyliśmy w multireturnie zywkłej funkcji *)
  | TCERR_ExpectedFunctionReturningManyValues of
    { loc: location
    ; expected: int
    ; actual: int
    ; id: identifier
    }

    (* Return w procedurze *)
  | TCERR_ProcedureCannotReturnValue of
    { loc: location
    }

    (* Brakuje parametru w return *)
  | TCERR_FunctionMustReturnValue of
    { loc: location
    }
  
    (* Typ miał być tablicą *)
  | TCERR_ExpectedArray of
    { loc: location
    ; actual: normal_type
    }

    (* Przykryliśmy nazwę *)
  | TCERR_ShadowsPreviousDefinition of
    { loc: location
    ; id: identifier
    }

    (* W wyrażeniu typowym pojawiło się wyrażenie oznaczające rozmiar *)
  | TCERR_ArrayInitializationForbidden of
    { loc: location }

    (* Generyczny błąd, że nie dało się zrekonstruować typu *)
  | TCERR_CannotInferType of
    { loc: location }

let string_of_type_checking_error = function
  | TCERR_TypeMismatch {loc; actual; expected} ->
    Format.sprintf "%s: error: type mismatch: expected %s; got %s"
      (string_of_location loc)
      (string_of_normal_type expected)
      (string_of_normal_type actual)

  | TCERR_BindingTypeMismatch {loc; actual; expected; id} ->
    Format.sprintf "%s: error: type mismatch: expected %s; got %s; binding %s"
      (string_of_location loc)
      (string_of_normal_type expected)
      (string_of_normal_type actual)
      (string_of_identifier id)

  | TCERR_BadNumberOfActualArguments {loc; actual; expected} ->
    Format.sprintf "%s: error: bad number of actual arguments: expected %u; got %u"
      (string_of_location loc)
      (expected)
      (actual)

  | TCERR_BadNumberOfReturnValues {loc; actual; expected} ->
    Format.sprintf "%s: error: bad number of return values: expected %u; got %u"
      (string_of_location loc)
      (expected)
      (actual)

  | TCERR_UnknownIdentifier {loc; id} ->
    Format.sprintf "%s: unknown identifier: %s"
      (string_of_location loc)
      (string_of_identifier id)

  | TCERR_IdentifierIsNotVariable {loc; id} ->
    Format.sprintf "%s: identifier is not a variable: %s"
      (string_of_location loc)
      (string_of_identifier id)

  | TCERR_IdentifierIsNotCallable {loc; id} ->
    Format.sprintf "%s: identifier is not callable: %s"
      (string_of_location loc)
      (string_of_identifier id)

  | TCERR_OtherError {loc; descr} ->
    Format.sprintf "%s: error: %s"
      (string_of_location loc)
      descr

  | TCERR_NotAllControlPathsReturnValue {loc; id} ->
    Format.sprintf "%s: not all control paths return value: %s"
      (string_of_location loc)
      (string_of_identifier id)

  | TCERR_ExpectedFunctionReturningOneValue {loc; id} ->
    Format.sprintf "%s: expected function returning exactly one value: %s"
      (string_of_location loc)
      (string_of_identifier id)

  | TCERR_ExpectedFunctionReturningManyValues {loc; id; expected; actual} ->
    Format.sprintf "%s: expected function returning %u values, not %u: %s"
      (string_of_location loc)
      expected actual
      (string_of_identifier id)

  | TCERR_ExpectedArray {loc; actual} ->
    Format.sprintf "%s: expected array, not: %s"
      (string_of_location loc)
      (string_of_normal_type actual)

  | TCERR_FunctionMustReturnValue {loc} ->
    Format.sprintf "%s: function must return something"
      (string_of_location loc)

  | TCERR_ProcedureCannotReturnValue {loc} ->
    Format.sprintf "%s: procedure cannot return value"
      (string_of_location loc)

  | TCERR_ShadowsPreviousDefinition {loc; id} ->
    Format.sprintf "%s: shadows previous definition: %s"
      (string_of_location loc)
      (string_of_identifier id)

  | TCERR_ArrayInitializationForbidden {loc} ->
    Format.sprintf "%s: array initialization is forbidden here"
      (string_of_location loc)

  | TCERR_CannotInferType {loc} ->
    Format.sprintf "%s: cannot infer type"
      (string_of_location loc)




  module MakeCollectingErrorReporter () = struct

    let r = ref []

    let add e = r := e :: !r

    let wrap f x =
      let result = f x in
      let errors = List.rev !r in
      r := [];
      match errors with
      | [] -> Ok result
      | xs -> Error xs

    let report_type_mismatch ~loc ~expected ~actual =
      add @@ TCERR_TypeMismatch {loc;expected;actual}

    let report_binding_type_mismatch ~loc ~expected ~actual ~id =
      add @@ TCERR_BindingTypeMismatch {loc;expected;actual; id}

    let report_other_error ~loc ~descr =
      add @@ TCERR_OtherError {loc; descr}

    let report_identifier_is_not_variable ~loc ~id =
      add @@ TCERR_IdentifierIsNotVariable {loc; id}

    let report_unknown_identifier ~loc ~id =
      add @@ TCERR_UnknownIdentifier {loc; id}

    let report_identifier_is_not_callable ~loc ~id =
      add @@ TCERR_IdentifierIsNotCallable {loc; id}

    let report_bad_number_of_arguments ~loc ~expected ~actual =
      add @@ TCERR_BadNumberOfActualArguments {loc; expected; actual}

    let report_bad_number_of_return_values ~loc ~expected ~actual =
      add @@ TCERR_BadNumberOfReturnValues {loc; expected; actual}

    let report_expected_function_returning_one_value ~loc ~id =
      add @@ TCERR_ExpectedFunctionReturningOneValue {loc;id}

    let report_expected_function_returning_many_values ~loc ~id ~expected ~actual =
      add @@ TCERR_ExpectedFunctionReturningManyValues {loc;id; expected;actual}

    let report_function_must_return_something ~loc =
      add @@ TCERR_FunctionMustReturnValue {loc}

    let report_procedure_cannot_return_value ~loc =
      add @@ TCERR_ProcedureCannotReturnValue {loc}

    let report_expected_array ~loc ~actual =
      add @@ TCERR_ExpectedArray {loc; actual}

    let report_not_all_control_paths_return_value ~loc ~id =
      add @@ TCERR_NotAllControlPathsReturnValue {loc; id}

    let report_shadows_previous_definition ~loc ~id =
      add @@ TCERR_ShadowsPreviousDefinition {loc; id}

    let report_array_initialization_forbidden ~loc =
      add @@ TCERR_ArrayInitializationForbidden {loc}

    let report_cannot_infer ~loc =
      add @@ TCERR_CannotInferType {loc}


  end

  (* Kopia poniewaz chcemy aby typ wyniku funkcji `add` był dowolny bo sterowanie się kończy przez raise *)
  module MakeOneShotErrorReporter() = struct 

    exception TypeCheckingError of type_checking_error

    let add e = raise (TypeCheckingError e)

    let wrap f x =
      try
        Ok (f x)
      with (TypeCheckingError e) ->
        Error [e]

    let report_type_mismatch ~loc ~expected ~actual =
      add @@ TCERR_TypeMismatch {loc;expected;actual}

    let report_binding_type_mismatch ~loc ~expected ~actual ~id =
      add @@ TCERR_BindingTypeMismatch {loc;expected;actual; id}

    let report_other_error ~loc ~descr =
      add @@ TCERR_OtherError {loc; descr}

    let report_identifier_is_not_variable ~loc ~id =
      add @@ TCERR_IdentifierIsNotVariable {loc; id}

    let report_unknown_identifier ~loc ~id =
      add @@ TCERR_UnknownIdentifier {loc; id}

    let report_identifier_is_not_callable ~loc ~id =
      add @@ TCERR_IdentifierIsNotCallable {loc; id}

    let report_bad_number_of_arguments ~loc ~expected ~actual =
      add @@ TCERR_BadNumberOfActualArguments {loc; expected; actual}

    let report_bad_number_of_return_values ~loc ~expected ~actual =
      add @@ TCERR_BadNumberOfReturnValues {loc; expected; actual}

    let report_expected_function_returning_one_value ~loc ~id =
      add @@ TCERR_ExpectedFunctionReturningOneValue {loc;id}

    let report_expected_function_returning_many_values ~loc ~id ~expected ~actual =
      add @@ TCERR_ExpectedFunctionReturningManyValues {loc;id; expected;actual}

    let report_function_must_return_something ~loc =
      add @@ TCERR_FunctionMustReturnValue {loc}

    let report_procedure_cannot_return_value ~loc =
      add @@ TCERR_ProcedureCannotReturnValue {loc}

    let report_expected_array ~loc ~actual =
      add @@ TCERR_ExpectedArray {loc; actual}

    let report_not_all_control_paths_return_value ~loc ~id =
      add @@ TCERR_NotAllControlPathsReturnValue {loc; id}

    let report_shadows_previous_definition ~loc ~id =
      add @@ TCERR_ShadowsPreviousDefinition {loc; id}

    let report_array_initialization_forbidden ~loc =
      add @@ TCERR_ArrayInitializationForbidden {loc}

    let report_cannot_infer ~loc =
      add @@ TCERR_CannotInferType {loc}
  
  end 
