open Ir

let reg_fp = REG_Spec 30

let reg_sp = REG_Spec 29

let reg_ra = REG_Spec 31

let reg_zero = REG_Spec 0

let expr_reg_zero = E_Reg reg_zero

let reg_v0 = REG_Hard 2

let reg_v1 = REG_Hard 3

module type REGISTERS_DESCRIPTION = sig

  val callee_saves_registers : reg list

  val caller_saves_registers : reg list

  val available_registers : reg list

  val arguments_registers : reg list

end


module NormalRegistersDescription : REGISTERS_DESCRIPTION = struct

  let callee_saves_registers = 
    [ REG_Hard 16
    ; REG_Hard 17
    ; REG_Hard 18
    ; REG_Hard 19
    ; REG_Hard 20
    ; REG_Hard 21
    ; REG_Hard 22
    ; REG_Hard 23
    ]

  let caller_saves_registers =
    [ REG_Hard 1
    ; REG_Hard 2
    ; REG_Hard 3
    ; REG_Hard 4
    ; REG_Hard 5
    ; REG_Hard 6
    ; REG_Hard 7
    ; REG_Hard 8
    ; REG_Hard 9
    ; REG_Hard 10
    ; REG_Hard 11
    ; REG_Hard 12
    ; REG_Hard 13
    ; REG_Hard 14
    ; REG_Hard 15
    ; REG_Hard 24
    ; REG_Hard 25
    ]

  let available_registers = List.flatten
    [ caller_saves_registers
    ; callee_saves_registers
    ]

  let arguments_registers =
    [ REG_Hard 4
    ; REG_Hard 5
    ; REG_Hard 6
    ; REG_Hard 7
    ]

end

module SimpleCallerRegistersDescription : REGISTERS_DESCRIPTION = struct

  let callee_saves_registers = 
    [ 
    ]

  let caller_saves_registers =
    [ REG_Hard 2
    ; REG_Hard 3
    ; REG_Hard 4
    ; REG_Hard 5
    ; REG_Hard 6
    ; REG_Hard 7
    ]

  let available_registers = List.flatten
    [ callee_saves_registers
    ; caller_saves_registers
    ]

  let arguments_registers =
    [ REG_Hard 4
    ; REG_Hard 5
    ]

end

let descriptions =
  [ "normal", (module NormalRegistersDescription : REGISTERS_DESCRIPTION )
  ; "simple_caller", (module SimpleCallerRegistersDescription : REGISTERS_DESCRIPTION )
  ]