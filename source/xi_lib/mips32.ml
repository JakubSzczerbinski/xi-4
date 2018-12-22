
type reg =
  | Reg of int

let string_of_reg_raw (Reg i) = Format.sprintf "$%u" i

let string_of_reg = function
  | Reg 0 -> "$zero"
  | Reg 1 -> "$at"
  | Reg 2 -> "$v0"
  | Reg 3 -> "$v1"
  | Reg 4 -> "$a0"
  | Reg 5 -> "$a1"
  | Reg 6 -> "$a2"
  | Reg 7 -> "$a3"
  | Reg 8 -> "$t0"
  | Reg 9 -> "$t1"
  | Reg 10 -> "$t2"
  | Reg 11 -> "$t3"
  | Reg 12 -> "$t4"
  | Reg 13 -> "$t5"
  | Reg 14 -> "$t6"
  | Reg 15 -> "$t7"
  | Reg 16 -> "$s0"
  | Reg 17 -> "$s1"
  | Reg 18 -> "$s2"
  | Reg 19 -> "$s3"
  | Reg 20 -> "$s4"
  | Reg 21 -> "$s5"
  | Reg 22-> "$s6"
  | Reg 23 -> "$s7"
  | Reg 24 -> "$t8"
  | Reg 25 -> "$t9"
  | Reg 26 -> "$k0"
  | Reg 27 -> "$k1"
  | Reg 28 -> "$gp"
  | Reg 29 -> "$sp"
  | Reg 30 -> "$fp"
  | Reg 31 -> "$ra"
  | r -> string_of_reg_raw r

let reg_zero = Reg 0
let reg_sp = Reg 29
let reg_fp = Reg 30
let reg_ra = Reg 31 

let reg_s = function
  | i when i < 8 ->
    Reg (16 + i)
  | i -> failwith @@ Format.sprintf "There is no $sp%u" i

type label =
  | Label of string

let string_of_label (Label s) = s

type instr =
  | I_Label of label
  | I_Add of reg * reg * reg
  | I_Addu of reg * reg * reg
  | I_Addi of reg * reg * Int32.t
  | I_Addiu of reg * reg * Int32.t
  | I_Sub of reg * reg * reg
  | I_Subu of reg * reg * reg
  | I_Div of reg * reg
  | I_Mult of reg * reg
  | I_Multu of reg * reg 
  | I_And of reg * reg * reg
  | I_Andi of reg * reg * Int32.t
  | I_Nor of reg * reg * reg
  | I_Or of reg * reg * reg
  | I_Ori of reg * reg * Int32.t
  | I_Xor of reg * reg * reg
  | I_Xori of reg * reg * Int32.t
  | I_Sll of reg * reg * reg
  | I_Sllv of reg * reg * reg
  | I_Sra of reg * reg * reg
  | I_Srav of reg * reg * reg
  | I_Srl of reg * reg * reg
  | I_Rol of reg * reg * reg
  | I_Ror of reg * reg * reg
  | I_Srlv of reg * reg * reg
  | I_Mfhi of reg
  | I_Mflo of reg
  | I_Lui of reg * Int32.t
  | I_Lb of reg * Int32.t * reg
  | I_Sb of reg * Int32.t * reg
  | I_Lw of reg * Int32.t * reg
  | I_Sw of reg * Int32.t * reg
  | I_Slt of reg * reg * reg
  | I_Slti of reg * reg * Int32.t
  | I_Sltu of reg * reg * reg
  | I_Beq of reg * reg * label
  | I_Bgez of reg * label
  | I_Bgezal of reg * label
  | I_Bgtz of reg * label
  | I_Blez of reg * label
  | I_Bltz of reg * label
  | I_Bltzal of reg * label
  | I_Bne of reg * reg * label
  | I_J of label
  | I_Jal of label
  | I_Jr of reg
  | I_Jalr of reg
  | I_Nop

let string_of_instr = function
  | I_Label l -> Format.sprintf "%s:"
    (string_of_label l)
  |I_Add (r0, r1, r2) -> Format.sprintf "add %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Addu (r0, r1, r2) -> Format.sprintf "addu %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Addiu (r0, r1, i) -> Format.sprintf "addiu %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (Int32.to_string i) 
  |I_Addi (r0, r1, i) -> Format.sprintf "addi %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (Int32.to_string i) 
  |I_Sub (r0, r1, r2) -> Format.sprintf "sub %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Subu (r0, r1, r2) -> Format.sprintf "subu %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Div (r0, r1) -> Format.sprintf "div %s, %s"
    (string_of_reg r0) (string_of_reg r1) 
  |I_Mult (r0, r1) -> Format.sprintf "mult %s, %s"
    (string_of_reg r0) (string_of_reg r1) 
  |I_Multu (r0, r1) -> Format.sprintf "multu %s, %s"
    (string_of_reg r0) (string_of_reg r1) 
  |I_And (r0, r1, r2) -> Format.sprintf "and %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Andi (r0, r1, i) -> Format.sprintf "andi %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (Int32.to_string i) 
  |I_Nor (r0, r1, r2) -> Format.sprintf "nor %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Or (r0, r1, r2) -> Format.sprintf "or %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Ori (r0, r1, i) -> Format.sprintf "ori %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (Int32.to_string i) 
  |I_Xor (r0, r1, r2) -> Format.sprintf "xor %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Xori (r0, r1, i) -> Format.sprintf "xori %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (Int32.to_string i) 
  |I_Sll (r0, r1, r2) -> Format.sprintf "sll %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Sllv (r0, r1, r2) -> Format.sprintf "sllv %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Srl (r0, r1, r2) -> Format.sprintf "srl %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Srlv (r0, r1, r2) -> Format.sprintf "srlv %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Mfhi (r0) -> Format.sprintf "mfhi %s"
    (string_of_reg r0)
  |I_Mflo (r0) -> Format.sprintf "mflo %s"
    (string_of_reg r0)
  |I_Lui (r0, i) -> Format.sprintf "lui %s, %s"
    (string_of_reg r0) (Int32.to_string i) 
  |I_Lb (r0, i0, r1) -> Format.sprintf "lb %s, %s(%s)"
    (string_of_reg r0) (Int32.to_string i0) (string_of_reg r1) 
  |I_Sb (r0, i0, r1) -> Format.sprintf "sb %s, %s(%s)"
    (string_of_reg r0) (Int32.to_string i0) (string_of_reg r1) 
  |I_Lw (r0, i0, r1) -> Format.sprintf "lw %s, %s(%s)"
    (string_of_reg r0) (Int32.to_string i0) (string_of_reg r1) 
  |I_Sw (r0, i0, r1) -> Format.sprintf "sw %s, %s(%s)"
    (string_of_reg r0) (Int32.to_string i0) (string_of_reg r1) 
  |I_Slt (r0, r1, r2) -> Format.sprintf "slt %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Sra (r0, r1, r2) -> Format.sprintf "sra %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Srav (r0, r1, r2) -> Format.sprintf "srav %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Rol (r0, r1, r2) -> Format.sprintf "srav %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Ror (r0, r1, r2) -> Format.sprintf "srav %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Slti (r0, r1, i) -> Format.sprintf "slti %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (Int32.to_string i) 
  |I_Sltu (r0, r1, r2) -> Format.sprintf "sltu %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_reg r2) 
  |I_Beq (r0, r1, l) -> Format.sprintf "beq %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_label l) 
  |I_Bgez (r0, l) -> Format.sprintf "bgez %s, %s"
    (string_of_reg r0) (string_of_label l) 
  |I_Bgezal (r0, l) -> Format.sprintf "bgezal %s, %s"
    (string_of_reg r0) (string_of_label l) 
  |I_Bgtz (r0, l) -> Format.sprintf "bgtz %s, %s"
    (string_of_reg r0) (string_of_label l) 
  |I_Blez (r0, l) -> Format.sprintf "blez %s, %s"
    (string_of_reg r0) (string_of_label l) 
  |I_Bltz (r0, l) -> Format.sprintf "bltz %s, %s"
    (string_of_reg r0) (string_of_label l) 
  |I_Bltzal (r0, l) -> Format.sprintf "bltzal %s, %s"
    (string_of_reg r0) (string_of_label l) 
  |I_Bne (r0, r1, l) -> Format.sprintf "bne %s, %s, %s"
    (string_of_reg r0) (string_of_reg r1) (string_of_label l) 
  |I_J (l) -> Format.sprintf "j %s"
    (string_of_label l)
  |I_Jal (l) -> Format.sprintf "jal %s"
    (string_of_label l)
  |I_Jr (r0) -> Format.sprintf "jr %s"
    (string_of_reg r0)
  |I_Jalr (r0) -> Format.sprintf "jalr %s"
    (string_of_reg r0)
  | I_Nop -> Format.sprintf "add $zero, $zero, $zero"

type program = (label * instr list) list


let indent x = "    " ^ x

let string_of_program (l, b) =
  String.concat "\n"
    [ Format.sprintf "%s:" (string_of_label l)
    ; String.concat "\n" (List.map indent @@ List.map string_of_instr b)
    ]

let string_of_program xs =
  String.concat "\n"
    (List.map string_of_program xs)
