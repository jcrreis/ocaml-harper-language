type t_exp = 
  | C of string (* * hash_contract_code? *)
  | Bool
  | Unit 
  | UInt 
  | Address

type b_val =
  | True
  | False

type values = 
  | VBool of b_val
  | VUInt of int 
  | VAddress of string 
  | VUnit 
  | VContract of string


type expr =
  | Var of string
  | Val of values
  | This of string (* * string (? contracto a que se refer o this) *)
  | MsgSender 
  | MsgValue 
  | Balance of expr
  | Address of expr 
  | Assign of string * expr
  | Transfer of expr * expr
  | Let of string * expr * expr
  | New of string * expr (* list of expr ? parameters *)
  | Revert 
  | If of expr * expr * expr 
  | Seq of expr * expr




