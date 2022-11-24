(* BEFORE 0.5.0 there was no distinction between address and address payable!!! *)
(* msg.sender.transfer(x) to payable(msg.sender).transfer(x) *)
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
  | Return of expr
and arit_ops = 
  | Plus of expr * expr 
  | Div of expr * expr 
  | Times of expr * expr
  | Minus of expr * expr 
  | Exp of expr * expr 
  | Mod of expr * expr 
and bool_ops =
  | Neg of b_val
  | Conj of b_val * b_val
  | Disj of b_val * b_val
  | Equals of expr * expr 
  | Greater of expr * expr 
  | GreaterOrEquals of expr * expr
  | Lesser of expr * expr
  | LessOrEquals of expr * expr
  | Inequals of expr * expr
  




