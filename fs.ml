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
  | This 
  | MsgSender 
  | MsgValue 
  | Balance of expr
  | Address of expr 
  | StateRead of expr * string
  | Transfer of expr * expr
  | New of string * expr (* list of expr ? parameters *)
  | Cons of string * expr 
  | Seq of expr * expr
  | Let of (*t_exp * ?*) string * expr * expr (* EM SOLIDITY NÃO EXISTE *)
  | Assign of string * expr
  | StateAssign of expr * string * expr
  | MapRead of expr * expr 
  | MapWrite of expr * expr * expr
  | Call of expr * string * expr * expr (*List?*) 
  | CallVariant of expr * string * expr * expr * expr (*list?*) 
  | Revert
  | If of expr * expr * expr 
  | Return of expr
and arit_ops = 
  | Num of int
  | Plus of arit_ops * arit_ops 
  | Div of arit_ops * arit_ops 
  | Times of arit_ops * arit_ops
  | Minus of arit_ops * arit_ops 
  | Exp of arit_ops * arit_ops 
  | Mod of arit_ops * arit_ops 
and bool_ops =
  | Bool of b_val
  | Neg of b_val
  | Conj of b_val * b_val
  | Disj of b_val * b_val
  | Equals of bool_ops * bool_ops 
  | Greater of bool_ops * bool_ops 
  | GreaterOrEquals of bool_ops * bool_ops
  | Lesser of bool_ops * bool_ops
  | LessOrEquals of bool_ops * bool_ops
  | Inequals of bool_ops * bool_ops
  
type fun_def =
  | Name of string
  | RetType of t_exp
  | Args of t_exp * string (* list *)
  | Body of expr 

type contract_def = 
  | Name of string 
  | State of t_exp * string (* list *)
  | Constructor of t_exp * string (* list *) * expr 
  | Functions of fun_def (*list*)

let ct: (string, contract_def) Hashtbl.t = Hashtbl.create 64

(* let blockchain: ((values,values), (string, values(*state vars*),values)) Hashtbl.t = Hashtbl.create 64 *)

let rec eval_arit_expr (e: arit_ops) : arit_ops = match e with
  | Plus (e1, e2) -> begin match e1, e2 with
    | Num n1, Num n2 -> Num (n1 + n2)
    | Num n1, e2 -> eval_arit_expr (Plus(Num(n1), eval_arit_expr e2))
    | e1, e2 -> eval_arit_expr (Plus(eval_arit_expr e1, e2))
    end  
  | _ -> assert false

let rec eval_bool_expr (e: bool_ops) : bool_ops = match e with
  | Neg (b1) -> begin match b1 with 
    | False -> Bool(True)
    | True -> Bool(False)
    end
  | Conj (b1, b2) -> begin match b1, b2 with
    | False, _ -> Bool(False) 
    | _, False -> Bool(False)
    | True, True -> Bool(True)
    end  
  | Disj (b1, b2) -> begin match b1, b2 with
    | True, _ -> Bool(True)
    | _, True -> Bool(True)
    | False, False -> Bool(False) 
    end
  | _ -> assert false

let rec eval_expr (e: expr) : expr = match e with
	| Var(x) -> Var(x)
	| _ -> assert false





