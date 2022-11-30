(* BEFORE 0.5.0 there was no distinction between address and address payable!!! *)
(* msg.sender.transfer(x) to payable(msg.sender).transfer(x) *)
module FV = Set.Make(String)
module FN = Set.Make(String)

type t_exp = 
  | C of string (* * hash_contract_code? *)
  | Bool
  | Unit 
  | UInt 
  | Address
  | Map of t_exp * t_exp

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
  | New of string * expr list
  | Cons of string * expr 
  | Seq of expr * expr
  | Let of t_exp *  string * expr * expr (* EM SOLIDITY NÃO EXISTE *)
  | Assign of string * expr
  | StateAssign of expr * string * expr
  | MapRead of expr * expr 
  | MapWrite of expr * expr * expr
  | Call of expr * string * expr * expr list
  | CallVariant of expr * string * expr * expr * expr list
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
  
type fun_def = {
  name : string;
  rettype : t_exp;
  args : (t_exp * string) list;
  body : expr
}

type contract_def = {
  name : string;
  state : (t_exp * string) list;
  constructor : (t_exp * string) list * expr;
  functions : fun_def list;
}

let ct: (string, contract_def) Hashtbl.t = Hashtbl.create 64

let blockchain: ((values * values), (string * values(*state vars*) * values)) Hashtbl.t = Hashtbl.create 64

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

let from_arit_ops_to_expr (e: arit_ops) : expr = match e with 
  | Num (i) -> Val(VUInt(i))
  | _ -> assert false 

let from_bool_ops_to_expr (e: bool_ops) : expr = match e with
  | Bool (bval) -> Val(VBool(bval))
  | _ -> assert false

let from_expr_to_arit_ops (e: expr) : arit_ops = match e with
  | Val (VUInt(i)) -> Num (i)
  | _ -> assert false

let from_expr_to_bool_ops (e: expr) : bool_ops = match e with
  | Val (VBool(bval)) -> Bool (bval)
  | _ -> assert false


let rec eval_expr (e: expr) : expr = match e with
	| Var(x) -> Var(x)
	| _ -> assert false

let rec expr_to_string (e: expr) : string = match e with
  | _ -> assert false

let rec arit_op_to_string (e: arit_ops) : string = match e with
  | Num n -> Stdlib.string_of_int n
  | Plus (e1, e2) -> "(" ^ arit_op_to_string e1 ^ " + " ^ arit_op_to_string e2 ^ ")"
  | Times (e1, e2) -> "(" ^ arit_op_to_string e1 ^ " * " ^ arit_op_to_string e2 ^ ")"
  | _ -> assert false

let rec bool_op_to_string (e: bool_ops) : string = match e with
  | Bool(True) -> "true"
  | Bool(False) -> "false"
  | _ -> assert false


let bank_contract unit : contract_def = 
  let deposit = {
    name = "deposit";
    rettype = Unit;
    args = [];
    body = Val(VUnit)
  } in 
  let getBalance = {
    name = "getBalance";
    rettype = UInt;
    args = [];
    body = Val(VUnit)
  } in 
  let transfer = {
    name = "transfer";
    rettype = Unit;
    args = [(Address, "to"); (UInt, "amount")];
    body = Val(VUnit)
  } in 
  let withdraw = {
    name = "withdraw";
    rettype = Unit;
    args = [(UInt, "amount")];
    body = Val(VUnit)
  } in 
  {
    name = "Bank";
    state = [(Map(Address, UInt),"balances")];
    constructor = ([(Map(Address, UInt),"balances")], Return (StateAssign(This, "balances", Val(VUInt(1)))));
    functions = [deposit; getBalance; transfer; withdraw];
  }

let blood_bank_contract unit : contract_def =
let setHealth = {
  name = "setHealth";
  rettype = Unit;
  args = [(Address, "donor"); (Bool, "isHealty")];
  body = Val(VUnit);
} in 
let isHealty = {
  name = "setHealth";
  rettype = Unit;
  args = [(Address, "donor")];
  body = Val(VUnit);
} in
let donate = {
  name = "donate";
  rettype = Unit;
  args = [(UInt, "amount")];
  body = Val(VUnit);
} in
let getDoctor = {
  name = "getDoctor";
  rettype = Address;
  args = [];
  body = Val(VUnit);
} in
let getBlood = {
  name = "getBlood";
  rettype = UInt;
  args = [];
  body = Val(VUnit);
} in
{
  name = "BloodBank";
  state = [(Map(Address, Bool), "healty"); (Address, "doctor"); (UInt, "blood")];
  constructor = ([], Return (Val(VUnit)));
  functions = [setHealth; isHealty; donate; getDoctor; getBlood];
}


let donor_contract unit : contract_def = 
let donate = {
  name = "donate";
  rettype = Unit;
  args = [(UInt, "amount")];
  body = Val(VUnit);
} in
let getBank = {
  name = "getBank";
  rettype = C("BloodBank");
  args = [];
  body = Val(VUnit);
} in
let getBlood = {
  name = "getBlood";
  rettype = UInt;
  args = [];
  body = Val(VUnit);
} in
{
  name = "Donor";
  state = [(UInt, "blood"); (Address, "bank")];
  constructor = ([], Return (Val(VUnit)));
  functions = [donate; getBank; getBlood];
}

let () =
  let e1 = (Plus(Num(1),Times(Num(2),Num(3)))) in
  Format.eprintf "%s\n" (arit_op_to_string e1);



