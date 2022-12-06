(* BEFORE 0.5.0 there was no distinction between address and address payable!!! *)
(* msg.sender.transfer(x) to payable(msg.sender).transfer(x) *)
module FV = Set.Make(String)
module FN = Set.Make(String)
module StateVars = Map.Make(String)

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
  | VMapping 
  (*c.f*)

type arit_ops = 
  | Num of int
  | Plus of expr * expr 
  | Div of expr * expr 
  | Times of expr * expr
  | Minus of expr * expr 
  | Exp of expr * expr 
  | Mod of expr * expr 

and bool_ops =
  | Bool of b_val
  | Neg of expr
  | Conj of expr * expr
  | Disj of expr * expr
  | Equals of expr * expr 
  | Greater of expr * expr 
  | GreaterOrEquals of expr * expr
  | Lesser of expr * expr
  | LessOrEquals of expr * expr
  | Inequals of expr * expr

and expr =
  | AritOp of arit_ops
  | BoolOp of bool_ops
  | Var of string
  | Val of values
  | This 
  | MsgSender 
  | MsgValue 
  | Balance of expr
  | Address of expr 
  | StateRead of expr * string
  | Transfer of expr * expr
  | New of string * expr * expr list
  | Cons of string * expr 
  | Seq of expr * expr
  | Let of t_exp *  string * expr * expr (* EM SOLIDITY NÃO EXISTE *) 
  | Assign of string * expr
  | StateAssign of expr * string * expr
  | MapRead of expr * expr 
  | MapWrite of expr * expr * expr
  | Call of expr * string * expr * expr list (* e.f.value(e)(le) *)
  | CallVariant of expr * string * expr * expr * expr list (* e.f.value(e).sender(e)(le) *)
  | Revert
  | If of expr * expr * expr 
  | Return of expr
  
  
type fun_def = {
  name : string;
  rettype : t_exp;
  args : (t_exp * string) list;
  body : expr;
}

type contract_def = {
  name : string;
  state : (t_exp * string) list;
  constructor : (t_exp * string) list * expr;
  functions : fun_def list;
}

let ct: (string, contract_def) Hashtbl.t = Hashtbl.create 64

let blockchain: ((values * values), (string * (expr) StateVars.t * values)) Hashtbl.t = Hashtbl.create 64

type program = ((string, contract_def) Hashtbl.t * ((values * values), (string * (expr) StateVars.t * values)) Hashtbl.t * expr)

(* let rec eval_arit_expr (e: arit_ops) : arit_ops = match e with
  | Plus (e1, e2) -> begin match e1, e2 with
    | Num n1, Num n2 -> Num (n1 + n2)
    | Num n1, e2 -> eval_arit_expr (Plus(Num(n1), eval_arit_expr e2))
    | e1, e2 -> eval_arit_expr (Plus(eval_arit_expr e1, e2))
    end  
  | _ -> assert false

let rec eval_bool_expr (e: bool_ops) : bool_ops = match e with
  | Neg (b1) -> begin match b1 with 
    | Bool(False) -> Bool(True)
    | Bool(True) -> Bool(False)
    end
  | Conj (b1, b2) -> begin match b1, b2 with
    | Bool(False), _ -> Bool(False) 
    | _, Bool(False) -> Bool(False)
    | Bool(True), Bool(True) -> Bool(True)
    end  
  | Disj (b1, b2) -> begin match b1, b2 with
    | Bool(True), _ -> Bool(True)
    | _, Bool(True) -> Bool(True)
    | Bool(False), Bool(False) -> Bool(False) 
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
  | _ -> assert false *)

let rec eval_expr (e: expr) (vars: (string, expr) Hashtbl.t): expr = match e with
  | AritOp e1 -> Val(VUInt(0))
  | BoolOp e1 -> Val(VUInt(0))
  | Var(x) -> Hashtbl.find vars x
  | Val e1 -> Val e1
  | This -> Val(VAddress("0x23213"))
  | MsgSender -> Val(VAddress("0x23213"))
  | MsgValue -> Val(VUInt(1000))
  | _ -> assert false

let rec free_variables (e: expr) : FV.t = match e with 
  | AritOp e1 -> FV.empty
  | BoolOp e1 -> FV.empty
  | Val _ -> FV.empty
  | Var x -> FV.singleton x
  | This -> FV.singleton "this"
  | MsgSender -> FV.singleton "msg.sender"
  | MsgValue -> FV.singleton "msg.value"
  | Balance e1 -> free_variables e1 
  | Address e1 -> free_variables e1 
  | StateRead (e1, _) ->  free_variables e1 
  | Transfer (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
  | New (_, e1, le) -> begin let rec aux_fun set lst = match lst with 
    | [] -> set
    | x :: xs -> let fvsx = free_variables x in aux_fun (FV.union set fvsx) xs 
    in aux_fun FV.empty le
    end 
  (* | New (_, le) -> List.map  *)
  | Cons (_, e1) -> free_variables e1
  | Seq (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
  | Let(_, x, e1, e2) -> FV.union (free_variables e1) ((FV.filter (fun (x') -> x <> x') (free_variables e2)))
  | Assign (x, e1) -> FV.union (FV.singleton x) (free_variables e1)
  | If (e1, e2, e3) -> FV.union (free_variables e1) (FV.union (free_variables e2) (free_variables e3))
  | Call (e1, _, e2, le) -> FV.union (free_variables e1) (free_variables e2)
  | CallVariant (e1, _, e2, e3, le) -> FV.union (free_variables e1) (FV.union (free_variables e2) (free_variables e3))
  | Revert -> FV.empty
  | StateAssign (e1, _ , e2) -> FV.union (free_variables e1) (free_variables e2)
  | MapRead (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
  | MapWrite (e1, e2, e3) -> FV.union (free_variables e1) (FV.union (free_variables e2) (free_variables e3))
  | Return e1 -> free_variables e1



let rec free_addr_names (e: expr) : FN.t = match e with 
  | AritOp e1 -> FV.empty 
  | BoolOp e1 -> FV.empty
  | Val (VAddress(a)) -> FN.singleton a 
  | Val (VContract(c)) -> FN.singleton c
  | Val _ -> FN.empty 
  | This -> FN.empty 
  | Var x -> FN.empty 
  | MsgSender -> FN.empty 
  | MsgValue -> FN.empty 
  | Address e1 -> free_addr_names e1 
  | Balance e1 -> free_addr_names e1
  | StateRead (e1, _) -> free_addr_names e1 
  | Transfer (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | New (_, e1, le) -> begin let rec aux_fun set lst = match lst with 
    | [] -> set
    | x :: xs -> let fnsx = free_addr_names x in aux_fun (FN.union set fnsx) xs 
    in aux_fun FN.empty le
    end 
  | Cons (_, e1) -> free_addr_names e1
  | Seq (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | Let(_, _, e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | Assign (_, e1) -> free_variables e1
  | If (e1, e2, e3) -> FN.union (free_addr_names e1) (FV.union (free_addr_names e2) (free_addr_names e3))
  | Call (e1, _, e2, le) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | CallVariant (e1, _, e2, e3, le) ->  FN.union (free_addr_names e1) (FV.union (free_addr_names e2) (free_addr_names e3))
  | Revert -> FN.empty
  | StateAssign (e1, _ , e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | MapRead (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | MapWrite (e1, e2, e3) -> FN.union (free_addr_names e1) (FV.union (free_addr_names e2) (free_addr_names e3))
  | Return e1 -> free_addr_names e1

  
let rec substitute (e: expr) (e': expr) (x: string) : expr = match e with 
  | AritOp a1 -> begin match a1 with
    | Num i -> AritOp (Num i)
    | Plus (e1, e2) -> AritOp (Plus (substitute e1 e' x, substitute e2 e' x)) 
    | Div (e1, e2) ->  AritOp (Div (substitute e1 e' x, substitute e2 e' x))
    | Times (e1, e2) -> AritOp (Times (substitute e1 e' x, substitute e2 e' x))
    | Minus (e1, e2) ->  AritOp (Minus (substitute e1 e' x, substitute e2 e' x))
    | Exp (e1, e2) ->  AritOp (Exp (substitute e1 e' x, substitute e2 e' x))
    | Mod (e1, e2) ->  AritOp (Mod (substitute e1 e' x, substitute e2 e' x))
  end
  | BoolOp b1 -> begin match b1 with 
    | _ -> assert false
  end 
  | Var y -> if x = y then e' else e
  | Val _ -> e
  | This -> if x = "this" then e' else e 
  | MsgSender -> e
  | MsgValue -> e 
  | Balance e1 -> Balance (substitute e1 e' x)
  | Address e1 -> Address (substitute e1 e' x)
  | StateRead (e1, s) -> StateRead (substitute e1 e' x, s)
  | Transfer (e1, e2) -> Transfer (substitute e1 e' x, substitute e2 e' x)
  | Let (t_e, s, e1, e2) -> assert false 
  | Assign (y, e1) -> Assign (y, substitute e1 e' x)
  | MapRead (e1, e2) -> MapRead (substitute e1 e' x, substitute e2 e' x)
  | MapWrite (e1, e2, e3) -> MapWrite (substitute e1 e' x, substitute e2 e' x, substitute e3 e' x)
  | If (e1, e2, e3) -> If (substitute e1 e' x, substitute e2 e' x, substitute e3 e' x)
  | Seq (e1, e2) -> Seq (substitute e1 e' x, substitute e2 e' x)
  | New (s, e1, le) -> assert false
  | Cons (s, e1) -> Cons (s, substitute e1 e' x)
  | Revert -> e 
  | Return e1 -> Return e1
  | _ -> assert false

  (* Blockchain maps cases? *)

let bank_contract unit : contract_def = 
  let deposit = {
    name = "deposit";
    rettype = Unit;
    args = [];
    body = Return(
      (StateAssign(
        This, 
        "balances", 
        MapWrite(
          StateRead(This,"balances"), MsgSender, AritOp((Plus(MapRead(StateRead(This,"balances"),MsgSender), MsgValue)))))))
  } in 
  let getBalance = {
    name = "getBalance";
    rettype = UInt;
    args = [];
    body = MapRead(StateRead(This,"balances"),MsgSender)
  } in 
  let transfer = {
    name = "transfer";
    rettype = Unit;
    args = [(Address, "to"); (UInt, "amount")];
    body = If(BoolOp(GreaterOrEquals(MapRead(StateRead(This,"balances"),MsgSender),Var("amount"))), 
          Seq(StateAssign(This, "balances", MapWrite(
            StateRead(This,"balances"), MsgSender, AritOp(Minus(MapRead(StateRead(This,"balances"),MsgSender), Var("amount"))))),
              StateAssign(This, "balances", MapWrite(
            StateRead(This,"balances"), Var("to"), AritOp(Minus(MapRead(StateRead(This,"balances"),Var("to")), Var("amount")))))
            ),
          Val(VUnit))
  } in 
  let withdraw = {
    name = "withdraw";
    rettype = Unit;
    args = [(UInt, "amount")];
    body = If(BoolOp(GreaterOrEquals(MapRead(StateRead(This,"balances"),MsgSender),Var("amount"))),
            Seq(
              StateAssign(This, "balances", MapWrite(
              StateRead(This,"balances"), MsgSender, AritOp(Minus(MapRead(StateRead(This,"balances"),MsgSender), Var("amount"))))),
              Transfer(MsgSender, Var("x"))
              ),
            Val(VUnit)
    )
  } in 
  {
    name = "Bank";
    state = [(Map(Address, UInt),"balances")];
    constructor = ([(Map(Address, UInt),"balances")], Return (StateAssign(This, "balances", Var("balances"))));
    functions = [deposit; getBalance; transfer; withdraw];
  }


let blood_bank_contract unit : contract_def =
let setHealth = {
  name = "setHealth";
  rettype = Unit;
  args = [(Address, "donor"); (Bool, "isHealty")];
  body = Return (
    If(BoolOp(Equals(MsgSender, StateRead(This, "doctor"))),
      (StateAssign(
      This, 
      "healty", 
      MapWrite(
        StateRead(This,"healty"), Var("donor"), Var("isHealty")))),
      Revert
    )
  );
} in 
let isHealty = {
  name = "setHealth";
  rettype = Unit;
  args = [(Address, "donor")];
  body = Return(
    If(BoolOp(Equals(MsgSender, StateRead(This, "doctor"))),
      MapRead(StateRead(This, "healty"), Var("donor")),
      Revert
    )
  );
} in
let donate = {
  (* |Call of expr * string * expr * expr list e.f.value(e)(le) *)
  name = "donate";
  rettype = Unit;
  args = [(UInt, "amount")];
  body = Return(
    Let(UInt, "donorBlood",Call(Val(VContract("asx")),"getBlood",Val(VUInt(0)),[]),
    If(BoolOp(Conj(MapRead(StateRead(This, "healty"), MsgSender), BoolOp(Conj(
      BoolOp(Greater(Var("donorBlood"),Val(VUInt(3000)))), BoolOp(Greater(
        AritOp(Minus(Var("donorBlood"), Var("amount"))), Val(VUInt(0)))))))),
      StateAssign(This, "blood", AritOp(Plus(StateRead(This, "blood"), Var("amount")))),
      Val(VUnit)
  )));
} in
let getDoctor = {
  name = "getDoctor";
  rettype = Address;
  args = [];
  body = Return(StateRead(This, "doctor"));
} in
let getBlood = {
  name = "getBlood";
  rettype = UInt;
  args = [];
  body = Return(StateRead(This, "blood"));
} in
{
  name = "BloodBank";
  state = [(Map(Address, Bool), "healty"); (Address, "doctor"); (UInt, "blood")];
  constructor = ([(Map(Address, Bool), "healty"); (Address, "doctor"); (UInt, "blood")], Return 
        (Seq((StateAssign(This, "healty", Var("healty")),
          Seq((StateAssign(This, "doctor", Var("doctor"))),
               StateAssign(This, "blood", Var("blood"))))
  )));
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
  body = Return(StateRead(This, "bank"));
} in
let getBlood = {
  name = "getBlood";
  rettype = UInt;
  args = [];
  body = Return(StateRead(This, "blood"));
} in
{
  name = "Donor";
  state = [(UInt, "blood"); (Address, "bank")];
  constructor = ([(UInt, "blood"); (Address,"bank")], Return (Seq(
    StateAssign(This, "blood", Var("blood")),
    StateAssign(This, "bank", Var("bank"))
  )));
  functions = [donate; getBank; getBlood];
}

let () =
  (* let x: int = 10 ; x + x ;*)
  (* let e1 = (AritOp(Plus(Num(1),Times(Num(2),Num(3))))) in
  Format.eprintf "%s\n" (arit_op_to_string e1); *)
  let print_set s = FV.iter print_endline s in
  let e2 = New("BloodBank", Val(VUInt(0)),[StateRead(This, "blood"); MsgSender;Val (VAddress("0x01232"))]) in
  let lst = free_addr_names e2 in 
  print_set lst;






