(* BEFORE 0.5.0 there was no distinction between address and address payable!!!
 * *)
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
  | TRevert

type b_val =
  | True
  | False

type values =
  | VBool of b_val
  | VUInt of int
  | VAddress of string
  | VUnit
  | VContract of int
  | VMapping of (expr, expr) Hashtbl.t (* (values, values) ??? *)
  (*c.f*)
and arit_ops =
  | Plus of expr * expr
  | Div of expr * expr
  | Times of expr * expr
  | Minus of expr * expr
  | Exp of expr * expr
  | Mod of expr * expr

and bool_ops =
  | Neg of expr
  | Conj of expr * expr
  | Disj of expr * expr
  | Equals of expr * expr
  | Greater of expr * expr
  | GreaterOrEquals of expr * expr
  | Lesser of expr * expr
  | LesserOrEquals of expr * expr
  | Inequals of expr * expr

and expr =
  | AritOp of arit_ops
  | BoolOp of bool_ops
  | Var of string
  | Val of values
  | This of string option (*This ("") === This, else This.fname*)
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


type program =
  | Program of ((string, contract_def) Hashtbl.t * ((values * values), (string * (expr) StateVars.t * values)) Hashtbl.t * expr)

let rec eval_arit_expr (e: arit_ops) : expr = match e with
  | Plus (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> Val (VUInt(n1 + n2))
    | _ -> assert false
    end
  | Div (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> Val (VUInt (n1 / n2))
    | _ -> assert false
    end
  | Times (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> Val (VUInt (n1 * n2))
    | _ -> assert false
    end
  | Minus (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> Val (VUInt (n1 - n2))
    | _ -> assert false
    end
  | Exp (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> Val (VUInt ((float_of_int n1) ** (float_of_int n2) |> int_of_float))
    | _ -> assert false
    end
  | Mod (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> Val (VUInt (n1 mod n2))
    | _ -> assert false
    end

let rec eval_bool_expr (e: bool_ops) : expr = match e with
  | Neg b1 -> begin match b1 with
    | Val (VBool (True)) -> Val (VBool (False))
    | Val (VBool (False)) -> Val (VBool (True))
    | _ -> assert false
    end
  | Conj (e1, e2) -> begin match e1, e2 with
    | Val (VBool (True)), Val (VBool (True)) -> Val (VBool (True))
    | Val (VBool (True)),  Val (VBool (False)) -> Val (VBool (False))
    | Val (VBool (False)), Val (VBool (True)) -> Val (VBool (False))
    | Val (VBool (False)), Val (VBool (False)) -> Val (VBool (False))
    | _ -> assert false
    end
  | Disj (e1, e2) -> begin match e1, e2 with
    | Val (VBool (True)), Val (VBool (True)) -> Val (VBool (True))
    | Val (VBool (True)),  Val (VBool (False)) -> Val (VBool (True))
    | Val (VBool (False)), Val (VBool (True)) -> Val (VBool (True))
    | Val (VBool (False)), Val (VBool (False)) -> Val (VBool (False))
    | _ -> assert false
    end
  | Equals (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> if n1 = n2 then Val (VBool (True)) else Val (VBool (False))
    | _ -> assert false
    end
  | Greater (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> if n1 > n2 then Val (VBool (True)) else Val (VBool (False))
    | _ -> assert false
    end
  | GreaterOrEquals (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> if n1 >= n2 then Val (VBool (True)) else Val (VBool (False))
    | _ -> assert false
    end
  | Lesser (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> if n1 < n2 then Val (VBool (True)) else Val (VBool (False))
    | _ -> assert false
    end
  | LesserOrEquals (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> if n1 <= n2 then Val (VBool (True)) else Val (VBool (False))
    | _ -> assert false
    end
  | Inequals (e1, e2) -> begin match e1, e2 with
    | Val (VUInt n1), Val (VUInt n2) -> if n1 != n2 then Val (VBool (True)) else Val (VBool (False))
    | _ -> assert false
    end


(*

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

type blockchain = ((values * values), (string * (expr) StateVars.t * values)) Hashtbl.t

type conf = (blockchain * blockchain * values Stack.t * expr)

let rec eval_expr
  (ct: (string, contract_def) Hashtbl.t)
  (vars: (string, expr) Hashtbl.t)
  (conf: conf) : conf
   =
  let (blockchain, blockchain', sigma, e) = conf in
  let get_contract_by_address (blockchain: ((values * values), (string * (expr) StateVars.t * values)) Hashtbl.t ) (address: values) =
    Hashtbl.fold (fun (k1, k2) (_, _, _) acc -> if k2 = address then k1 else acc) blockchain VUnit
  in
  let get_address_by_contract (blockchain: ((values * values), (string * (expr) StateVars.t * values)) Hashtbl.t ) (contract: values) =
    Hashtbl.fold (fun (k1, k2) (_, _, _) acc -> if k1 = contract then k2 else acc) blockchain VUnit
  in
  match e with
    | AritOp a1 -> begin match a1 with
      | Plus (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Plus (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Plus (e1', e2)))
      end
      | Div (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
         eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Div (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Div (e1', e2)))
      end
      | Times (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Times (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Times (e1', e2)))
      end
      | Minus (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Minus (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Minus (e1', e2)))
      end
      | Exp (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Exp (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Exp (e1', e2)))
      end
      | Mod (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_arit_expr a1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Mod (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, AritOp(Mod (e1', e2)))
      end
    end
    | BoolOp b1 -> begin match b1 with
      | Neg e1 -> begin match e1 with
        | Val (VBool(_)) -> (blockchain, blockchain', sigma, eval_bool_expr b1)
        | _ -> eval_expr ct vars (eval_expr ct vars (blockchain, blockchain', sigma, e1))
      end
      | Conj (e1, e2) -> begin match e1, e2 with
        | Val (VBool(_)), Val (VBool(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
        | Val (VBool b), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Conj (Val (VBool b), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Conj (e1', e2)))
      end
      | Disj (e1, e2) -> begin match e1, e2 with
        | Val (VBool(_)), Val (VBool(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
        | Val (VBool b), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Disj (Val (VBool b), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Disj (e1', e2)))
      end
      | Equals (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Equals (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Equals (e1', e2)))
      end
      | Greater (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Greater (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Greater (e1', e2)))
      end
      | GreaterOrEquals (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(GreaterOrEquals (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(GreaterOrEquals (e1', e2)))
      end
      | Lesser (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Lesser (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Lesser (e1', e2)))
      end
      | LesserOrEquals (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(LesserOrEquals (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(LesserOrEquals (e1', e2)))
        end
      | Inequals (e1, e2) -> begin match e1, e2 with
        | Val (VUInt(_)), Val (VUInt(_)) ->  (blockchain, blockchain', sigma, eval_bool_expr b1)
        | Val (VUInt i), e2 -> let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Inequals (Val (VUInt i), e2')))
        | e1, e2 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
          eval_expr ct vars (blockchain, blockchain', sigma, BoolOp(Inequals (e1', e2)))      
        end
      end
    | Var(x) -> (blockchain, blockchain', sigma, Hashtbl.find vars x)
    | Val e1 -> (blockchain, blockchain', sigma, Val e1)
    | This None -> (blockchain, blockchain', sigma, Hashtbl.find vars "this")
    | This (Some s) -> (blockchain, blockchain', sigma, Val(VAddress("0x23213")))
    | MsgSender -> (blockchain, blockchain', sigma, Hashtbl.find vars "msg.sender")
    | MsgValue -> (blockchain, blockchain', sigma, Hashtbl.find vars "msg.value")
    | Balance e1 -> begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VAddress(a))) ->
        let c =  get_contract_by_address blockchain (VAddress(a)) in
        let (_, _, v) = Hashtbl.find blockchain (c, VAddress(a)) in
        (blockchain, blockchain', sigma, Val(v))
      | _ -> assert false
      end
    | Address e1 ->  begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VContract(c))) ->
        let a =  get_address_by_contract blockchain (VContract(c)) in
        (blockchain, blockchain', sigma, Val(a))
      | _ -> assert false
      end
    | StateRead (e1, s) ->  begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VContract(c))) ->
        let a = get_address_by_contract blockchain (VContract(c)) in
        let (_, sv, _) = Hashtbl.find blockchain (VContract(c),a) in
        (blockchain, blockchain', sigma, StateVars.find s sv)
      | _ -> assert false
      end
    | Transfer (e1, e2) -> assert false
    | New (s, e1, le) -> assert false
    | Cons (s, e1) -> assert false
    | Seq (e1, e2) -> assert false
    | Let(_, x, e1, e2) ->
      if Hashtbl.mem vars x then (blockchain, blockchain', sigma, Revert) else (* verify if x está em vars, modificação à tese do pirro*)
      let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
      Hashtbl.add vars x e1' ; eval_expr ct vars (blockchain, blockchain', sigma, e2)
    | Assign (x, e1) -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
      Hashtbl.add vars x e1' ; (blockchain, blockchain', sigma, Val(VUnit))
    | If (e1, e2, e3) -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in
      begin match e1' with
      | Val (VBool b) -> begin match b with
        | True -> eval_expr ct vars conf
        | False -> eval_expr ct vars conf
        end
      | _ -> assert false
      end
    | Call (e1, s, e2, le) -> assert false
    | CallVariant (e1, s, e2, e3, le) -> assert false
    | Revert -> 
      (blockchain', blockchain', sigma, Revert)
    | StateAssign (e1, s , e2) ->
      begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
        | (_, _, _, Val(VContract(c))) ->
          let a = get_address_by_contract blockchain (VContract(c)) in
          let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
          let (c_name, map, n) = Hashtbl.find blockchain (VContract c, a) in
          let map' = StateVars.add s e2' map in
          Hashtbl.replace blockchain (VContract(c),a) (c_name, map', n);
          (blockchain, blockchain', sigma, e2')
        | _ -> assert false
      end
    | MapRead (e1, e2) -> begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VMapping(m))) ->
        let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
        (blockchain, blockchain', sigma, Hashtbl.find m e2')
      | _ -> assert false
      end
    | MapWrite (e1, e2, e3) -> begin match eval_expr ct vars (blockchain, blockchain', sigma, e1) with
      | (_, _, _, Val(VMapping(m))) ->
        let (_, _, _, e2') = eval_expr ct vars (blockchain, blockchain', sigma, e2) in
        let (_, _, _, e3') = eval_expr ct vars (blockchain, blockchain', sigma, e3) in
        Hashtbl.add m e2' e3' ; (blockchain, blockchain', sigma, Val(VUnit))
      | _ -> assert false
      end
    | Return e1 -> let (_, _, _, e1') = eval_expr ct vars (blockchain, blockchain', sigma, e1) in (blockchain, blockchain', sigma, e1')



let rec free_variables (e: expr) : FV.t =
  let rec union_list_set (lst: FV.t list) (set: FV.t): FV.t = match lst with
    | [] -> set
    | x :: xs -> union_list_set xs (FV.union set x)
  in
  match e with
  | AritOp a1 -> begin match a1 with
    | Plus (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | Div (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | Times (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | Minus (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | Exp (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | Mod (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
  end
  | BoolOp b1 -> begin match b1 with
    | Neg e1 -> free_variables e1
    | Conj (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | Disj (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | Equals (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | Greater (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | GreaterOrEquals (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | Lesser (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | LesserOrEquals (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
    | Inequals (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
  end
  | Val _ -> FV.empty
  | Var x -> FV.singleton x
  | This s -> FV.singleton "this"
  | MsgSender -> FV.singleton "msg.sender"
  | MsgValue -> FV.singleton "msg.value"
  | Balance e1 -> free_variables e1
  | Address e1 -> free_variables e1
  | StateRead (e1, _) ->  free_variables e1
  | Transfer (e1, e2) -> FV.union (free_variables e1) (free_variables e2)
  | New (_, e1, le) -> let set_list = List.map free_variables le in
    FV.union (free_variables e1) (union_list_set set_list FV.empty)
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



let rec free_addr_names (e: expr) : FN.t =
  let rec union_list_set (lst: FN.t list) (set: FN.t): FN.t = match lst with
    | [] -> set
    | x :: xs -> union_list_set xs (FN.union set x)
  in
  match e with
  | AritOp a1 -> begin match a1 with
    | Plus (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | Div (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | Times (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | Minus (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | Exp (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | Mod (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  end
  | BoolOp b1 -> begin match b1 with
    | Neg e1 -> free_variables e1
    | Conj (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | Disj (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | Equals (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | Greater (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | GreaterOrEquals (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | Lesser (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | LesserOrEquals (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
    | Inequals (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  end
  | Val (VAddress a) -> FN.singleton a
  | Val (VContract c) -> FN.empty
  | Val _ -> FN.empty
  | This s -> FN.empty
  | Var x -> FN.empty
  | MsgSender -> FN.empty
  | MsgValue -> FN.empty
  | Address e1 -> free_addr_names e1
  | Balance e1 -> free_addr_names e1
  | StateRead (e1, _) -> free_addr_names e1
  | Transfer (e1, e2) -> FN.union (free_addr_names e1) (free_addr_names e2)
  | New (_, e1, le) -> let set_list = List.map free_addr_names le in
    FN.union (free_addr_names e1) (union_list_set set_list FV.empty)
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
  (* | _ -> assert false *)


let rec substitute (e: expr) (e': expr) (x: string) : expr =
  let f lst = substitute lst e' x in
  match e with
  | AritOp a1 -> begin match a1 with
    | Plus (e1, e2) -> AritOp (Plus (substitute e1 e' x, substitute e2 e' x))
    | Div (e1, e2) ->  AritOp (Div (substitute e1 e' x, substitute e2 e' x))
    | Times (e1, e2) -> AritOp (Times (substitute e1 e' x, substitute e2 e' x))
    | Minus (e1, e2) ->  AritOp (Minus (substitute e1 e' x, substitute e2 e' x))
    | Exp (e1, e2) ->  AritOp (Exp (substitute e1 e' x, substitute e2 e' x))
    | Mod (e1, e2) ->  AritOp (Mod (substitute e1 e' x, substitute e2 e' x))
  end
  | BoolOp b1 -> begin match b1 with
      | Neg e1 -> BoolOp (Neg (substitute e1 e' x))
      | Conj (e1, e2) -> BoolOp(Conj (substitute e1 e' x, substitute e2 e' x))
      | Disj (e1, e2) -> BoolOp(Disj (substitute e1 e' x, substitute e2 e' x))
      | Equals (e1, e2) -> BoolOp(Equals (substitute e1 e' x, substitute e2 e' x))
      | Greater (e1, e2) -> BoolOp(Greater (substitute e1 e' x, substitute e2 e' x))
      | GreaterOrEquals (e1, e2) -> BoolOp(GreaterOrEquals (substitute e1 e' x, substitute e2 e' x))
      | Lesser (e1, e2) -> BoolOp(Lesser (substitute e1 e' x, substitute e2 e' x))
      | LesserOrEquals (e1, e2) -> BoolOp(LesserOrEquals (substitute e1 e' x, substitute e2 e' x))
      | Inequals (e1, e2) -> BoolOp(Inequals (substitute e1 e' x, substitute e2 e' x))
  end
  | Var y -> if x = y then e' else e
  | Val _ -> e
  | This s -> if x = "this" then e' else e
  | MsgSender -> e
  | MsgValue -> e
  | Balance e1 -> Balance (substitute e1 e' x)
  | Address e1 -> Address (substitute e1 e' x)
  | StateRead (e1, s) -> StateRead (substitute e1 e' x, s)
  | Transfer (e1, e2) -> Transfer (substitute e1 e' x, substitute e2 e' x)
  | New (s, e1, le) -> New (s, substitute e1 e' x, List.map f le)
  | Seq (e1, e2) -> Seq (substitute e1 e' x, substitute e2 e' x)
  | Let (t_e, s, e1, e2) -> Let (t_e, s, substitute e1 e' x, substitute e2 e' x)
  | Assign (y, e1) -> Assign (y, substitute e1 e' x)
  | MapRead (e1, e2) -> MapRead (substitute e1 e' x, substitute e2 e' x)
  | MapWrite (e1, e2, e3) -> MapWrite (substitute e1 e' x, substitute e2 e' x, substitute e3 e' x)
  | If (e1, e2, e3) -> If (substitute e1 e' x, substitute e2 e' x, substitute e3 e' x)
  | Call (e1, s, e2, le) -> Call (substitute e1 e' x, s, substitute e2 e' x, List.map f le)
  | CallVariant (e1, s, e2, e3, le) ->  CallVariant (substitute e1 e' x, s, substitute e2 e' x, substitute e3 e' x, List.map f le)
  | Cons (s, e1) -> Cons (s, substitute e1 e' x)
  | Revert -> e
  | Return e1 -> Return e1
  | _ -> assert false

  (* Blockchain maps cases? *)

(*sv*)
let state_vars_contract (contract_name: string) (ct: (string, contract_def) Hashtbl.t) : (t_exp * string) list =
  let contract : contract_def = Hashtbl.find ct contract_name in contract.state


let function_body
  (contract_name: string)
  (function_name: string)
  (values: expr list)
  (ct: (string, contract_def) Hashtbl.t) :
  ((t_exp * string) list) * expr =
    let contract : contract_def = Hashtbl.find ct contract_name in
    let functions_def : fun_def list = contract.functions in
    try
      let f = List.find (fun (x : fun_def) -> x.name = function_name) (functions_def) in
      if List.length values = List.length f.args then (f.args, f.body) else ([], Return (Revert))
    with Not_found -> ([], Return (Revert))


let function_type (contract_name: string) (function_name: string) (ct: (string, contract_def) Hashtbl.t) : (t_exp list * t_exp) =
  let contract : contract_def = Hashtbl.find ct contract_name in
  let functions_def : fun_def list = contract.functions in
  try
    let f = List.find (fun (x : fun_def) -> x.name = function_name) (functions_def) in 
    let t_es = List.map (fun (t_e, _) -> t_e) f.args in
    (t_es, f.rettype)
  with Not_found -> ([], TRevert) (* maybe remove? *)

  (*uptbal(β, a, n)*)
let update_balance
  (ct: (string, contract_def) Hashtbl.t)
  (blockchain: ((values * values), (string * (expr) StateVars.t * values)) Hashtbl.t)
  (address: values)
  (value: values)
  (vars: (string, expr) Hashtbl.t)
  (conf: conf) : unit =
    let (blockchain, blockchain', sigma, _) = conf in
    let get_contract_by_address (blockchain: ((values * values), (string * (expr) StateVars.t * values)) Hashtbl.t ) (address: values) =
    Hashtbl.fold (fun (k1, k2) (_, _, _) acc -> if k2 = address then k1 else acc) blockchain VUnit
    in
    let contract = get_contract_by_address blockchain address in
    let (c, sv, old_balance) = Hashtbl.find blockchain (contract, address) in
    match eval_expr ct vars (blockchain, blockchain', sigma, (AritOp (Plus (Val(old_balance), Val(value))))) with 
      | (_, _, _, Val new_balance) -> Hashtbl.replace blockchain (contract, address) (c, sv, new_balance)
      | _ -> assert false
    

(*Top(σ)*)
(*if sigma = sigma' * a' then a' else if sigma = blockchain then Val(VUnit) *)

let top
 (conf: conf) : values =
 let (blockchain, blockchain', sigma, _) = conf in
  try
    Stack.top sigma
  with Stack.Empty -> VUnit

let bank_contract unit : contract_def =
  let deposit = {
    name = "deposit";
    rettype = Unit;
    args = [];
    body = Return(
      (StateAssign(
        This None,
        "balances",
        MapWrite(
          StateRead(This None,"balances"), MsgSender, AritOp((Plus(MapRead(StateRead(This None,"balances"),MsgSender), MsgValue)))))))
  } in
  let getBalance = {
    name = "getBalance";
    rettype = UInt;
    args = [];
    body = MapRead(StateRead(This None,"balances"),MsgSender)
  } in
  let transfer = {
    name = "transfer";
    rettype = Unit;
    args = [(Address, "to"); (UInt, "amount")];
    body = If(BoolOp(GreaterOrEquals(MapRead(StateRead(This None,"balances"),MsgSender),Var("amount"))),
          Seq(StateAssign(This None, "balances", MapWrite(
            StateRead(This None,"balances"), MsgSender, AritOp(Minus(MapRead(StateRead(This None,"balances"),MsgSender), Var("amount"))))),
              StateAssign(This None, "balances", MapWrite(
            StateRead(This None,"balances"), Var("to"), AritOp(Minus(MapRead(StateRead(This None,"balances"),Var("to")), Var("amount")))))
            ),
          Val(VUnit))
  } in
  let withdraw = {
    name = "withdraw";
    rettype = Unit;
    args = [(UInt, "amount")];
    body = If(BoolOp(GreaterOrEquals(MapRead(StateRead(This None,"balances"),MsgSender),Var("amount"))),
            Seq(
              StateAssign(This None, "balances", MapWrite(
              StateRead(This None,"balances"), MsgSender, AritOp(Minus(MapRead(StateRead(This None,"balances"),MsgSender), Var("amount"))))),
              Transfer(MsgSender, Var("x"))
              ),
            Val(VUnit)
    )
  } in
  {
    name = "Bank";
    state = [(Map(Address, UInt),"balances")];
    constructor = ([(Map(Address, UInt),"balances")], Return (StateAssign(This None, "balances", Var("balances"))));
    functions = [deposit; getBalance; transfer; withdraw];
  }


let blood_bank_contract unit : contract_def =
let setHealth = {
  name = "setHealth";
  rettype = Unit;
  args = [(Address, "donor"); (Bool, "isHealty")];
  body = Return (
    If(BoolOp(Equals(MsgSender, StateRead(This None, "doctor"))),
      (StateAssign(
      This None,
      "healty",
      MapWrite(
        StateRead(This None,"healty"), Var("donor"), Var("isHealty")))),
      Revert
    )
  );
} in
let isHealty = {
  name = "isHealty";
  rettype = Bool;
  args = [(Address, "donor")];
  body = Return(
    If(BoolOp(Equals(MsgSender, StateRead(This None, "doctor"))),
      MapRead(StateRead(This None, "healty"), Var("donor")),
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
    Let(UInt, "donorBlood",Call(Val(VContract(1)),"getBlood",Val(VUInt(0)),[]),
    If(BoolOp(Conj(MapRead(StateRead(This None, "healty"), MsgSender), BoolOp(Conj(
      BoolOp(Greater(Var("donorBlood"),Val(VUInt(3000)))), BoolOp(Greater(
        AritOp(Minus(Var("donorBlood"), Var("amount"))), Val(VUInt(0)))))))),
      StateAssign(This None, "blood", AritOp(Plus(StateRead(This None, "blood"), Var("amount")))),
      Val(VUnit)
  )));
} in
let getDoctor = {
  name = "getDoctor";
  rettype = Address;
  args = [];
  body = Return(StateRead(This None, "doctor"));
} in
let getBlood = {
  name = "getBlood";
  rettype = UInt;
  args = [];
  body = Return(StateRead(This None, "blood"));
} in
{
  name = "BloodBank";
  state = [(Map(Address, Bool), "healty"); (Address, "doctor"); (UInt, "blood")];
  constructor = ([(Map(Address, Bool), "healty"); (Address, "doctor"); (UInt, "blood")], Return
        (Seq((StateAssign(This None, "healty", Var("healty")),
          Seq((StateAssign(This None, "doctor", Var("doctor"))),
               StateAssign(This None, "blood", Var("blood"))))
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
  body = Return(StateRead(This None, "bank"));
} in
let getBlood = {
  name = "getBlood";
  rettype = UInt;
  args = [];
  body = Return(StateRead(This None, "blood"));
} in
{
  name = "Donor";
  state = [(UInt, "blood"); (Address, "bank")];
  constructor = ([(UInt, "blood"); (Address,"bank")], Return (Seq(
    StateAssign(This None, "blood", Var("blood")),
    StateAssign(This None, "bank", Var("bank"))
  )));
  functions = [donate; getBank; getBlood];
}

let rec t_exp_to_string (t_e: t_exp) : string = match t_e with
  | C s -> "contract(" ^ s ^ ")"
  | Bool -> "boolean"
  | Unit -> "unit"
  | UInt -> "uint"
  | Address -> "address"
  | Map (t_e1, t_e2)-> "mapping(" ^ t_exp_to_string t_e1 ^ " => " ^ t_exp_to_string t_e2 ^ ")"

let rec print_tuples lst =
  begin match lst with
    | [] -> ()
    | (t_e, s) :: rest ->
      let s1 = t_exp_to_string t_e in
      Printf.printf "%s : %s;\n" s1 s;
      print_tuples rest
  end


let () =
  (* let x: int = 10 ; x + x ;*)
  (* let e1 = (AritOp(Plus(Num(1),Times(Num(2),Num(3))))) in
  Format.eprintf "%s\n" (arit_op_to_string e1); *)
  let ct: (string, contract_def) Hashtbl.t = Hashtbl.create 64 in
  let blockchain: blockchain = Hashtbl.create 64 in
  let sigma: values Stack.t = Stack.create() in
  let conf: conf = (blockchain, blockchain, sigma, Val(VUInt(0))) in
  let vars: (string, expr) Hashtbl.t = Hashtbl.create 64 in
  let p = Program(ct, blockchain, Val(VUInt(0))) in

  let print_set s = FV.iter print_endline s in
  let e2 = New("BloodBank", Val(VUInt(0)),[StateRead(This None, "blood"); MsgSender;Val (VAddress("0x01232"));Val (VAddress("0x012dsadsadsadsa3"))]) in
  let lst = free_addr_names e2 in
  print_set lst;
  let e1 = BoolOp(Inequals((AritOp(Plus(Val (VUInt(1)),AritOp(Plus(Val(VUInt(10)),(Val(VUInt(2)))))))),Val(VUInt(20)))) in
  let (_, _, _, Val(VBool(b))) = eval_expr ct vars (blockchain, blockchain, sigma, e1) in
  match b with 
    | True -> Format.eprintf "True";
    | False -> Format.eprintf "False";
  (* Format.eprintf "%d\n" i; *)
  Hashtbl.add ct "Bank" (bank_contract());
  Hashtbl.add ct "BloodBank" (blood_bank_contract());
  Hashtbl.add ct "Donor" (donor_contract());
  let res = state_vars_contract "Bank" ct in
  let res2 = state_vars_contract "BloodBank" ct in
  let res3 = state_vars_contract "Donor" ct in
  (* let res4 = state_vars_contract "Error" ct in  *)
  print_tuples res;
  print_tuples res2;
  print_tuples res3;
  (* print_tuples res4; *)
  let (res1, _) = function_body "Bank" "transfer" [Val(VUInt(1));Val(VUInt(1))] ct in
  print_tuples res1;
  let res = function_type "Bank" "transfer" ct in
  (* print_tuples [(res, "transfer fun return_type")]; *)
  let res = function_type "BloodBank" "isHealty" ct in
  ()
  (* print_tuples [(res, "isHealty fun return_type")] *)




  (* match e2 with
    | Val (VUInt(i)) -> Format.eprintf "%s\n" (Stdlib.string_of_int i);
    | _ -> assert false *)
