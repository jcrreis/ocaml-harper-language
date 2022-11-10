type aexp =
 | Num of int
 | Var of string
 | Plus of aexp * aexp
 | Times of aexp * aexp
 | Minus of aexp * aexp

type bexp =
 | True 
 | False 
 | Neg of bexp
 | Equals of aexp * aexp
 | LessOrEqual of aexp * aexp
 | Conj of bexp * bexp
  
type stm =
 | Assign of string * aexp
 | Skip
 | Seq of stm * stm
 | If of bexp * stm * stm
 | While of bexp * stm

type expr =
 | Aexp of aexp
 | Bexp of bexp
 | Stm of stm

let rec eval_arit (e: aexp) (tbl: (string, aexp) Hashtbl.t) : aexp = match e with
	| Num (n) -> Num (n)
	| Var (x) -> Hashtbl.find tbl x 
	| Plus (Num n1, Num n2) -> Num (n1 + n2)
	| Plus (Num n1, e2) -> eval_arit (Plus(Num n1, eval_arit e2 tbl)) tbl
	| Plus (e1, e2) -> eval_arit (Plus(eval_arit e1 tbl, e2)) tbl
	| Times (Num n1, Num n2) -> Num (n1 * n2)
	| Times (Num n1, e2) -> eval_arit (Times(Num n1, eval_arit e2 tbl)) tbl
	| Times (e1, e2) -> eval_arit (Times(eval_arit e1 tbl, e2)) tbl
	| Minus (Num n1, Num n2) -> Num (n1 - n2)
	| Minus (Num n1, e2) -> eval_arit (Minus(Num n1, eval_arit e2 tbl)) tbl
	| Minus (e1, e2) -> eval_arit (Minus(eval_arit e1 tbl, e2)) tbl

let rec eval_bool (e: bexp) (tbl: (string, aexp) Hashtbl.t) : bexp = match e with
 | True -> True
 | False -> False
 | Neg (e1) -> begin match e1 with
   | True -> False
   | False -> True
   | _ -> eval_bool (Neg(eval_bool e1 tbl)) tbl
   end 
 | Equals (Num n1, Num n2) -> if n1 == n2 then True else False
	| Equals (Num n1, e2) -> eval_bool (Equals(Num n1, eval_arit e2 tbl)) tbl
	| Equals (e1, e2) -> eval_bool (Equals(eval_arit e1 tbl, e2)) tbl
 | LessOrEqual (Num n1, Num n2) -> if n1 <= n2 then True else False
	| LessOrEqual (Num n1, e2) -> eval_bool (LessOrEqual(Num n1, eval_arit e2 tbl)) tbl
	| LessOrEqual (e1, e2) -> eval_bool (LessOrEqual(eval_arit e1 tbl, e2)) tbl
 | Conj (e1, e2) -> begin match e1, e2 with 
   | True, True -> True
   | False, _ -> False
   | _, False -> False
			| True, e2 -> eval_bool (Conj(True, eval_bool e2 tbl)) tbl
			| e1, e2 -> eval_bool (Conj(eval_bool e1 tbl, e2)) tbl
   end

let eval_statements (e: stm) (tbl: (string, aexp) Hashtbl.t) : stm = match e with
	| Assign (x, Num n) -> (Hashtbl.add tbl x (Num n); Skip) 
 | Skip -> Skip
 | Seq (s1, s2) -> assert false
 | If (e1, s1, s2) -> assert false
 | While (e1, s1) -> assert false
 | _ -> assert false

let head_reduction (e: expr) (tbl: (string, aexp) Hashtbl.t) : expr = match e with
 | Aexp (e1) -> Aexp (eval_arit e1 tbl)
 | Bexp (e1) -> Bexp (eval_bool e1 tbl)
 | Stm (e1) -> Stm (eval_statements e1 tbl)


let expr_to_string (e: expr) : string = match e with
  | Aexp (e1) -> begin match e1 with
		| Num (n) -> Stdlib.string_of_int n
		| _ -> assert false
		end
 | Bexp (e1) -> begin match e1 with
		| True -> "True"
		| False -> "False"
		| _ -> assert false
		end
 | Stm (e1) -> assert false

let () = 
	let tbl: (string, aexp) Hashtbl.t = Hashtbl.create 64 in
	let res = head_reduction (Bexp(Neg(LessOrEqual(((Plus(Times(Num(3),Num(4)),Num(5)))),Num(100))))) tbl in
	Format.eprintf "%s\n" (expr_to_string res);