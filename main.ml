type t_exp =
  | Int
  | String
  | None
  | Infer

type expr =
  | Var of string
  | Num of int
  | Str of string
  | Plus of expr * expr
  | Times of expr * expr
  | Cat of expr * expr
  | Len of expr
  | Let of string * expr * expr
 
type expr_c = 
  | E of expr  
  | Hole


let gamma: (string, t_exp) Hashtbl.t = Hashtbl.create 64

let gamma_val: (string, expr) Hashtbl.t = Hashtbl.create 64

let rec ts (e: expr) (t_e: t_exp) : t_exp =
  match t_e with
  | Int | String ->
    begin match e with
      | Var x -> if Hashtbl.find gamma x = t_e then t_e else None
      | Num _ -> if Int = t_e then Int else None
      | Str _ -> if String = t_e then String else None
      | Plus (e1, e2) -> if (Int = t_e && (ts e1 Int) = Int && (ts e2 Int) = Int) then Int else None
      | Times (e1, e2) -> if (Int = t_e && (ts e1 Int) = Int && (ts e2 Int) = Int) then Int else None
      | Cat (e1, e2) -> if (String = t_e && (ts e1 String) = String && (ts e2 String) = String) then String else None
      | Len (e1) -> if(Int = t_e && (ts e1 String) = String) then Int else None
      | Let (x, e1, e2) ->
        let ty_x = ts e1 Infer in
        Hashtbl.add gamma x ty_x;
        ts e2 t_e
    end
  | None -> None
  | Infer ->
    begin match e with
      | Var x -> Hashtbl.find gamma x
      | Num n -> Int
      | Str s -> String
      | Plus (e1, e2) ->
        begin match ts e1 Int, ts e2 Int with
          | Int, Int -> Int
          | _ -> None
        end
      | Times (e1, e2) ->
        begin match ts e1 Int, ts e2 Int with
          | Int, Int -> Int
          | _ -> None
        end
      | Cat (e1, e2) ->
        begin match ts e1 String, ts e2 String with
          | String, String -> String
          | _ -> None
        end
      | Len (e1) ->
        begin match ts e1 String with
          | String -> Int
          | _ -> None
        end
      | Let (x, e1, e2) -> 
          let ty_x = ts e1 Infer in
          Hashtbl.add gamma x ty_x;
          ts e2 t_e
    end

let rec eval_expr (e: expr) : expr = match e with

  | Var x -> Hashtbl.find gamma_val x
  | Num n -> Num n
  | Str s -> Str s

  | Plus (e1, e2) -> (match e1, e2 with
      | Num x, Num y -> Num (x+y)
      | Num x, e2 -> eval_expr (Plus(Num x, eval_expr e2))
      | e1, e2 -> eval_expr (Plus(eval_expr e1, e2)))

  | Times (e1, e2) -> (match e1, e2 with
      | Num x, Num y -> Num (x*y)
      | Num x, e2 -> eval_expr (Times(Num x, eval_expr e2))
      | e1, e2 -> eval_expr (Times(eval_expr e1, e2)))

  | Cat (e1, e2) -> (match e1, e2 with
      | Str x, Str y -> Str (x^y)
      | Str x, e2 -> eval_expr (Cat(Str x, eval_expr e2))
      | e1, e2 -> eval_expr (Cat(eval_expr e1, e2)))


  | Len e -> (match e with
      | Str s -> Num(String.length s)
      | e -> eval_expr (Len(eval_expr e)))
(* Let("x",Let("y",Plus(Var("x"),Num(1)),Plus(Var("x"),Var("x")),Plus(Var("x"),Var("x"))) *)
  (* let x =
       let y = x + 1 in
     in
     x + x *)
  (* | Let (e1, e2, e3) -> Num(1) *)
  (* | Let (x, e2, e3) -> (Hashtbl.add gamma_val x (eval_expr (e2));
                        eval_expr e3) *)
  | Let (x, e2, e3) -> 
    begin match e2 with  
     | Num n -> (Hashtbl.add gamma_val x (Num n) ; eval_expr e3)
     | Str s -> (Hashtbl.add gamma_val x (Str s) ; eval_expr e3)
     | Var x -> (Hashtbl.add gamma_val x (Hashtbl.find gamma_val x); eval_expr e3)
     | Plus (e4, e5) -> (Hashtbl.add gamma_val x (eval_expr (Plus (e4, e5))); eval_expr e3)
     | Times (e4, e5) -> (Hashtbl.add gamma_val x (eval_expr (Times (e4, e5))); eval_expr e3)
     | Cat (e4, e5) -> (Hashtbl.add gamma_val x (eval_expr (Cat (e4, e5))); eval_expr e3)
     | Len (e4) -> (Hashtbl.add gamma_val x (eval_expr (Len (e4))); eval_expr e3)
     | Let (y, e4, e5) -> (Hashtbl.add gamma_val x (eval_expr (Let (y, e4, e5))); eval_expr e3)
    end 

(* let base_cases (e: expr_c) : expr_c =
  match e with 
    | Plus (Num n1, Num n2) -> n1 + n2 *)
  (* Plus(e1,e2) = (let x = 2 + 3 in x + 1) + 4 *)
  (* 1+2+3
  Hole ([])+ 3 *)
(* let rec eval_expr_contextual_dynamics (e: expr_c) : expr_c = match e with 
    | Plus (e1, e2) -> match e1 with 
      | Num n -> n + eval_expr_contextual_dynamics e2 
      | Str _ -> assert false
      | Let (x, e3, e4) -> ( ; eval_expr_contextual_dynamics e4 + eval_expr_contextual_dynamics e2 ; eval_expr_contextual_dynamics e4)
      | Cat (_,_) -> assert false *)

 

let expr_to_value (e: expr) : string = match eval_expr e with
  | Num n -> Stdlib.string_of_int n
  | Str s -> s
  | _ -> "Not defined"

let type_exp_to_string (t_e: t_exp) : string = match t_e with 
  | Int -> "Int"
  | String -> "String"
  | None -> "None"
  | Infer -> "Infer"

let expr_to_type (e: expr) (t_e: t_exp) : string = match ts e t_e with
  | Int -> "Int"
  | String -> "String"
  | None -> "None"
  | Infer -> "Infer"


let rec expr_to_string (e: expr) : string = match e with
  | Num n -> Stdlib.string_of_int n
  | Str s -> "\"" ^ s ^ "\""
  | Var x -> x
  | Plus (e1, e2) -> expr_to_string e1 ^ " + " ^ expr_to_string e2
  | Times (e1, e2) -> expr_to_string e1 ^ " * " ^ expr_to_string e2
  | Cat (e1, e2) -> expr_to_string e1 ^ " ^ " ^ expr_to_string e2
  | Len (e1) -> "Len (" ^ expr_to_string e1 ^ ")"
  | Let (x, e1, e2) -> "Let " ^ x ^ " := " ^ expr_to_string e1 ^ " in " ^ expr_to_string e2 


let expr_to_value_result (e: expr) : string =  expr_to_string e ^ " = " ^ expr_to_value e 

let expr_to_type_result (e: expr) (t_e: t_exp) : string = expr_to_string e ^ " : " ^ type_exp_to_string (t_e) ^ " = " ^  expr_to_type e t_e 

let rec print_list lst t_exp =
  match lst with
  | [] -> ()
  | x :: xs -> 
      Format.eprintf "%s\n" (expr_to_type_result x t_exp);
      Format.eprintf "%s\n" (expr_to_value_result x);
      print_list xs t_exp


let () =
  let e1 = (Let("x",Let("y",Plus(Num(3),Num(1)),Plus(Var("y"),Var("y"))),Plus(Var("x"),Var("x")))) in
  let e2 = ((Let("x", Num(3),Plus(Var("x"),Num(3))))) in
  let e3 = (Times(Plus(Num(3),Num(2)),Num(3))) in 
  let e4 = (Let("x",Let("y", Cat(Cat(Str("a"),Str("b")),Cat(Str("c"),Str("d"))),Cat(Var("y"),Str("EF"))),Len(Var("x")))) in
  let lst = [e1; e2; e3; e4] in
  print_list lst Int;

  let e1 = (Cat(Str("a"),Str("b"))) in
  let e2 = (Let("x",Cat(Str("ab"),Str("cd")),Cat(Var("x"),Var("x")))) in
  let e3 = (Let("x",Let("y", Cat(Cat(Str("a"),Str("b")),Cat(Str("c"),Str("d"))),Cat(Var("y"),Str("EF"))),Cat(Var("x"),Var("x")))) in
  let lst = [e1; e2; e3] in

  print_list lst String;
