type t_exp =
  | Int
  | String
  | None
  | Infer

type my_val =
  | Num_val of int
  | Str_val of string
  | Error_val of string

type expr =
  | Var of string
  | Num of int
  | Str of string
  | Plus of expr * expr
  | Div of expr * expr
  | Times of expr * expr
  | Cat of expr * expr
  | Len of expr
  | Let of string * expr * expr
  | Error of string
 
type expr_c =  
  | Hole (* 5.6a *)
  | E_leftplus of expr_c * expr (* 5.6b *)
  | E_rightplus of expr * expr_c 
  | E_lefttimes of expr_c * expr 
  | E_righttimes of expr * expr_c
  | E_leftdiv of expr_c * expr
  | E_rightdiv of expr * expr_c
  | E_leftcat of expr_c * expr
  | E_rightcat of expr * expr_c
  | E_len of expr_c 
  | E_leftlet of string * expr_c * expr
  | E_rightlet of string * expr * expr_c



let head_reduction (e: expr)  (tbl: (string, expr) Hashtbl.t) : expr = match e with
  | Error s -> Error s
  | Var x -> Hashtbl.find tbl x
  | Plus (Num n1, Num n2) -> Num (n1 + n2)
  | Times (Num n1, Num n2) -> Num (n1 * n2)
  | Div (_, Num 0) -> Error ("Divisão por zero!")
  | Div (Num n1, Num n2) -> Num (n1 / n2)
  | Cat (Str s1, Str s2) -> Str (s1 ^ s2)
  | Len (Str s) -> Num  (String.length s)
  | _ -> assert false


let rec decompose (e: expr) (tbl: (string, expr) Hashtbl.t) : (expr * expr_c) = match e with 
  | Plus (Error s, _) -> (Error s, Hole)
  | Plus (_, Error s) -> (Error s, Hole)
  | Plus (Num n1, Num n2) -> (e, Hole) 
  | Plus (Num n1, e2) -> let r, c = decompose e2 tbl in (r, E_rightplus (Num n1, c))
  | Plus (e1, e2) -> let r,c = decompose e1 tbl in (r, E_leftplus(c, e2))
  | Times (Error s, _) -> (Error s, Hole)
  | Times (_, Error s) -> (Error s, Hole)
  | Times (Num n1, Num n2) -> (e, Hole)
  | Times (Num n1, e2) -> let r, c = decompose e2 tbl in (r, E_righttimes (Num n1, c))
  | Times (e1, e2) -> let r, c = decompose e1 tbl in (r, E_lefttimes(c, e2))
  | Div (Error s, _) -> (Error s, Hole)
  | Div (_, Error s) -> (Error s, Hole)
  | Div (Num n1, Num n2) -> (e, Hole)
  | Div (Num n1, e2) -> let r, c = decompose e2 tbl in (r, E_rightdiv (Num n1, c))
  | Div (e1, e2) -> let r, c = decompose e1 tbl in (r, E_leftdiv(c, e2))
  | Cat (Str s1, Str s2) -> (e, Hole)
  | Cat (Str n1, e2) -> let r, c = decompose e2 tbl in (r, E_rightcat (Str n1, c))
  | Cat (e1, e2) -> let r, c = decompose e1 tbl in (r, E_leftcat(c, e2))
  | Len (Str s1) -> (e, Hole)
  | Len (e1) -> let r, c = decompose e1 tbl in (r, E_len(c)) 
  | Let (x, e1, e2) ->  match decompose e1 tbl with
    | (e, Hole) -> Hashtbl.add tbl x (head_reduction e tbl); let r2, c2 = decompose e2 tbl in (r2, E_rightlet(x, e, c2))
    | _ -> let r1, c1 = decompose e1 tbl in (r1, E_leftlet(x, c1, e2))




let rec fill_context (e_c: expr_c) (e: expr) : expr = match e_c with 
  | Hole -> e
  | E_rightplus (e1, e2) -> Plus (e1, fill_context e2 e) 
  | E_leftplus (e1, e2) -> Plus (fill_context e1 e, e2) 
  | E_righttimes (e1, e2) -> Times (e1, fill_context e2 e)
  | E_lefttimes (e1, e2) -> Times (fill_context e1 e, e2) 
  | E_rightdiv (e1, e2) -> Div (e1, fill_context e2 e)
  | E_leftdiv (e1, e2) -> Div (fill_context e1 e, e2)
  | E_rightcat (e1, e2) -> Cat (e1, fill_context e2 e)
  | E_leftcat (e1, e2) -> Cat (fill_context e1 e, e2)
  | E_len (e1) -> Len (fill_context e1 e)
  | E_leftlet (x, e1, e2) -> Let (x, fill_context e1 e, e2)
  | E_rightlet (x, e1, e2) -> Let (x, e1, fill_context e2 e)


let rec eval_expr_contextual_dynamics (e: expr) (tbl: (string, expr) Hashtbl.t) : my_val = match e with 
  | Var x -> let e1 = Hashtbl.find tbl x in begin match e1 with 
    | Str s -> Str_val s
    | Num i -> Num_val i
    end
  | Num i -> Num_val i
  | Str s -> Str_val s 
  | Error s -> Error_val s
  | _ -> let e_d, e_c = decompose e tbl in let e1 = head_reduction e_d tbl in let e2 = fill_context e_c e1 in eval_expr_contextual_dynamics e2 tbl


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
      | Str s, _ -> assert false
      | _, Str s -> assert false
      | Num x, Num y -> Num (x+y)
      | Num x, e2 -> eval_expr (Plus(Num x, eval_expr e2))
      | e1, e2 -> eval_expr (Plus(eval_expr e1, e2)))

  | Times (e1, e2) -> (match e1, e2 with
      | Str s, _ -> assert false
      | _, Str s -> assert false
      | Num x, Num y -> Num (x*y)
      | Num x, e2 -> eval_expr (Times(Num x, eval_expr e2))
      | e1, e2 -> eval_expr (Times(eval_expr e1, e2)))

  | Cat (e1, e2) -> (match e1, e2 with
      | Num n, _ -> assert false
      | _, Num n -> assert false
      | Str x, Str y -> Str (x^y)
      | Str x, e2 -> eval_expr (Cat(Str x, eval_expr e2))
      | e1, e2 -> eval_expr (Cat(eval_expr e1, e2)))


  | Len e -> (match e with
      | Num n -> assert false
      | Str s -> Num(String.length s)
      | e -> eval_expr (Len(eval_expr e)))

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
  | Plus (e1, e2) -> "(" ^ expr_to_string e1 ^ " + " ^ expr_to_string e2 ^ ")"
  | Times (e1, e2) -> "(" ^ expr_to_string e1 ^ " * " ^ expr_to_string e2 ^ ")"
  | Cat (e1, e2) -> expr_to_string e1 ^ " ^ " ^ expr_to_string e2
  | Len (e1) -> "Len(" ^ expr_to_string e1 ^ ")"
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

let pp_stack_expr (s:string) (v:expr) =
  Format.eprintf "%s ---> " s;
  Format.eprintf "%s; " (expr_to_string v);
  Format.eprintf "@."

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

  (* This cases fail! *)
  (* let e1 = (Plus(Str("a"),Str("2"))) in
  let e2 = (Let("x",Let("y", Cat(Cat(Num(1),Str("b")),Cat(Str("c"),Num(2))),Cat(Var("y"),Str("EF"))),Cat(Var("x"),Var("x")))) in
  let lst = [e2] in

  print_list lst String; *)
  let gamma_val: (string, expr) Hashtbl.t = Hashtbl.create 64 in
  (* let e1 = Times(Plus(Num(1),Num(2)),Num(3)) in *)
  (* let e1 = Len(Cat(Cat(Str("a"),Str("b")),Str("c"))) in *)
  (* let e1 = Times(Div(Div(Num(10),Num(0)),Num(1)),Num(3)) in *)
  let e2 = Times(Div(Num(1), Len(Str(""))),Num(9)) in
  (* let e1 = Plus(Num(2), Len(Cat(Str("ab"),Str("cd")))) in *)
  (* let e1 = Div(Num(10), Num(0)) in *)
  let e1 = Let("x", Plus(Num(5),Num(5)), Plus(Num(4),Num(4))) in
  let res: my_val = eval_expr_contextual_dynamics e2 gamma_val in
  match res with
    | Num_val i -> Format.eprintf "%s\n" (Stdlib.string_of_int i);
    | Str_val s -> Format.eprintf "%s\n" (s);
    | Error_val s -> Format.eprintf "%s\n" (s);

  Hashtbl.iter pp_stack_expr gamma_val;

  let res: my_val = eval_expr_contextual_dynamics e1 gamma_val in
  match res with
    | Num_val i -> Format.eprintf "%s\n" (Stdlib.string_of_int i);
    | Str_val s -> Format.eprintf "%s\n" (s);
    | Error_val s -> Format.eprintf "%s\n" (s);

  Hashtbl.iter pp_stack_expr gamma_val;
  
  (* let e5 = (Plus(Sub(Sub(Num(30), Num(2)),Num(20)),Num(40))) in 
  let e6 = (Sub(Num(2),Num(30))) in
  let e7 =  (Cat_e(Str("2"),Plus(Num(1),Num(2)))) in
  (* mini_eval_expr_string e5; *)
  mini_eval_expr_string e6;
  mini_eval_expr_string e7 *)

