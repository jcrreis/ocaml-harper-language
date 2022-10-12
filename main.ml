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
(* Let("x",Let("y",Plus(Var("x"),Num(1)))) *)
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
     | Let (y, e5, e6) -> Num(0)
    end 
let rec eval_expr_contextual_dynamics (e: expr) : expr = match e with 
  | _ -> Num(0)

let rec eval_expr_equation_dynamics (e: expr) : expr = match e with 
  | _ -> Num(0)
     

let expr_to_value (e:expr) : string = match e with
  | Num n -> Stdlib.string_of_int n
  | Str s -> s
  | _ -> "Not defined"

let expr_to_type (e: expr) (t_e: t_exp) : string = match ts e t_e with
  | Int -> "Int"
  | String -> "String"
  | None -> "None"
  | Infer -> "Infer"


let () =
  (* let res_second = expr_to_value (eval_expr (Times(Plus(Num(3),Num(2)),Num(3)))) in
  let res_first = expr_to_value (eval_expr (Cat(Str("ab"), Str("cd")))) in
  let res = expr_to_value (eval_expr (Len((Cat(Str("ab"), Str("cd")))))) in *)
  let res = expr_to_value (eval_expr ((Let("x", Num(3),Plus(Var("x"),Num(3)))))) in
  (* let res = expr_to_type (Let("x", Num(3),Plus(Var("x"),Num(3)))) Int in *)
  let res_second = expr_to_type (Times(Plus(Num(3),Num(2)),Num(3))) Int in 
  let res_first = expr_to_type (Cat(Str("ab"), Str("cd"))) Int in
  (* let res = expr_to_type (Len((Cat(Str("ab"), Str("cd"))))) Int in *)
  (* let res = expr_to_type (Let("x", Num(3),Plus(Var("x"),Num(3)))) Int in *)
  Format.eprintf "%s\n" res_second;
  Format.eprintf "%s\n" res_first;
  Format.eprintf "%s\n" res;
