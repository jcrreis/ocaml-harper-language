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

let rec ts e t_e =
  match t_e with
  | Int | String ->
    begin match e with
      | Var x -> if Hashtbl.find gamma x = t_e then t_e else None
      (* | Var x -> ts (Hashtbl.find gamma_val x) t_e *)
      | Num _ -> Int = t_e
      | Str _ -> String = t_e
      | Plus (e1, e2) -> Int = t_e && ts e1 Int && ts e2 Int
      | Times (e1, e2) -> Int = t_e && ts e1 Int && ts e2 Int
      | Cat (e1, e2) -> String = t_e && ts e1 String && ts e2 String
      | Len (e1) -> Int = t_e && ts e1 String
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
      | Plus (e1, e2) ->
        begin match ts e1 Int, ts e2 Int with
          | Int, Int -> Int
          | _ -> None
        end
      | _ -> assert false (* TODO? *)
    end

let rec eval_expr e = match e with

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

  (* let x =
       let y = x + 1 in
     in
     x + x *)
  (* | Let (e1, e2, e3) -> Num(1) *)
  | Let (x, e2, e3) -> (Hashtbl.add gamma_val x (eval_expr (e2));
                        eval_expr e3)

let expr_to_value e = match e with
  | Num n -> Stdlib.string_of_int n
  | Str s -> s
  | _ -> "Not defined"


let () =
  let res_second = expr_to_value (eval_expr (Times(Plus(Num(3),Num(2)),Num(3)))) in
  let res_first = expr_to_value (eval_expr (Cat(Str("ab"), Str("cd")))) in
  let res = expr_to_value (eval_expr (Len((Cat(Str("ab"), Str("cd")))))) in
  Format.eprintf "%s\n" res_second;
  Format.eprintf "%s\n" res_first;
  Format.eprintf "%s\n" res;
