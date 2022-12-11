type t_exp =
  | Int
  | String
  | None
  | Infer
  | Fun of string * t_exp * t_exp

type my_val =
  | Num_val of int
  | Str_val of string
  | Error_val of string
  | Fun_val

type expr =
  | Var of string
  | Num of int
  | Str of string
  | Fun
  | Error of string
  | Plus of expr * expr
  | Div of expr * expr
  | Times of expr * expr
  | Cat of expr * expr
  | Len of expr
  | Let of string * expr * expr
  | F_def of string (*f_name*) * t_exp * t_exp * string (* x1 *) * expr (* e2 *) * expr (*e*) (* Usar hastables para guardar? *)
  | F_apply of string (*f_name*) * expr (* arg *)


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
  | E_fdef of string * t_exp * t_exp * string * expr_c
  | E_fapply of string * expr_c


let head_reduction (e: expr) (tbl: (string, expr) Hashtbl.t) : expr = match e with
  | Fun -> Fun
  | Error s -> Error s
  | Plus (Num n1, Num n2) -> Num (n1 + n2)
  | Times (Num n1, Num n2) -> Num (n1 * n2)
  | Div (_, Num 0) -> Error ("Divisão por zero!")
  | Div (Num n1, Num n2) -> Num (n1 / n2)
  | Cat (Str s1, Str s2) -> Str (s1 ^ s2)
  | Len (Str s) -> Num  (String.length s)
  | _ -> assert false

module SS = Set.Make(String)

let rec free_variables (e: expr) : SS.t = match e with
  | Var x -> SS.singleton x
  | Num _ -> SS.empty
  | Str _ -> SS.empty
  | Plus (e1, e2) -> SS.union (free_variables e1) (free_variables e2)
  | Times (e1, e2) -> SS.union (free_variables e1) (free_variables e2)
  | Div (e1, e2) -> SS.union (free_variables e1) (free_variables e2)
  | Cat (e1, e2) -> SS.union (free_variables e1) (free_variables e2)
  | Len (e1) -> free_variables e1
  | Let (x, e1, e2) ->  SS.union (free_variables e1) ((SS.filter (fun (x') -> x <> x') (free_variables e2)))
  | F_def (_, _, _, x, e1, e) -> SS.union ((SS.filter (fun (x') -> x <> x') (free_variables e1))) (free_variables e)
  | F_apply (_, e1) -> free_variables e1
  | _ -> assert false (* TODO *)

(* let rec gen_random_string (length: int) (s: string) = match length with
 | 0 -> s
 | _ -> Random.self_init ();
    gen_random_string (length-1) (s ^ String.make 1 (Char.chr (97 + (Random.int 26)))) *)


let rec generate_unique_name (xs: SS.t) (x: string): string =
  let new_val = x ^ "1" in
  if (SS.mem new_val xs) then generate_unique_name xs new_val else new_val

let rec rename (e: expr) (x: string) (x': string) : expr = match e with
  | Var y -> if x = y then Var x' else Var y
  | Num _ -> e
  | Str _ -> e
  | Plus (e1, e2) -> Plus(rename e1 x x', rename e2 x x')
  | Times (e1,e2) -> Times(rename e1 x x', rename e2 x x')
  | Div (e1, e2) -> Div(rename e1 x x', rename e2 x x')
  | Cat (e1, e2) -> Cat(rename e1 x x', rename e2 x x')
  | Len (e1) -> Len (rename e1 x x')
  | Let (y, e1, e2) -> if x = y then Let (x', e1, rename e2 x x')
    else Let (y, rename e1 x x', rename e2 x x')


let rec substitute (e: expr) (v: expr) (x: string) : expr = match e with
  | Var y -> (*if (SS.mem x (free_variables e)) then
    let new_val = generate_unique_name (free_variables e) x in
    substitute (rename e x new_val) v new_val
    else *)if x = y then v else e
  | Num _ -> e
  | Str _ -> e
  | Plus (e1, e2) -> Plus(substitute e1 v x, substitute e2 v x)
  | Times (e1, e2) -> Times(substitute e1 v x, substitute e2 v x)
  | Div (e1, e2) -> Div(substitute e1 v x, substitute e2 v x)
  | Cat (e1, e2) -> Cat(substitute e1 v x, substitute e2 v x)
  | Len (e1) -> Len(substitute e1 v x)
  | Let (y, e1, e2) ->
    let e3 = substitute e1 v x in
      Let (y, e3, substitute e2 v x)


let rec expr_to_string (e: expr) : string = match e with
  | Num n -> Stdlib.string_of_int n
  | Str s -> "\"" ^ s ^ "\""
  | Var x -> x
  | Plus (e1, e2) -> "(" ^ expr_to_string e1 ^ " + " ^ expr_to_string e2 ^ ")"
  | Times (e1, e2) -> "(" ^ expr_to_string e1 ^ " * " ^ expr_to_string e2 ^ ")"
  | Cat (e1, e2) -> expr_to_string e1 ^ " ^ " ^ expr_to_string e2
  | Len (e1) -> "Len(" ^ expr_to_string e1 ^ ")"
  | Let (x, e1, e2) -> "Let " ^ x ^ " := " ^ expr_to_string e1 ^ " in " ^ expr_to_string e2

let pp_stack_expr (s:string) (v:expr) =
  Format.eprintf "%s ---> " s;
  Format.eprintf "%s; " (expr_to_string v);
  Format.eprintf "@."

(* let functions: (string, expr) Hashtbl.t = Hashtbl.create 64 *)

let rec decompose (e: expr) (tbl: (string, expr) Hashtbl.t) (functions: (string, (expr * string)) Hashtbl.t): (expr * expr_c) = match e with
  | Plus (Error s, _) -> (Error s, Hole)
  | Plus (_, Error s) -> (Error s, Hole)
  | Plus (Num n1, Num n2) -> (e, Hole)
  | Plus (Num n1, e2) -> let r, c = decompose e2 tbl functions in (r, E_rightplus (Num n1, c))
  | Plus (e1, e2) -> let r,c = decompose e1 tbl functions in (r, E_leftplus(c, e2))
  | Times (Error s, _) -> (Error s, Hole)
  | Times (_, Error s) -> (Error s, Hole)
  | Times (Num n1, Num n2) -> (e, Hole)
  | Times (Num n1, e2) -> let r, c = decompose e2 tbl functions in (r, E_righttimes (Num n1, c))
  | Times (e1, e2) -> let r, c = decompose e1 tbl functions in (r, E_lefttimes(c, e2))
  | Div (Error s, _) -> (Error s, Hole)
  | Div (_, Error s) -> (Error s, Hole)
  | Div (Num n1, Num n2) -> (e, Hole)
  | Div (Num n1, e2) -> let r, c = decompose e2 tbl functions in (r, E_rightdiv (Num n1, c))
  | Div (e1, e2) -> let r, c = decompose e1 tbl functions in (r, E_leftdiv(c, e2))
  | Cat (Str s1, Str s2) -> (e, Hole)
  | Cat (Str n1, e2) -> let r, c = decompose e2 tbl functions in (r, E_rightcat (Str n1, c))
  | Cat (e1, e2) -> let r, c = decompose e1 tbl functions in (r, E_leftcat(c, e2))
  | Len (Str s1) -> (e, Hole)
  | Len (e1) -> let r, c = decompose e1 tbl functions in (r, E_len(c))
  | Let (x, Num n1, e2) -> let e3 = substitute e2 (Num n1) x in let r, c = decompose e3 tbl functions in
    begin match c with
      | Hole -> (r, c)
      | _ -> (r, E_rightlet (x, Num n1, c))
    end
  | Let (x, Str s1, e2) -> let e3 = substitute e2 (Str s1) x in let r, c = decompose e3 tbl functions in
    begin match c with
     | Hole -> (r, c)
     | _ -> (r, E_rightlet (x, Str s1, c))
    end
  | Let (x, e1, e2) -> let r, c = decompose e1 tbl functions in (r, E_leftlet(x, c, e2))
  | F_def (fname, _, _, x, e1, e) -> 
    Hashtbl.add functions fname (e1, x); 
    decompose e tbl functions
  | F_apply (fname, e1) -> let (e2, x) = Hashtbl.find functions fname in
    let e1_d, _ = decompose e1 tbl functions in 
    let e_sub = substitute e2 (e1_d) x in
    decompose e_sub tbl functions



let rec fill_context (e_c: expr_c) (e: expr) (tbl: (string, expr) Hashtbl.t) : expr = match e_c with
  | Hole -> e
  | E_rightplus (e1, e2) -> Plus (e1, fill_context e2 e tbl)
  | E_leftplus (e1, e2) -> Plus (fill_context e1 e tbl, e2)
  | E_righttimes (e1, e2) -> Times (e1, fill_context e2 e tbl)
  | E_lefttimes (e1, e2) -> Times (fill_context e1 e tbl, e2)
  | E_rightdiv (e1, e2) -> Div (e1, fill_context e2 e tbl)
  | E_leftdiv (e1, e2) -> Div (fill_context e1 e tbl, e2)
  | E_rightcat (e1, e2) -> Cat (e1, fill_context e2 e tbl)
  | E_leftcat (e1, e2) -> Cat (fill_context e1 e tbl, e2)
  | E_len (e1) -> Len (fill_context e1 e tbl)
  | E_leftlet (x, e1, e2) -> Let (x, fill_context e1 e tbl, e2)
  | E_rightlet (x, e1, e2) -> Let (x, e1, fill_context e2 e tbl)


let rec eval_expr_contextual_dynamics (e: expr) (tbl: (string, expr) Hashtbl.t) (functions: (string, (expr * string)) Hashtbl.t): my_val = match e with
  | Var x -> let e1 = Hashtbl.find tbl x in begin match e1 with
    | Str s -> Str_val s
    | Num i -> Num_val i
    end
  | Num i -> Num_val i
  | Str s -> Str_val s
  | Error s -> Error_val s
  | Fun -> Fun_val
  | _ -> let e_d, e_c = decompose e tbl functions in
         let e1 = head_reduction e_d tbl in
         let e2 = fill_context e_c e1 tbl in
         eval_expr_contextual_dynamics e2 tbl functions


let gamma: (string, t_exp) Hashtbl.t = Hashtbl.create 64

let gamma_val: (string, expr) Hashtbl.t = Hashtbl.create 64

let rec ts (gamma: (string, t_exp) Hashtbl.t) (e: expr) (t_e: t_exp): t_exp =
  match t_e with
  | Int | String | Fun(_,_,_) ->
    begin match e with
      | Var x -> if Hashtbl.find gamma x = t_e then t_e else None
      | Num _ -> if Int = t_e then Int else None
      | Str _ -> if String = t_e then String else None
      | Plus (e1, e2) -> if (Int = t_e && (ts gamma e1 Int) = Int && (ts gamma e2 Int) = Int) then Int else None
      | Times (e1, e2) -> if (Int = t_e && (ts gamma e1 Int) = Int && (ts gamma e2 Int) = Int) then Int else None
      | Cat (e1, e2) -> if (String = t_e && (ts gamma e1 String) = String && (ts gamma e2 String ) = String) then String else None
      | Len (e1) -> if(Int = t_e && (ts gamma e1 String) = String) then Int else None
      | Let (x, e1, e2) ->
        let ty_x = ts gamma e1 Infer in
        Hashtbl.add gamma x ty_x;
        ts gamma e2 t_e
      | F_def (fname, t_e (*tau1*), t_e1 (*tau2*), x,e1 (*e2*), e) ->
          Hashtbl.add gamma x t_e;
          Hashtbl.add gamma fname (Fun(fname, t_e, t_e1));
          if(t_e1 = (ts gamma e1 t_e1))
          then
            begin
              Hashtbl.add gamma fname (Fun(fname, t_e, t_e1));
              Fun(fname, t_e, t_e1)
            end
          else
            None
      | F_apply (fname, e1) ->
        let Fun(_,t_e, t_e1) = Hashtbl.find gamma fname in
        if(t_e = (ts gamma e1 t_e))
        then
          t_e1
        else
          None
    end
  | None -> None
  | Infer ->
    begin match e with
      | Var x -> Hashtbl.find gamma x
      | Num n -> Int
      | Str s -> String
      | Plus (e1, e2) ->
        begin match ts gamma e1 Int, ts gamma e2 Int with
          | Int, Int -> Int
          | _ -> None
        end
      | Times (e1, e2) ->
        begin match ts gamma e1 Int, ts gamma e2 Int with
          | Int, Int -> Int
          | _ -> None
        end
      | Cat (e1, e2) ->
        begin match ts gamma e1 String, ts gamma e2 String with
          | String, String -> String
          | _ -> None
        end
      | Len (e1) ->
        begin match ts gamma e1 String with
          | String -> Int
          | _ -> None
        end
      | Let (x, e1, e2) ->
          let ty_x = ts gamma e1 Infer in
          Hashtbl.add gamma x ty_x;
          ts gamma e2 t_e
      | F_def (fname, t_e, t_e1, x, e1, e) -> assert false
      | F_apply (fname, e1) -> assert false
    end



let rec decompose_small_step (e: expr) (tbl: (string, expr) Hashtbl.t) (functions: (string, (expr * string)) Hashtbl.t): expr = match e with
  | Plus (Error s, _) -> Error s
  | Plus (_, Error s) -> Error s
  | Plus (Num _, Num _) -> head_reduction e tbl
  | Plus (Num n1, e2) -> Plus(Num n1, decompose_small_step e2 tbl functions)
  | Plus (e1, e2) -> Plus(decompose_small_step e1 tbl functions, e2)
  | Times (Error s, _) -> Error s
  | Times (_, Error s) -> Error s
  | Times (Num _, Num _) -> head_reduction e tbl
  | Times (Num n1, e2) -> Times(Num n1, decompose_small_step e2 tbl functions)
  | Times (e1, e2) -> Times(decompose_small_step e1 tbl functions, e2)
  | Div (Error s, _) -> Error s
  | Div (_, Error s) -> Error s
  | Div (Num _, Num _) -> head_reduction e tbl
  | Div (Num n1, e2) -> Div(Num n1, decompose_small_step e2 tbl functions)
  | Div (e1, e2) -> Div(decompose_small_step e1 tbl functions, e2)
  | Cat (Str _, Str _) -> head_reduction e tbl
  | Cat (Str s1, e2) -> Cat(Str s1, decompose_small_step e2 tbl functions)
  | Cat (e1, e2) -> Cat(decompose_small_step e1 tbl functions, e2)
  | Len (Str _) -> head_reduction e tbl
  | Len (e1) -> Len(decompose_small_step e1 tbl functions)
  | Let (x, Num n1, e2) -> substitute e2 (Num n1) x
  | Let (x, Str s1, e2) -> substitute e2 (Str s1) x
  | Let (x, e1, e2) -> Let(x, decompose_small_step e1 tbl functions, e2)
  | F_def (fname, t_e, t_e1, x, e1, e) -> Hashtbl.add functions fname (e1, x); decompose_small_step e tbl functions
  | F_apply (fname, e1) -> let (e2, x) = Hashtbl.find functions fname in
    let e_sub = substitute e2 e1 x in
    decompose_small_step e_sub tbl functions


let rec eval_expr_small_step (e: expr) (tbl: (string, expr) Hashtbl.t) (functions: (string, (expr * string)) Hashtbl.t) : my_val = match e with
  | Var x -> let e1 = Hashtbl.find tbl x in begin match e1 with
    | Str s -> Str_val s
    | Num i -> Num_val i
    end
  | Num i -> Num_val i
  | Str s -> Str_val s
  | Error s -> Error_val s
  | Fun -> Fun_val
  | _-> let e1 = decompose_small_step e tbl functions in eval_expr_small_step e1 tbl functions


let rec eval_expr_big_step (e: expr) : expr = match e with

  | Var x -> Hashtbl.find gamma_val x
  | Num n -> Num n
  | Str s -> Str s

  | Plus (e1, e2) -> (match e1, e2 with
      | Str s, _ -> assert false
      | _, Str s -> assert false
      | Num x, Num y -> Num (x+y)
      | Num x, e2 -> eval_expr_big_step (Plus(Num x, eval_expr_big_step e2))
      | e1, e2 -> eval_expr_big_step (Plus(eval_expr_big_step e1, e2)))

  | Times (e1, e2) -> (match e1, e2 with
      | Str s, _ -> assert false
      | _, Str s -> assert false
      | Num x, Num y -> Num (x*y)
      | Num x, e2 -> eval_expr_big_step (Times(Num x, eval_expr_big_step e2))
      | e1, e2 -> eval_expr_big_step (Times(eval_expr_big_step e1, e2)))

  | Cat (e1, e2) -> (match e1, e2 with
      | Num n, _ -> assert false
      | _, Num n -> assert false
      | Str x, Str y -> Str (x^y)
      | Str x, e2 -> eval_expr_big_step (Cat(Str x, eval_expr_big_step e2))
      | e1, e2 -> eval_expr_big_step (Cat(eval_expr_big_step e1, e2)))


  | Len e -> (match e with
      | Num n -> assert false
      | Str s -> Num(String.length s)
      | e -> eval_expr_big_step (Len(eval_expr_big_step e)))

  (* | Let (x, e2, e3) -> (Hashtbl.add gamma_val x (eval_expr (e2));
                        eval_expr e3) *)

  | Let (x, e2, e3) ->
    begin match e2 with
     | Num n -> (Hashtbl.add gamma_val x (Num n) ; eval_expr_big_step e3)
     | Str s -> (Hashtbl.add gamma_val x (Str s) ; eval_expr_big_step e3)
     | Var x -> (Hashtbl.add gamma_val x (Hashtbl.find gamma_val x); eval_expr_big_step e3)
     | Plus (e4, e5) -> (Hashtbl.add gamma_val x (eval_expr_big_step (Plus (e4, e5))); eval_expr_big_step e3)
     | Times (e4, e5) -> (Hashtbl.add gamma_val x (eval_expr_big_step (Times (e4, e5))); eval_expr_big_step e3)
     | Cat (e4, e5) -> (Hashtbl.add gamma_val x (eval_expr_big_step (Cat (e4, e5))); eval_expr_big_step e3)
     | Len (e4) -> (Hashtbl.add gamma_val x (eval_expr_big_step (Len (e4))); eval_expr_big_step e3)
     | Let (y, e4, e5) -> (Hashtbl.add gamma_val x (eval_expr_big_step (Let (y, e4, e5))); eval_expr_big_step e3)
    end


let expr_to_value (e: expr) : string = match eval_expr_big_step e with
  | Num n -> Stdlib.string_of_int n
  | Str s -> s
  | _ -> "Not defined"

let type_exp_to_string (t_e: t_exp) : string = match t_e with
  | Int -> "Int"
  | String -> "String"
  | None -> "None"
  | Infer -> "Infer"

let expr_to_type (e: expr) (t_e: t_exp) (gamma: (string, t_exp) Hashtbl.t): string = match ts gamma e t_e with
  | Int -> "Int"
  | String -> "String"
  | None -> "None"
  | Infer -> "Infer"
  | Fun (fname, t_e1, t_e2) -> fname ^ " : " ^ type_exp_to_string t_e1 ^ " -> " ^ type_exp_to_string t_e2


let expr_to_value_result (e: expr) : string =  expr_to_string e ^ " = " ^ expr_to_value e

let expr_to_type_result (e: expr) (t_e: t_exp) (gamma: (string, t_exp) Hashtbl.t): string =
    expr_to_string e ^ " : " ^ type_exp_to_string (t_e) ^ " = " ^  expr_to_type e t_e gamma

let rec print_list lst t_exp gamma =
  match lst with
  | [] -> ()
  | x :: xs ->
      Format.eprintf "%s\n" (expr_to_type_result x t_exp gamma);
      Format.eprintf "%s\n" (expr_to_value_result x);
      print_list xs t_exp gamma

let print_set (s: SS.t): unit = SS.iter print_endline s;;

let test_free_var_and_substitute (e: expr) (tbl: (string, expr) Hashtbl.t) (functions: (string, (expr * string)) Hashtbl.t): unit =
  Format.eprintf "Original Expression: %s\n" (expr_to_string e);
  let f_vars = free_variables e in
  Format.eprintf "Free variables: \n";
  print_set f_vars;
  let e2 = eval_expr_contextual_dynamics e tbl functions in
  match e2 with
    | Num_val i -> Format.eprintf "%s\n" (Stdlib.string_of_int i);
    | Str_val s -> Format.eprintf "%s\n" (s);
    | Error_val s -> Format.eprintf "%s\n" (s)

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
  let gamma: (string, t_exp) Hashtbl.t = Hashtbl.create 64 in
  let gamma_val: (string, expr) Hashtbl.t = Hashtbl.create 64 in
  let functions: (string, (expr * string)) Hashtbl.t = Hashtbl.create 64 in
  (* let e1 = Times(Plus(Num(1),Num(2)),Num(3)) in *)
  (* let e1 = Len(Cat(Cat(Str("a"),Str("b")),Str("c"))) in *)
  (* let e1 = Times(Div(Div(Num(10),Num(0)),Num(1)),Num(3)) in *)
  (* let e2 = Times(Div(Num(1), Len(Str(""))),Num(9)) in
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

  Hashtbl.iter pp_stack_expr gamma_val; *)
  let e1 = (Let("x",Let("x", Cat(Cat(Str("a"),Str("b")),Cat(Str("c"),Str("d"))),Cat(Var("x"),Str("EF"))),Cat(Var("x"),Var("x")))) in
  let e2 = (Let("x",Num(42),Plus(Var("x"),Var("x")))) in
  let e3 = (Let("x",Var("y"),Let("y",Plus(Var("x"),Var("y")),Var("y")))) in
  (* let e1 = Plus(Var("x"),Var("y")) in *)
  (* let e2 = rename e1 "x" "b" in *)
  let s = expr_to_string e2 in
  let lst = free_variables e1 in
  (* test_free_var_and_substitute e1 gamma_val functions; *)
  (* test_free_var_and_substitute e2; *)
  (* test_free_var_and_substitute e3;; *)
  (* let print_set s =
    SS.iter print_endline s in
  print_set lst;
  Format.eprintf "%s\n" (generate_unique_name lst "x"); *)
  let e1 = F_def("teste1", String, Int, "x", Len(Var("x")),Plus(Num(10),Num(10))) in
  Format.eprintf "%s\n" (expr_to_type e1 (Fun("teste", String, Int)) gamma);
  let e2 = F_def("teste2", String, String, "x", Cat(Var("x"),Var("x")),Plus(Num(10),Num(10))) in
  Format.eprintf "%s\n" (expr_to_type e2 (Fun("teste", String, String)) gamma);
  let res3 = F_apply("teste3", Let("y", Cat(Str("AB"),Str("CD")),Cat(Var("y"),Var("y")))) in
  let e3 = F_def("teste3", String, String, "x", Let("y", Str("O valor de x é: "), Cat(Var("y"),Var("x"))), res3) in
  Format.eprintf "%s\n" (expr_to_type e2 (Fun("teste", String, String)) gamma);
  eval_expr_contextual_dynamics e1 gamma_val functions;
  eval_expr_contextual_dynamics e2 gamma_val functions;
  let e4' = eval_expr_contextual_dynamics e3 gamma_val functions in
  (* Let("y", Cat(Str("AB"),Str("CD")),Cat(Var("y"),Var("y"))) *)
  (* Cat(Str("AB"),Str("CD")) *)
  let res1 = F_apply("teste1",  Let("y", Cat(Str("AB"),Str("CD")),Cat(Var("y"),Var("y")))) in
  let res2 = Let("x", Let("x", Str("a"), Cat(Var("x"),Var("x"))), Var("x")) in
  (* Format.eprintf "%s" (expr_to_string (rename res2 "x" "x'")); *)
  let e1' = eval_expr_contextual_dynamics res1 gamma_val functions in
  let res2 = F_apply("teste2", Let("y", Cat(Str("AB"),Str("CD")),Cat(Var("y"),Var("y")))) in
  let e2' = eval_expr_contextual_dynamics res2 gamma_val functions in
 
  let e3' = eval_expr_contextual_dynamics res3 gamma_val functions in
  (* match e1' with
    | Num_val i -> Format.eprintf "%s\n" (Stdlib.string_of_int i);
    | Str_val s -> Format.eprintf "%s\n" (s);
    | Error_val s -> Format.eprintf "%s\n" (s);
  match e2' with
    | Num_val i -> Format.eprintf "%s\n" (Stdlib.string_of_int i);
    | Str_val s -> Format.eprintf "%s\n" (s);
    | Error_val s -> Format.eprintf "%s\n" (s); *)
  match e4' with
    | Num_val i -> Format.eprintf "%s\n" (Stdlib.string_of_int i);
    | Str_val s -> Format.eprintf "%s\n" (s);
    | Error_val s -> Format.eprintf "%s\n" (s)

  (* let e1 = F_def("teste", Int, Int, "x", Let("x", Plus(Num(10),Var("x")),Plus(Var("x"),Var("x")))) in
  let e2 = F_apply("teste", Num(10)) in
  let res = eval_expr_contextual_dynamics e1 gamma_val functions in
  let res: my_val = eval_expr_contextual_dynamics e2 gamma_val functions in
  match res with
   | Num_val i -> Format.eprintf "%s\n" (Stdlib.string_of_int i);
   | Str_val s -> Format.eprintf "%s\n" (s);
   | Error_val s -> Format.eprintf "%s\n" (s);
   | Fun_val -> Format.eprintf "%s\n" "Função definida"; *)
  (* let e1 = (Let("x",Let("y", Cat(Cat(Str("a"),Str("b")),Cat(Str("c"),Str("d"))),Cat(Var("y"),Str("EF"))),Cat(Var("x"),Var("x")))) in
  let res: my_val = eval_expr_contextual_dynamics e1 gamma_val in
  match res with
    | Num_val i -> Format.eprintf "%s\n" (Stdlib.string_of_int i);
    | Str_val s -> Format.eprintf "%s\n" (s);
    | Error_val s -> Format.eprintf "%s\n" (s);
  let e1 = Let("x", Plus(Num(5),Num(5)), Div(Var("x"),Num(0))) in
  let res: my_val = eval_expr_small_step e1 gamma_val functions in
   match res with
    | Num_val i -> Format.eprintf "%s\n" (Stdlib.string_of_int i);
    | Str_val s -> Format.eprintf "%s\n" (s);
    | Error_val s -> Format.eprintf "%s\n" (s);

  Hashtbl.iter pp_stack_expr gamma_val; *)
  (* let e5 = (Plus(Sub(Sub(Num(30), Num(2)),Num(20)),Num(40))) in
  let e6 = (Sub(Num(2),Num(30))) in
  let e7 =  (Cat_e(Str("2"),Plus(Num(1),Num(2)))) in
  (* mini_eval_expr_string e5; *)
  mini_eval_expr_string e6;
  mini_eval_expr_string e7 *)
