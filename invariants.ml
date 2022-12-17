open Printf

(* Définitions de terme, test et programme *)
type term = 
  | Const of int
  | Var of int
  | Add of term * term
  | Mult of term * term

type test = 
  | Equals of term * term
  | LessThan of term * term

let tt = Equals (Const 0, Const 0)
let ff = LessThan (Const 0, Const 0)
 
type program = {nvars : int; 
                inits : term list; 
                mods : term list; 
                loopcond : test; 
                assertion : test}

let x n = "x" ^ string_of_int n

            
(* Question 1 ----------------------------------------------------------------------------*)
(*str_of_term : term -> string*)
let rec str_of_term t =  
  match t with 
  |Var a -> "x" ^ string_of_int a ^ ""
  |Const a -> string_of_int a
  |Add(a1,a2) -> "(+" ^ " " ^ str_of_term a1 ^ " " ^ str_of_term a2 ^ ")"
  |Mult(a1,a2) -> "(*" ^ " " ^ str_of_term a1 ^ " " ^ str_of_term a2 ^ ")"

(*str_of_term : term -> string*)
let str_of_test t = 
  match t with 
  |Equals(term1, term2) -> "(= " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ ")"
  |LessThan(term1, term2) -> "(< " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ ")"

(*string_repeat : string -> int -> string*)
let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s) 


(* Question 2 ----------------------------------------------------------------------------*)
(*str_condition : term list -> string*)
let str_condition l = 
  let rec str_of_term_with_space term reste= 
    " " ^ str_of_term term ^ reste
  in
  "(Inv" ^ (List.fold_right str_of_term_with_space l "") ^ ")"

  
(* Question 3 ----------------------------------------------------------------------------*)
(*str_condition : term list -> string*)
let str_assert s = "(assert " ^ s ^ ")"

(*str_assert_forall : int -> string -> string*)
let str_assert_forall n s = 
  let rec str_assert_forall_aux n_init n= 
    if n > n_init
    then "" 
    else 
      let espace = if n = n_init then "" else " " in
      "(" ^ (str_of_term (Var(n))) ^ " Int)" ^ espace ^ (str_assert_forall_aux n_init (n+1))

  in str_assert ("(forall (" ^ str_assert_forall_aux n 1 ^ ") (" ^ s ^ "))")


(* Question 4 ----------------------------------------------------------------------------*)
(*list_var : int -> term list -> term list*)
let rec list_var n l=
  if n = 0 then l
  else if n > 0 then list_var (n-1) (List.cons (Var n) l)
  else failwith "n negatif"
;;             

(*smtlib_of_wa : program -> string*)
let smtlib_of_wa p = 
  let declare_invariant n =
    "; synthèse d'invariant de programme\n"
    ^"; on déclare le symbole non interprété de relation Invar\n"
    ^"(declare-fun Invar (" ^ string_repeat "Int " n ^  ") Bool)" in
  let loop_condition p =
    "; la relation Invar est un invariant de boucle\n"

    ^ str_assert_forall p.nvars ( "(=> (and " ^ 
    str_condition (list_var p.nvars [])
    ^ " " ^
    str_of_test p.loopcond ^ ") " ^ str_condition p.mods ^ ")" )in

  let initial_condition p =
    "; la relation Invar est vraie initialement\n"
    ^str_assert (str_condition p.inits) in
  let assertion_condition p =
    "; l'assertion finale est vérifiée\n"
    ^ str_assert_forall p.nvars ("(=> (and " ^ 
    str_condition (list_var p.nvars l)
    ^ " " ^
    str_of_test p.loopcond ^ ") " ^ str_of_test p.assertion ^ ")" )  in
  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in
  String.concat "\n" [declare_invariant p.nvars;
                      loop_condition p;
                      initial_condition p;
                      assertion_condition p;
                      call_solver]

let p1 = {nvars = 2;
          inits = [(Const 0) ; (Const 0)];
          mods = [Add ((Var 1), (Const 1)); Add ((Var 2), (Const 3))];
          loopcond = LessThan ((Var 1),(Const 3));
          assertion = Equals ((Var 2),(Const 9))}


let () = Printf.printf "%s" (smtlib_of_wa p1)

(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMTLIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. Ajoutez dans la variable p2 ci-dessous au moins
   un autre programme test, et vérifiez qu'il donne un fichier SMTLIB
   de la forme attendue. *)

let p2 = None (* À compléter *) 
