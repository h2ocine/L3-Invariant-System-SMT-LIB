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
  |Var a -> x a
  |Const a -> string_of_int a
  |Add(a1,a2) -> "(+ " ^ str_of_term a1 ^ " " ^ str_of_term a2 ^ ")"
  |Mult(a1,a2) -> "(* " ^ str_of_term a1 ^ " " ^ str_of_term a2 ^ ")"

(*str_of_term : term -> string*)
let str_of_test t = 
  match t with 
  |Equals(term1, term2) -> "(= " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ ")"
  |LessThan(term1, term2) -> "(< " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ ")"

(* Question 2 ----------------------------------------------------------------------------*)
(*str_condition : term list -> string*)
(*str_condition : term list -> string*)
(*str confition doit retourner "(Invar string_term1 string_term2 ...)" *)
(*donc on utilise la fonction List.fold (qu'on explique dans le RENDU) avec comme arguments : 
    -une fonction qui concatène un espace avec un terme et un autre string (qui representera 
    la reste du resultat de la fonction),
    -la liste des terms, 
    -puis le caractère null comme initilisation du string
*)
let str_condition l = 
  "(Invar" 
   ^ 
  (List.fold_right (fun term rest -> "  " ^ str_of_term term ^ rest) l "") 
   ^ 
  ")"

  
(* Question 3 ----------------------------------------------------------------------------*)
(*str_assert : string -> string*)
(*ajoute des parenthèse et le mot assert dans un string*)
let str_assert s = "(assert " ^ s ^ ")"

(*str_assert_forall : int -> string -> string*)
(*
  cette fonction renvoie un string sous la forme : assert (forall ((x1 Int) (x2 Int)) (< x1 x2))) 
  on utilise la fonction str_assert pour les premier parenthèse et le mot assert.
  on concatène les deuxieme, troisieme parenthèses, "forall", le string s donné en entré avec des parenthèse,
  ainsi que le resultat de la fonction str_assert_forall_aux n 1 qu'on expliquera juste après.
*)
let str_assert_forall n s = 
  let rec str_assert_forall_aux n_init n= 
  (*
      n_init doit être initialiser a n (le nombre de term), n doit être initaliser a 1
      a chaque occuration n augemente juqu'a arrivé a n_init 
      cette fonction est plus détailé dans le RENDU
  *) 
    if n > n_init
    then "" 
    else 
      let espace = if n = n_init then "" else " " in (*le caractère espace ne doit être present lors de la derniere occurance (quand n = n_init)*)
      "(" ^ (str_of_term (Var(n))) ^ " Int)" ^ espace ^ (str_assert_forall_aux n_init (n+1))

  in str_assert ("(forall (" ^ str_assert_forall_aux n 1 ^ ") (" ^ s ^ "))")


(* Question 4 ----------------------------------------------------------------------------*)

(*list_var : int -> term list -> term list*)
(* une fonction qui retourne une liste de n variables (type Var a)*)
let rec list_var n l=
  if n = 0 then l
  else if n > 0 then list_var (n-1) (List.cons (Var n) l)
  else failwith "n negatif"
;;


(*str_of_inverse_test : test -> string*)
(* prend un type test en parametre et inverse le signe de test et renvoie un string de la formule*)
(*utile pour tester l'assertion finale, le cas de sortie de la boucle la formule de test est inversée*)
let str_of_inverse_test s = 
  match s with
  |Equals(term1, term2) -> "(!= " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ ")"
  |LessThan(term1, term2) -> "(>= " ^ (str_of_term term1) ^ " " ^ (str_of_term term2) ^ ")"
;;

(*smtlib_of_wa : program -> string*)
let smtlib_of_wa p = 
  let declare_invariant n =
    "; synthèse d'invariant de programme\n"
    ^"; on déclare le symbole non interprété de relation Invar\n"
    ^"(declare-fun Invar (" ^ string_repeat "Int " n ^  ") Bool)" in
  let loop_condition p =
    "; la relation Invar est un invariant de boucle\n"

    ^ str_assert_forall p.nvars (*lister toutes les variables *)
    (*   la conjonction entre la condition que les variable sont dans l'invariant (Invar x1 ... xk)
     * et la condition de boucle (p.loopcond) implique que les resultats des operations de boucle (p.mods) restent dans l'invariant   *)
    ( "=> (and " ^ str_condition (list_var p.nvars []) 
    ^ " " ^
    str_of_test p.loopcond ^ ") " ^ str_condition p.mods )in

  let initial_condition p =
    "; la relation Invar est vraie initialement\n"
    (*la fonction str_condition modelise que p.inits (la combinaison initiale ) est
     * dans l'invariant, on la met donc dans une assertion pour la verifier *)
    ^str_assert (str_condition p.inits) in
  let assertion_condition p =
    "; l'assertion finale est vérifiée\n"
    (*appliquer assert sur l'implication qui dit (si toute les variables sont dans l'invariant(str_condition) et la condition de boucle 
    * est inversé pour sortir de la boucle (str_of_inverse_test) implique que l'assertion finale est verifiée (p.assertion)*)
    ^ str_assert_forall p.nvars ("=> (and " ^ 
    str_condition (list_var p.nvars [])
    ^ " " ^
    str_of_inverse_test p.loopcond ^ ") " ^ str_of_test p.assertion )  in
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


(* let () = Printf.printf "%s" (smtlib_of_wa p1) *)

(* Question 5---------------------------------------------------------------------------------- *)

let p2 = {
  nvars = 3;
  inits = [(Const 0) ; (Const 10); (Const 0)];
  mods = [Add ((Var 1), (Const 2)); Add ((Var 2), (Var 3)); Add ((Var 3), (Const 1))];
  loopcond = LessThan ((Var 1),(Const 10));
  assertion = LessThan ((Const 15),(Var 2))
} 

let () = Printf.printf "%s" (smtlib_of_wa p2)

 (* programme p2 
  int x=0;
  int y=10;
  int z=0;
  while(x<10){
    x=x+2; 
    y=y+z;
    z=z+1;
  }
  assert(y>15)*)


(* programme p3 
  int x=0;
  int y=19;
  int z=0;
  while(x<y){
    x=x+6; 
    y=y+z;
    z=z+1;
  }
  assert(y=30)*)

  let p3 = {
    nvars = 3;
    inits = [(Const 0) ; (Const 19); (Const 0)];
    mods = [Add ((Var 1), (Const 6)); Add ((Var 2), (Var 3)); Add ((Var 3), (Const 1))];
    loopcond = LessThan ((Var 1),(Var 2));
    assertion = Equals ((Var 2), (Const 30))
  } 
  