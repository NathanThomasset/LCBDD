(* Example of file when using the compiles mode *)

open Lib
open Formulas
open Prop
open Bdd

(* Pretty-printer for formulas, to be used with compiled mode *)
let print_formula fm = print_prop_formula fm; print_newline();;

let f = << ( 1 <=> 2 ) /\ ( 3 <=> 4 )>>;;
print_formula f;;

let taille = 100 in
(* initialization of tables*)
let t = init_t taille in
let ht = init_ht taille in
(* Adding a node for variable x_1, with low son 0 and high son 1 *)
let u = add t 1 0 1 in
  insert ht 1 0 1 u;

  (* Adding a node for variable x_2, with low son 1 and high son u *)
  let v = add t 2 1 u in
    insert ht 2 1 u v;
    debug_print_t t;
    debug_print_h ht 10 10;
    print_t t v "bla.dot";;

(* creates, if necessary, a node with variable i, low l and high h in tableT tablet as well as tableH tableh
  returns the new node index *)
let make tablet tableh i l h =
  if (member tableh i l h) then lookup tableh i l h
  else let u = add tablet i l h in
    insert tableh i l h u;
    u;;

(* creates in tableT tablet and tableH tableh the ROBDD corresponding to the given formula *)
let rec build tablet tableh formula =
  match formula with
    False -> zero
    |True -> one
    |Atom(P(i)) -> let u = make tablet tableh i zero one in u
    |Not(f) -> let u = build tablet tableh f in apply_neg tablet tableh u
    |And(f,g) -> let u = build tablet tableh f and v = build tablet tableh g
                 in apply tablet tableh Et u v
    |Or(f,g) -> let u = build tablet tableh f and v = build tablet tableh g
                in apply tablet tableh Ou u v
    |Imp(f,g) -> let u = build tablet tableh f and v = build tablet tableh g
                 in apply tablet tableh Impl u v
    |Iff(f,g) -> let u = build tablet tableh f and v = build tablet tableh g
                 in apply tablet tableh Equiv u v;;
