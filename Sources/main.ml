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
  else if (l == h) then l
  else let u = add tablet i l h in
    insert tableh i l h u;
    u;;

let apply_neg tabT tabH i =
  let t = Array.make MAXINT -1 in
  t.(zero) = zero;
  t.(one) = one;
  let rec aux j =
    if j == zero then one
    else if j == one then zero
    else if t.(j)==-1 then let new_low, new_high = aux (low tabT j), aux (high tabT j) in
      let new_id = make tabT tabH (var j) new_low new_high in
      t.(j)<- new_id;
      t.(new_id)<- new_id;
      new_id
    else t.(j)
  in aux i;;

let apply tabT tabH i op bdd1 bdd2 =
  let t = Array.make MAXINT -1 in
  t.(0) <- False;
  t.(1) <- False;
  let rec aux j = match op with
    | Et ->
    | Ou -> apply tabT tabH i Et (apply_neg bdd1) (apply_neg bdd2)
    | Impl -> apply tabT tabH i Ou (apply_neg bdd1) bdd2
    | Equiv -> apply tabT tabH (apply tabT tabH i Impl bdd1 bdd2) Impl bdd2 bdd1
  in aux i
    ;;

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

(* tests if the formula represented by its ROBDD is valid *)
let rec valid tablet id = isOne id;;

(* tests if the formula represented by its ROBDD can be satisfied *)
let rec sat tablet id = not(valid (apply_neg id));;

(* returns, if it exists, a valuation that satisfies the formula represented by its BDD *)
