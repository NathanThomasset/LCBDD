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
  let t = Array.make max_int (-1) in
  t.(zero) <- zero;
  t.(one) <- one;
  let rec aux j =
    if j == zero then one
    else if j == one then zero
    else if (t.(j) == -1) then let new_low, new_high = aux (low tabT j), aux (high tabT j) in
      let new_id = make tabT tabH (var tabT j) new_low new_high in
      t.(j)<- new_id;
      t.(new_id)<- new_id;
      new_id
    else t.(j)
  in aux i;;

let apply tabT tabH op bdd1 bdd2 =
  let t = Array.make_matrix max_int max_int (-1) in
  let rec aux f1 f2 =
    match op with
      Et -> for i = 0 to max_int-1 do t.(zero).(i)<- zero; t.(i).(zero)<-zero done; t.(one).(one)<-one;
      |Ou -> for i = 0 to max_int-1 do t.(one).(i)<- one; t.(i).(one)<-one done; t.(zero).(zero)<-zero;
      |Impl -> for i = 0 to max_int-1 do t.(zero).(i)<- one; t.(i).(one)<- one done;
      |Equiv -> t.(zero).(zero)<-one; t.(one).(one)<-one; t.(zero).(one)<-zero; t.(one).(zero)<-zero;
    if (t.(f1).(f2) == -1) then begin
      if (isZero f1) then begin match op with (* case 0 op f2 *)
        Et -> let new_id = zero in t.(f1).(f2)<- zero;
        |Ou -> let new_id = f2 in t.(f1).(f2)<- f2;
        |Impl-> let new_id = one in t.(f1).(f2)<- one;
        |Equiv -> let new_id = apply_neg tabT tabH f2 in t.(f1).(f2)<- new_id;
      end
      else begin
        if (isOne f1) then begin match op with (* case 1 op f2 *)
          Et -> let new_id = f2 in t.(f1).(f2)<- f2;
          |Ou -> let new_id = one in t.(f1).(f2)<- one;
          |Impl-> let new_id = f2 in t.(f1).(f2)<- f2;
          |Equiv -> let new_id = f1 in t.(f1).(f2)<- f1;
        end
        else begin
          if (isZero f2) then begin match op with (* case f1 op 0 *)
            Et -> let new_id = zero in t.(f1).(f2)<- zero;
            |Ou -> let new_id = f1 in t.(f1).(f2)<- f1;
            |Impl-> let new_id = apply_neg tabT tabH f1 in t.(f1).(f2)<- new_id;
            |Equiv -> let new_id = apply_neg tabT tabH f1 in t.(f1).(f2)<- new_id;
          end
          else begin
            if (isOne f2) then begin match op with (* case f1 op 1 *)
              Et -> let new_id = f1 in t.(f1).(f2)<- f1;
              |Ou -> let new_id = one in t.(f1).(f2)<- one;
              |Impl-> let new_id = one in t.(f1).(f2)<- one;
              |Equiv -> let new_id = f1 in t.(f1).(f2)<- f1;
            end
            else begin
              let var1, var2 = var tabT f1, var tabT f2 in
              if (var1 == var2) then begin (* same variable so we act according to proposition 5 *)
                let new_low, new_high = aux (low tabT f1) (low tabT f2), aux (high tabT f1) (high tabT f2) in
                let new_id = make tabT tabH var1 new_low new_high in
                t.(f1).(f2)<- new_id;
              end
              else begin
                if (var1 < var2) then begin
                  let new_low, new_high = aux (low tabT f1) f2, aux (high tabT f1) f2 in
                  let new_id = make tabT tabH var1 new_low new_high in
                  t.(f1).(f2)<- new_id;
                end
                else begin
                  let new_low, new_high = aux f1 (low tabT f2), aux f1 (high tabT f2) in
                  let new_id = make tabT tabH var2 new_low new_high in
                  t.(f1).(f2)<- new_id;
                end
              end
            end
          end
        end
      end
    end
    new_id
    else t.(f1).(f2)
  in aux bdd1 bdd2;;

(* creates in tableT tablet and tableH tableh the ROBDD corresponding to the given formula *)
let rec build tablet tableh formula =
  match formula with
    false -> zero
    |true -> one
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
