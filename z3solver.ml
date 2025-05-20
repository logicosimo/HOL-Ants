(* ========================================================================= *)
(* Interface HOL Light with the Z3 solver.                                   *)
(* ========================================================================= *)

needs "z3base.ml";;

(* ------------------------------------------------------------------------- *)
(* Constructor for variables.                                                *)
(* ------------------------------------------------------------------------- *)

let z3_of_var ctx tm =
  let nm,ty = dest_var tm in
  if ty = bool_ty
  then Zzz.Boolean.mk_const_s ctx nm
  else failwith ("z3_of_var: Unsupported type: "^string_of_type ty);;

(* ------------------------------------------------------------------------- *)
(* Net-based translation infrastructure from HOL terms to Z3 expressions.    *)
(* ------------------------------------------------------------------------- *)

let z3_of_term_net : (Zzz.context -> term-> Zzz.Expr.expr) net ref =
  ref empty_net;;

let z3_of_term ctx tm =
  if is_var tm then z3_of_var ctx tm else
  let l = lookup tm !z3_of_term_net in
  try tryfind (fun f -> f ctx tm) l
  with Failure s -> failwith "z3_of_term";;

(* ------------------------------------------------------------------------- *)
(* Translation of boolean expressions.                                       *)
(* ------------------------------------------------------------------------- *)

let z3_of_neg ctx tm =
  Zzz.Boolean.mk_not ctx (z3_of_term ctx (dest_neg tm));;

let z3_of_conj ctx tm =
  let p,q = dest_conj tm in
  Zzz.Boolean.mk_and ctx [z3_of_term ctx p; z3_of_term ctx q];;

let z3_of_disj ctx tm =
  let p,q = dest_disj tm in
  Zzz.Boolean.mk_or ctx [z3_of_term ctx p; z3_of_term ctx q];;

let z3_of_imp ctx tm =
  let p,q = dest_imp tm in
  Zzz.Boolean.mk_implies ctx (z3_of_term ctx p) (z3_of_term ctx q);;

(* ------------------------------------------------------------------------- *)
(* Default net.                                                              *)
(* ------------------------------------------------------------------------- *)

z3_of_term_net := itlist (enter [])
  [`~p`,z3_of_neg;
   `p /\ q`, z3_of_conj;
   `p \/ q`, z3_of_disj;
   `p ==> q`, z3_of_imp]
  empty_net;;

(* ------------------------------------------------------------------------- *)
(* Example: checking the satisfiability of the boolean formula
     ¬((p ∨ q → r) ∧ ¬(q ∨ r))
   in Z3.                                                                    *)
(* ------------------------------------------------------------------------- *)

let ctx = Zzz.mk_context [];;
let tm = `~((p \/ q ==> r) /\ ~(q \/ r))`;;
let expr = z3_of_term ctx tm;;
Zzz.Expr.to_string expr;;
solve ctx [expr];;

`a:num < b` |> z3_of_term ctx;;

(* ------------------------------------------------------------------------- *)
(* Create enumerative sort for positions.                                    *)
(* ------------------------------------------------------------------------- *)

let sort_position = Zzz.Enumeration.mk_sort_s ctx "position"
                      ["P0"; "P1"; "P2"; "P3"; "P4"];;

let [z3p0; z3p1; z3p2; z3p3; z3p4] =
  Zzz.Enumeration.get_consts sort_position;;
