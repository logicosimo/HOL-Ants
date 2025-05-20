(* ========================================================================= *)
(* Z3 whith HOL Light: "Hello World" experiment.                             *)
(* ========================================================================= *)

needs "z3base.ml";;

(* ------------------------------------------------------------------------- *)
(* Simple example of an OCaml function that translates an HOL term that
   is a boolean formula into a Z3 expresion.                                 *)
(* ------------------------------------------------------------------------- *)

let z3_of_term ctx =
  let rec z3_of_term tm =
    if is_neg tm then
      Zzz.Boolean.mk_not ctx (z3_of_term (dest_neg tm))
    else if is_conj tm then
      let p,q = dest_conj tm
      in Zzz.Boolean.mk_and ctx [z3_of_term p; z3_of_term q]
    else if is_disj tm then
      let p,q = dest_disj tm
      in Zzz.Boolean.mk_or ctx [z3_of_term p; z3_of_term q]
    else if is_imp tm then
      let p,q = dest_imp tm
      in Zzz.Boolean.mk_implies ctx (z3_of_term p) (z3_of_term q)
    else if (is_var tm && type_of tm = `:bool`) then
      let symbol,ty = dest_var tm
      in Zzz.Boolean.mk_const_s ctx symbol
    else
      failwith "Parsing of HOL Light formula failed"
  in
  z3_of_term;;

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
