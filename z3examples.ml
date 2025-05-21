(* ========================================================================= *)
(* Simple tests and examples for z3_of_term of z3solver.ml.                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Example: checking the satisfiability of the boolean formula
     ¬((p ∨ q → r) ∧ ¬(q ∨ r))
   in Z3.                                                                    *)
(* ------------------------------------------------------------------------- *)

let ctx = Zzz.mk_context [];;

(* Example: *)
let tm = `~((p \/ q ==> r) /\ ~(q \/ r))`;;
let expr = z3_of_term ctx tm;;
Zzz.Expr.to_string expr;;
solve ctx [expr];;

(* ------------------------------------------------------------------------- *)
(* Further simple exmaples.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Example: *)
let tm = `T = a /\ b = F`;;
let expr = z3_of_term ctx tm;;
Zzz.Expr.to_string expr;;
solve ctx [expr];;

(* Example: *)
let tm = `!x. x = a \/ x = F`;;
let expr = z3_of_term ctx tm;;
Zzz.Expr.to_string expr;;
solve ctx [expr];;

(* Example: *)
let tm = `if a = b then a = T else b = F`;;
let expr = z3_of_term ctx tm;;
Zzz.Expr.to_string expr;;
solve ctx [expr];;

(* Example: *)
let tm = `if a = b then a = 0 else b = 1`;;
let expr = z3_of_term ctx tm;;
Zzz.Expr.to_string expr;;
solve ctx [expr];;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

let z3show tm = Zzz.Expr.to_string (z3_of_term ctx tm);;

z3_of_term ctx `m:num`;;
z3_of_term ctx `m + n`;;
z3_of_add ctx `m + n`;;

assert (z3show `b:num` = "b");;
assert (z3show `n:num` = "n");;
assert (z3show `b <=> c` = "(= b c)");;
assert (z3show `m:num = n` = "(= m n)");;
assert (z3show `b /\ c` = "(and b c)");;
assert (z3show `m + n:num` = "(+ m n)");;
assert (z3show `m > n:num` = "(> m n)");;
assert (z3show `m <= n:num` = "(>= n m)");;   (* Z3 API BUG *)
assert (z3show `T /\ F` = "(and true false)");;
assert (z3show `!b. b` = "(forall ((b Bool)) b)");;
assert (z3show `?b. b` = "(exists ((b Bool)) b)");;
assert (z3show `!n:num. b` = "(forall ((n Int)) (=> (<= 0 n) b))");;
assert (z3show `?n:num. b` = "(exists ((n Int)) (and (<= 0 n) b))");;
