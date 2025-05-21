(* ========================================================================= *)
(* Experiments with HOL and Z3 with our system of foraging ants.             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Introduce a Z3 enumerative sort for positions.                            *)
(* ------------------------------------------------------------------------- *)

let ctx = Zzz.mk_context [];;

let sort_position = Zzz.Enumeration.mk_sort_s ctx "position"
                      ["P0"; "P1"; "P2"; "P3"; "P4"];;

let [z3p0; z3p1; z3p2; z3p3; z3p4] =
  Zzz.Enumeration.get_consts sort_position;;

z3_of_var_translators :=
  let z3_pos_var ctx nm = Zzz.Expr.mk_const_s ctx nm sort_position in
  (`:position`, z3_pos_var) :: basic_z3_of_var_translators;;

z3_of_term_net :=
  itlist (fun (ptm,c) -> enter [] (ptm, mk_z3_const ptm (K c)))
  [`P0`,z3p0;
   `P1`,z3p1;
   `P2`,z3p2;
   `P3`,z3p3;
   `P4`,z3p4]
  basic_z3_of_term_net;;

(* Example: *)
let tm = `P0 = p`;;
let expr = z3_of_term ctx tm;;
Zzz.Expr.to_string expr;;
solve ctx [expr];;

(* ------------------------------------------------------------------------- *)
(* Prove the invariant for a system with 3 ants.                             *)
(* ------------------------------------------------------------------------- *)

g `!sys sys':3 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
e (REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_3]);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_3; NSUM_3; VECTOR_3; PP]);;
e (REWRITE_TAC[MAX]);;
(* ~1 min *)
time e (Z3_TAC ctx);;
top_goal();;

axioms();;

(* ------------------------------------------------------------------------- *)
(* Prove the invariant for a system with 2 ants.                             *)
(* ------------------------------------------------------------------------- *)

g `!sys sys':2 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
e (REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; DIMINDEX_2; FORALL_2; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_VECTOR_2; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_3; VECTOR_2]);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_2; NSUM_2; VECTOR_2; PP]);;
e (REWRITE_TAC[MAX]);;
(* ~1 min *)
time e (Z3_TAC ctx);;
top_goal();;

let asl,w = top_goal();;
assert (asl = []);;
solve ctx [z3_of_term ctx (mk_neg w)];;
z3_prove ctx [] w;;

let expr = z3_of_term ctx (mk_neg w);;
let s = Zzz.Solver.mk_simple_solver ctx;;
let ret = Zzz.Solver.check s [expr];;




time e (Z3_TAC ctx);;
(* top_goal();; *)

(* ------------------------------------------------------------------------- *)
(* Prove the invariant for a system with 4 ants.                             *)
(* ------------------------------------------------------------------------- *)


e (REWRITE_TAC[]);;



e (REWRITE_TAC[CART_EQ; DIMINDEX_4; FORALL_4; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_4; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_4]);;



e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_4; NSUM_4; VECTOR_4; PP]);;
e (REWRITE_TAC[MAX]);;
(* ~1 min *)
time e (Z3_TAC ctx);;
top_goal();;





g `!sys sys':4 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
e (REWRITE_TAC[CART_EQ; DIMINDEX_4; FORALL_4; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_4; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_4]);;



e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_4; NSUM_4; VECTOR_4; PP]);;
e (REWRITE_TAC[MAX]);;
(* ~1 min *)
time e (Z3_TAC ctx);;
top_goal();;
