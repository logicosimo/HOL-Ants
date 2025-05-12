(* ========================================================================= *)
(* Experiments with Z3.                                                      *)
(* ========================================================================= *)

needs "z3base.ml";;

(* ------------------------------------------------------------------------- *)
(* Additional HOL Light helper functions.                                    *)
(* ------------------------------------------------------------------------- *)

let dest_quantifier tm =
  if is_forall tm
  then let v,b = dest_forall tm in v,b,true
  else if is_exists tm
  then let v,b = dest_exists tm in v,b,false
  else failwith "dest_quantifier";;

let is_quantifier = can dest_quantifier;;

(* Test: *)
assert (dest_quantifier `?n:num. b` = (`n:num`, `b:bool`, false));;

(* ------------------------------------------------------------------------- *)
(* Constructors for quantifiers.                                             *)
(* ------------------------------------------------------------------------- *)

let z3_simple_mk_forall ctx vars body =
  let quant = Zzz.Quantifier.mk_forall_const ctx vars body
                None [] [] None None in
  Zzz.Quantifier.expr_of_quantifier quant;;

let z3_simple_mk_exists ctx vars body =
  let quant = Zzz.Quantifier.mk_exists_const ctx vars body
                None [] [] None None in
  Zzz.Quantifier.expr_of_quantifier quant;;

(* ------------------------------------------------------------------------- *)
(* Create enumerative sort for positions.                                    *)
(* ------------------------------------------------------------------------- *)

let ctx = Zzz.mk_context [];;

let sort_position = Zzz.Enumeration.mk_sort_s ctx "position"
                      ["P0"; "P1"; "P2"; "P3"; "P4"];;
                      
let [z3p0; z3p1; z3p2; z3p3; z3p4] =
  Zzz.Enumeration.get_consts sort_position;;

(* ------------------------------------------------------------------------- *)
(* Translates an HOL term into a Z3 expresion.
   Handles a fragment barely sufficient for accepting goals generated from
   the ANTS formalization.                                                   *)
(* ------------------------------------------------------------------------- *)

let z3_of_term =
  let num_ty = `:num`
  and position_ty = `:position`
  and zexpr = Zzz.Arithmetic.Integer.mk_numeral_i ctx 0 in
  let rec z3_of_term tm =
    if is_const tm then
      match name_of tm with
      | "T" -> Zzz.Boolean.mk_true ctx
      | "F" -> Zzz.Boolean.mk_false ctx
      | "P0" -> z3p0
      | "P1" -> z3p1
      | "P2" -> z3p2
      | "P3" -> z3p3
      | "P4" -> z3p4
      | nm -> failwith ("Unknown constant: "^nm)
    else if is_var tm then
      let nm,ty = dest_var tm in
      if ty = bool_ty then Zzz.Boolean.mk_const_s ctx nm
      else if ty = num_ty then Zzz.Arithmetic.Integer.mk_const_s ctx nm
      else if ty = position_ty then Zzz.Expr.mk_const_s ctx nm sort_position
      else failwith ("Variable of unhandled type: "^nm)
    else if is_eq tm then
      let x,y = dest_eq tm in
      let e = z3_of_term x
      and f = z3_of_term y in
      if type_of x = bool_ty
      then Zzz.Boolean.mk_iff ctx e f
      else Zzz.Boolean.mk_eq ctx e f
    else if is_neg tm then
      Zzz.Boolean.mk_not ctx (z3_of_term (dest_neg tm))
    else if is_conj tm then
      let p,q = dest_conj tm in
      Zzz.Boolean.mk_and ctx [z3_of_term p; z3_of_term q]
    else if is_disj tm then
      let p,q = dest_disj tm in
      Zzz.Boolean.mk_or ctx [z3_of_term p; z3_of_term q]
    else if is_imp tm then
      let p,q = dest_imp tm in
      Zzz.Boolean.mk_implies ctx (z3_of_term p) (z3_of_term q)
    else if is_cond tm then
      let b,(s,t) = dest_cond tm in
      Zzz.Boolean.mk_ite ctx (z3_of_term b) (z3_of_term s) (z3_of_term t)
    else if is_quantifier tm then
      let vtm,btm,universal = dest_quantifier tm in
      let vexpr = z3_of_term vtm
      and bexpr = z3_of_term btm in
      let bexpr = if type_of vtm = num_ty
                  then let lexpr = Zzz.Arithmetic.mk_le ctx zexpr vexpr in
                       if universal
                       then Zzz.Boolean.mk_implies ctx lexpr bexpr
                       else Zzz.Boolean.mk_and ctx [lexpr; bexpr]
                  else bexpr in
      if universal
      then z3_simple_mk_forall ctx [vexpr] bexpr
      else z3_simple_mk_exists ctx [vexpr] bexpr
    else if is_binary "<=" tm then
      let x,y = dest_binary "<=" tm in
      Zzz.Arithmetic.mk_ge ctx (z3_of_term y) (z3_of_term x)
    else if is_binary ">" tm then
      let x,y = dest_binary ">" tm in
      Zzz.Arithmetic.mk_gt ctx (z3_of_term x) (z3_of_term y)
    else if is_numeral tm then
      Zzz.Arithmetic.Integer.mk_numeral_i ctx (dest_small_numeral tm)
    else if is_binary "+" tm then
      let x,y = dest_binary "+" tm in
      Zzz.Arithmetic.mk_add ctx [z3_of_term x; z3_of_term y]
    else
      let s = string_of_term tm in
      failwith ("Parsing of HOL Light formula failed: "^s)
  in
  z3_of_term;;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

let ctx = Zzz.mk_context [];;

let z3show tm = Zzz.Expr.to_string (z3_of_term ctx tm);;

assert (z3show `b:num` = "b");;
assert (z3show `n:num` = "n");;
assert (z3show `b <=> c` = "(= b c)");;
assert (z3show `m:num = n` = "(= m n)");;
assert (z3show `b /\ c` = "(and b c)");;
assert (z3show `m + n:num` = "(+ m n)");;
assert (z3show `T /\ F` = "(and true false)");;
assert (z3show `!b. b` = "(forall ((b Bool)) b)");;
assert (z3show `?b. b` = "(exists ((b Bool)) b)");;
assert (z3show `!n:num. b` = "(forall ((n Int)) (=> (<= 0 n) b))");;
assert (z3show `?n:num. b` = "(exists ((n Int)) (and (<= 0 n) b))");;

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
let (_,thtm) = top_goal();;

let expr = z3_of_term ctx thtm;;

let thtm = tm |> REWRITE_CONV[MAX] |> concl |> rand;;
time (solve ctx) [mk_neg (z3_of_term ctx thtm)];;

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(*                        HIC SUNT LEONES                                    *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)


z3show `b <=> c`;;
solve ctx [`!b. b \/ ~b`];;
solve ctx [`?b. b`];;
solve ctx [`b:bool`];;
solve ctx [mk_neg tm];;

let simtm =
`System (vector[(p1,d1); (p2,d2); (p3,d3)])
        (vector[s1; s2; s3]) : 3 system
 IN ITER 10 (SETBIND NEW_SYSTEM)
           {System (vector[(P0,T); (P1,F); (P2,F)])
                   (vector[0; 0; 0]) : 3 system}`
|> TOP_SWEEP_CONV num_CONV THENC
   REWRITE_CONV[ITER; IN_SETBIND; IN_INSERT; NOT_IN_EMPTY] THENC
   TOP_DEPTH_CONV UNWIND_CONV THENC
   REWRITE_CONV[IN_NEW_SYSTEM_ALT; EXISTS_SYSTEM_THM;
                STI; ANT; NEW_STI_ALT; DELTA_STI_COMPONENT_ALT;
                NEW_ANT_ALT;
                VECTOR_ADD_NUM_COMPONENT;
                DIMINDEX_3; FORALL_3; EXISTS_VECTOR_3; EXISTS_PAIR_THM;
                NSUM_3; PP;
                CART_EQ; VECTOR_3;
                POSITION_DISTINCTNESS]
|> concl |> rand;;

solve ctx [simtm];;
solve ctx [];;


solve ctx [`0 <= 0`];;
solve ctx [`0 <= 0`];;
z3show `0 <= 0`;;
z3show `~(0 <= 0)`;;
z3show `(x:num <= y)`;;
solve ctx [`~(0 <= 0)`];;
solve ctx [`(x:num <= y)`];;


solve ctx [`0 <= 1`];;
solve ctx [`1 <= 0`];;
solve ctx [`0 <= 0`];;
solve ctx [`1 > 0`];;
solve ctx [`0 > 1`];;
solve ctx [`0 > 0`];;
