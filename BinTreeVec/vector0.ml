(* ========================================================================= *)
(* Zero-based indexed vectors.                                               *)
(*                                                                           *)
(* Vectors in HOL Light uses one-based indexes by default.  This file        *)
(* provides some basic constants and theorems to work with HOL vectors       *)
(* using zero-indexes instead.                                               *)
(*                                                                           *)
(* This file can be loaded in the core version of HOL Light.  See file       *)
(* real_btvector0.ml for theorems and procedures specific to real vectors    *)
(* and matrices, that requires the the library of multivariate calculus.     *)
(*                                                                           *)
(* (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018                  *)
(* (c) Copyright, Marco Maggesi 2025                                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Miscellanea on vectors and matrices.                                      *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_GT_0 = prove
 (`!s:N->bool. 0 < dimindex s`,
  GEN_TAC THEN SUBGOAL_THEN `1 <= dimindex (s:N->bool)` MP_TAC THENL
  [REWRITE_TAC[DIMINDEX_GE_1]; ARITH_TAC]);;

let VECTOR_1_GEN = prove
 (`!v:A^1 i. v$i = v$1`,
  GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN
    `?k. 1 <= k /\ k <= dimindex (:1) /\ (!x:A^1. x$i = x$k)`
    (DESTRUCT_TAC "@k. k1 + eq") THENL
  [MATCH_ACCEPT_TAC FINITE_INDEX_INRANGE; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_1] THEN DISCH_TAC THEN
  SUBGOAL_THEN `k = 1` SUBST_VAR_TAC THENL
  [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The zero-based indexing operator is denoted `$.` (dollar dot).            *)
(* The binder for zero-based vectors is denote `lambda0`.                    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("$.",get_infix_status "$");;
parse_as_binder "lambda0";;

let component0 = new_definition
  `v:A^N $. i = v$(i+1) `;;

let lambda0 = new_definition
  `(lambda0) g:A^N = (lambda) (\i. g (i - 1))`;;

let LAMBDA0_BETA = prove
 (`!i. i < dimindex (:B) ==> ((lambda0) g:A^B)$.i = g i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lambda0; component0] THEN
  TRANS_TAC EQ_TRANS `(\i. g (i - 1):A) (i + 1)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC LAMBDA_BETA THEN ASM_ARITH_TAC;
   REWRITE_TAC[] THEN AP_TERM_TAC THEN ARITH_TAC]);;

let FINITE_COMPONENT0_INRANGE = prove
 (`!i. ?k. k < dimindex(:N) /\ (!x:A^N. x$.i = x$.k)`,
  GEN_TAC THEN REWRITE_TAC[component0] THEN
  SUBGOAL_THEN
    `?k. 1 <= k /\ k <= dimindex(:N) /\ (!x:A^N. x$(i+1) = x$k)`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC FINITE_INDEX_INRANGE;
   POP_ASSUM (fun th -> ONCE_REWRITE_TAC[th])] THEN
  EXISTS_TAC `k - 1` THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= k ==> k - 1 + 1 = k`] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Extensional equality using zero-based indexing.                           *)
(* ------------------------------------------------------------------------- *)

let CART_EQ0 = prove
 (`!x y:A^N. x = y <=> (!i. i < dimindex(:N) ==> x$.i = y$.i)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[component0; CART_EQ] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `i - 1`) THEN
  SUBGOAL_THEN `i - 1 + 1 = i` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let CART_EQ0_FULL = prove
 (`!x y:A^N. x = y <=> (!i. x$.i = y$.i)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN SIMP_TAC[CART_EQ0]);;

(* ------------------------------------------------------------------------- *)
(* Conversion between one-based and zero-based notation.                     *)
(* ------------------------------------------------------------------------- *)

let LAMBDA_EQ_LAMBDA0 = prove
 (`!f:num-> A. (lambda) f : A^N = lambda0 i. f (i + 1)`,
  GEN_TAC THEN REWRITE_TAC[lambda0; CART_EQ] THEN
  SIMP_TAC[LAMBDA_BETA; ARITH_RULE `!i. 1 <= i ==> i - 1 + 1 = i`]);;

let INDEX_EQ_COMPONENT0 = prove
 (`!x:A^N i. 1 <= i ==> x$i = x$.(i-1)`,
  GEN_TAC THEN REWRITE_TAC[component0] THEN
  SIMP_TAC[ARITH_RULE `1 <= i ==> (i-1)+1 = i`]);;

(* ------------------------------------------------------------------------- *)
(* Special case in dimension 1.                                              *)
(* ------------------------------------------------------------------------- *)

let VECTOR0_1_GEN = prove
 (`!v:A^1 i. v$.i = v$.0`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[component0] THEN
  ONCE_REWRITE_TAC[VECTOR_1_GEN] THEN REFL_TAC);;
