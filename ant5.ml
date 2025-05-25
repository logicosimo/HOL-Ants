(* ========================================================================= *)
(* Example with 5 ants which uses bintreevects.                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* ((!i. 1 <= i /\ i <= NUMERAL n ==> P i) <=>
 (!i. 1 <= i /\ i <= n ==> P (NUMERAL i))) /\
((!i. 1 <= i /\ i <= _0 ==> P i) <=> T) /\
(!n. (!i. 1 <= i /\ i <= BIT0 n ==> P i) <=>
     (!i. 1 <= i /\ i <= n ==> P (BIT0 i)) /\
     (!i. 1 <= i /\ i <= n ==> P (BIT1 i))) /\ *)

let FORALL_LE_BIN = prove
 (`(!n. (!i. i < NUMERAL n ==> P i) <=> (!i. i < n ==> P (NUMERAL i))) /\
   ((!i. i <= _0 ==> P i) <=> P _0) /\
   ((!i. i <= BIT0 n ==> P i) <=>
    (!i. i <= n ==> P (BIT0 i)) /\ (!i. i < n ==> P (BIT1 i))) /\
   ((!i. i <= BIT1 n ==> P i) <=>
    (!i. i <= n ==> P (BIT0 i)) /\ (!i. i <= n ==> P (BIT1 i)))`,
  CONJ_TAC THENL [REWRITE_TAC[NUMERAL]; ALL_TAC] THEN
  CONV_TAC (ONCE_DEPTH_CONV BITS_ELIM_CONV) THEN
  REWRITE_TAC[FORALL_LE_BINARY]);;

let FORALL_LT_BIN = prove
 (`(!n. (!i. i < NUMERAL n ==> P i) <=> (!i. i < n ==> P (NUMERAL i))) /\
   (!i. i < _0 ==> P i) /\
   (!n. (!i. i < BIT0 n ==> P i) <=>
        (!i. i < n ==> P (BIT0 i)) /\ (!i. i < n ==> P (BIT1 i))) /\
   (!n. (!i. i < BIT1 n ==> P i) <=>
        (!i. i <= n ==> P (BIT0 i)) /\ (!i. i < n ==> P (BIT1 i)))`,
  CONJ_TAC THENL [REWRITE_TAC[NUMERAL]; ALL_TAC] THEN
  CONV_TAC (ONCE_DEPTH_CONV BITS_ELIM_CONV) THEN
  REWRITE_TAC[FORALL_LT_BINARY]);;

let FORALL_N_THM = prove
 (`!P. (!i. 1 <= i /\ i <= n ==> P i) <=> (!i. i < n ==> P (SUC i))`,
  GEN_TAC THEN EQ_TAC THENL
  [MESON_TAC[ARITH_RULE `!n i. 1 <= SUC i /\ SUC i <= n <=> i < n`];
   MESON_TAC[ARITH_RULE `1 <= i /\ i <= n
                         ==> SUC (PRE i) = i /\ PRE i < n`]]);;

let NUM_VECTOR_ADD_COMPONENT0 = prove
 (`!x y:num^N i. vetor_add_num x y $. i = x $. i + y $. i`,
  REWRITE_TAC[component0; VECTOR_ADD_NUM_COMPONENT]);;

let NUM_VECTOR_ADD_ARITH = prove
 (`(!x y:num. vetor_add_num (vecx x) (vecx y) = vecx (x + y)) /\
   (!x x' y y':num^N.
      vetor_add_num (vec0 x y) (vec0 x' y') =
      vec0 (vetor_add_num x x') (vetor_add_num y y')) /\
   (!x x' y y':num^N a a'.
      vetor_add_num (vec1 x y a) (vec1 x' y' a') =
      vec1 (vetor_add_num x x') (vetor_add_num y y') (a + a'))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ0; NUM_VECTOR_ADD_COMPONENT0;
     DIMINDEX_1; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  MATCH_MP_TAC FORALL_BINARY_THM THEN
  SIMP_TAC[VECX_COMPONENT0; VEC0_COMPONENT0_BINARY;
    VEC1_COMPONENT0_BINARY; NUM_VECTOR_ADD_COMPONENT0; NUM_LT_BINARY] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Sums.                                                                     *)
(* ------------------------------------------------------------------------- *)

(* let NSUM_NUMSEG_LT = prove
 (`(!f. nsum {i | i < 0} f = 0) /\
   (!f. nsum {i | i < 1} f = f 0) /\
   (!n f. nsum {i | i < n + 1} f = f n + nsum {i | i < n} f) /\
   (!n f. nsum {i | i < 2 * n} f =
          nsum {i | i < n} (\i. f(2 * i)) +
          nsum {i | i < n} (\i. f(2 * i + 1)))`,
  MP_TAC (MATCH_MP ITERATE_NUMSEG_LT MONOIDAL_ADD) THEN
  REWRITE_TAC[GSYM nsum; NEUTRAL_ADD]);;

let NSUM_NUMSEG = prove
 (`nsum (m..n) f = nsum {i | i < n+1-m} (\i. f (i+m))`,

;;
NSUM_OFFSET
NSUM_INJECTION
NSUM_IMAGE
NSUM_EQ_GENERAL_INVERSES
NSUM_EQ_GENERAL
NSUM_BIJECTION
;;
 search[`nsum a b = nsum c d`];; *)


(* ------------------------------------------------------------------------- *)
(* Invariant.                                                                *)
(* ------------------------------------------------------------------------- *)

g `!sys sys':5 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_THM;
               IN_NEW_SYSTEM_ALT; STI; ANT;
               NEW_ANT_ALT; NEW_STI_ALT; ANT; STI; DELTA_STI_COMPONENT_ALT]);;
e DIMINDEX_TAC;;
e (REWRITE_TAC[FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN; ARITH_ZERO]);;
e NUM_REDUCE_TAC;;
e VECTOR_REDUCE_TAC;;
e (REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;
e (REWRITE_TAC[CART_EQ]);;
e DIMINDEX_TAC;;
e (REWRITE_TAC[FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN; ARITH_ZERO]);;
e (REWRITE_TAC[VECTOR_ADD_NUM_COMPONENT]);;
e NUM_REDUCE_TAC;;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT]);;
e DIMINDEX_TAC;;


e VECTOR_REDUCE_TAC;;



e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT]);;

e (REWRITE_TAC[NEW_ANT_ALT; NEW_STI_ALT; ANT; STI; DELTA_STI_COMPONENT_ALT]);;
e VECTOR_REDUCE_TAC;;

(* e (REWRITE_TAC[NEW_ANT_ALT]);; *)


e (REWRITE_TAC[INJECTIVE_ALT])




e (REWRITE_TAC[CART_EQ; DIMINDEX_1; FORALL_1; DIMINDEX_3; FORALL_3; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_VECTOR_1; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_3; VECTOR_1]);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_3; DIMINDEX_1; NSUM_1; VECTOR_3; VECTOR_1; PP]);;
e (REWRITE_TAC[MAX]);;
let _,ptm = top_goal();;