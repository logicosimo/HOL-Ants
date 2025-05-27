(* ========================================================================= *)
(* Reasoning and computing with binary expansions of natural numbers.        *)
(*                                                                           *)
(* (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018                  *)
(* (c) Copyright, Marco Maggesi 2025                                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Conversion that elimiates every occurrence of `NUMERAL`, `BIT0`,          *)
(* `BIT1`, `_0` that are not part of a well-formed numeral.                  *)
(* ------------------------------------------------------------------------- *)

let BITS_ELIM_CONV : conv =
  let NUMERAL_pth = prove(`m = n <=> NUMERAL m = n`,REWRITE_TAC[NUMERAL])
  and ZERO_pth = GSYM (REWRITE_CONV[NUMERAL] `0`)
  and BIT0_pth,BIT1_pth = CONJ_PAIR
   (prove(`(m = n <=> BIT0 m = 2 * n) /\
           (m = n <=> BIT1 m = 2 * n + 1)`,
    CONJ_TAC THEN GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [BIT0; BIT1] THEN
    ARITH_TAC))
  and mvar,nvar = `m:num`,`n:num` in
  let rec BITS_ELIM_CONV : conv =
    fun tm -> match tm with
      Const("_0",_) -> ZERO_pth
    | Var _ | Const _ -> REFL tm
    | Comb(Const("NUMERAL",_),mtm) ->
        if is_numeral tm then REFL tm else
        let th = BITS_ELIM_CONV mtm in
        EQ_MP (INST[mtm,mvar;rand(concl th),nvar] NUMERAL_pth) th
    | Comb(Const("BIT0",_),mtm) ->
        let th = BITS_ELIM_CONV mtm in
        EQ_MP (INST [mtm,mvar;rand(concl th),nvar] BIT0_pth) th
    | Comb(Const("BIT1",_),mtm) ->
        let th = BITS_ELIM_CONV mtm in
        EQ_MP (INST [mtm,mvar;rand(concl th),nvar] BIT1_pth) th
    | Comb _ -> COMB_CONV BITS_ELIM_CONV tm
    | Abs _ -> ABS_CONV BITS_ELIM_CONV tm in
  BITS_ELIM_CONV;;

(* ------------------------------------------------------------------------- *)
(* Basic arithmetic operations on binary numbers.                            *)
(* ------------------------------------------------------------------------- *)

let NUM_EQ_BINARY = prove
 (`(!n. 2 * n = 0 <=> n = 0) /\
   (!n. ~(n + 1 = 0)) /\
   (!n. 0 = 2 * n <=> 0 = n) /\
   (!n. ~(0 = n + 1)) /\
   (!m n. 2 * m = 2 * n <=> m = n) /\
   (!m n. ~(2 * m = 2 * n + 1)) /\
   (!m n. ~(2 * m + 1 = 2 * n)) /\
   (!m n. 2 * m + 1 = 2 * n + 1 <=> m = n)`,
  REWRITE_TAC[CONV_RULE BITS_ELIM_CONV ARITH_EQ] THEN ARITH_TAC);;

let NUM_LE_BINARY = prove
 (`(!n. 0 <= n) /\
   (!n. 2 * n <= 0 <=> n <= 0) /\
   (!n. ~(n + 1 <= 0)) /\
   (!m n. 2 * m <= 2 * n <=> m <= n) /\
   (!m n. 2 * m <= 2 * n + 1 <=> m <= n) /\
   (!m n. 2 * m + 1 <= 2 * n <=> m < n) /\
   (!m n. 2 * m + 1 <= 2 * n + 1 <=> m <= n)`,
  REWRITE_TAC[CONV_RULE BITS_ELIM_CONV ARITH_LE] THEN ARITH_TAC);;

let NUM_LT_BINARY = prove
 (`(!n. ~(n < 0)) /\
   (!n. 0 < 2 * n <=> 0 < n) /\
   (!n. 0 < n + 1) /\
   (!m n. 2 * m < 2 * n <=> m < n) /\
   (!m n. 2 * m < 2 * n + 1 <=> m <= n) /\
   (!m n. 2 * m + 1 < 2 * n <=> m < n) /\
   (!m n. 2 * m + 1 < 2 * n + 1 <=> m < n)`,
  REWRITE_TAC[CONV_RULE BITS_ELIM_CONV ARITH_LT] THEN ARITH_TAC);;

let NUM_DIV2_BINARY = prove
 (`0 DIV 2 = 0 /\
   (!i. (2 * i) DIV 2 = i) /\
   (!i. (2 * i + 1) DIV 2 = i)`,
  ARITH_TAC);;

let NUM_MOD2_BINARY = prove
 (`0 MOD 2 = 0 /\
   (!i. (2 * i) MOD 2 = 0) /\
   (!i. (2 * i + 1) MOD 2 = 1)`,
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  REWRITE_TAC[MOD_MULT] THEN NUM_REDUCE_TAC);;

let NUM_EVEN_BINARY = prove
 (`EVEN 0 /\
   (!n. EVEN (2 * n)) /\
   (!n. ~EVEN (2 * n + 1))`,
  REWRITE_TAC[EVEN_MOD; NUM_MOD2_BINARY] THEN NUM_REDUCE_TAC);;

let NUM_ODD_BINARY = prove
 (`~ODD 0 /\
   (!n. ~ODD (2 * n)) /\
   (!n. ODD (2 * n + 1))`,
  REWRITE_TAC[ODD_MOD; NUM_MOD2_BINARY] THEN NUM_REDUCE_TAC);;

let NUM_BINARY_CASES_STRONG = prove
 (`!n. n = 0 \/ (?m. 0 < m /\ n = 2 * m) \/ (?m. n = 2 * m + 1)`,
  MATCH_MP_TAC BINARY_INDUCT THEN REWRITE_TAC[NUM_EQ_BINARY] THEN
  GEN_TAC THEN DISCH_THEN STRUCT_CASES_TAC THEN REWRITE_TAC[NUM_EQ_BINARY] THEN
  ASM_MESON_TAC[ARITH_RULE `(0 < m ==> 0 < 2 * m) /\ 0 < 2 * m + 1`]);;

let NUM_CASES_BINARY = prove
 (`!n. n = 0 \/ (?m. n = 2 * m) \/ (?m. n = 2 * m + 1)`,
  MESON_TAC[NUM_BINARY_CASES_STRONG]);;

let EXISTS_BINARY_THM = prove
 (`!P. (?n. P n) <=> P 0 \/ (?n. 0 < n /\ P (2*n)) \/ (?n. P (2*n+1))`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC (SPEC `n:num` NUM_BINARY_CASES_STRONG) THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN ASM_MESON_TAC[]);;

let FORALL_BINARY_THM = prove
 (`!P. (!n. P n) <=> P 0 /\ (!n. 0 < n ==> P (2*n)) /\ (!n. P (2*n+1))`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  STRIP_ASSUME_TAC (SPEC `n:num` NUM_BINARY_CASES_STRONG) THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN ASM_MESON_TAC[]);;

let FORALL_LT_BINARY = prove
 (`(!i. i < 0 ==> P i) /\
   ((!i. i < 1 ==> P i) <=> P 0) /\
   ((!i. i < 2 * n ==> P i) <=>
    (!i. i < n ==> P (2 * i)) /\ (!i. i < n ==> P (2 * i + 1))) /\
   ((!i. i < 2 * n + 1 ==> P i) <=>
    (!i. i <= n ==> P (2 * i)) /\ (!i. i < n ==> P (2 * i + 1)))`,
  REWRITE_TAC[ARITH_RULE `~(i < 0) /\ (i < 1 <=> i = 0)`;
              FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[GSYM FORALL_AND_THM] THEN CONJ_TAC THENL
  [EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   STRIP_TAC THEN GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `i:num` NUM_CASES_BINARY) THEN
   REWRITE_TAC[NUM_LT_BINARY] THEN ASM_SIMP_TAC[] THEN
   POP_ASSUM (MP_TAC o SPEC `0`) THEN NUM_REDUCE_TAC THEN SIMP_TAC[];
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   STRIP_TAC THEN GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `i:num` NUM_CASES_BINARY) THEN
   REWRITE_TAC[NUM_LT_BINARY] THEN ASM_SIMP_TAC[] THEN
   POP_ASSUM (MP_TAC o SPEC `0`) THEN NUM_REDUCE_TAC THEN SIMP_TAC[LE_0]]);;

let FORALL_LE_BINARY = prove
 (`((!i. i <= 0 ==> P i) <=> P 0) /\
   ((!i. i <= 2 * n ==> P i) <=>
    (!i. i <= n ==> P (2 * i)) /\ (!i. i < n ==> P (2 * i + 1))) /\
   ((!i. i <= 2 * n + 1 ==> P i) <=>
    (!i. i <= n ==> P (2 * i)) /\ (!i. i <= n ==> P (2 * i + 1)))`,
  REWRITE_TAC[ARITH_RULE `(i <= 0 <=> i = 0)`; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[GSYM FORALL_AND_THM] THEN CONJ_TAC THENL
  [EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   STRIP_TAC THEN GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `i:num` NUM_CASES_BINARY) THEN
   REWRITE_TAC[NUM_LE_BINARY] THEN ASM_SIMP_TAC[] THEN
   POP_ASSUM (MP_TAC o SPEC `0`) THEN NUM_REDUCE_TAC THEN SIMP_TAC[LE_0];
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   STRIP_TAC THEN GEN_TAC THEN
   STRUCT_CASES_TAC (SPEC `i:num` NUM_CASES_BINARY) THEN
   REWRITE_TAC[NUM_LE_BINARY] THEN ASM_SIMP_TAC[] THEN
   POP_ASSUM (MP_TAC o SPEC `0`) THEN NUM_REDUCE_TAC THEN SIMP_TAC[LE_0]]);;

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

(* ------------------------------------------------------------------------- *)
(* Binary representation of numeric segments.                                *)
(* ------------------------------------------------------------------------- *)

let NUMSEG_LT_BINARY = prove
 (`{i | i < 0} = {} /\
   {i | i < 1} = {0} /\
   {i | i < n + 1} = n INSERT {i | i < n} /\
   {i | i < 2 * n} = IMAGE (\i. 2 * i) {i | i < n} UNION
                     IMAGE (\i. 2 * i + 1) {i | i < n}`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC;
    FORALL_IN_IMAGE; FORALL_IN_INSERT; FORALL_IN_UNION] THEN
  REWRITE_TAC[NOT_IN_EMPTY; IN_INSERT; IN_UNION; IN_ELIM_THM; IN_IMAGE] THEN
  REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN MATCH_MP_TAC BINARY_INDUCT THEN
  REWRITE_TAC[NUM_LT_BINARY; NUM_EQ_BINARY; UNWIND_THM1]);;

let NUMSEG_LT_BINARY_ALT = prove
 (`{i | i < 0} = {} /\
   {i | i < 2 * n} = IMAGE (\i. 2 * i) {i | i < n} UNION
                     IMAGE (\i. 2 * i + 1) {i | i < n} /\
   {i | i < 2 * n + 1} = IMAGE (\i. 2 * i) {i | i <= n} UNION
                         IMAGE (\i. 2 * i + 1) {i | i < n}`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC;
    FORALL_IN_IMAGE; FORALL_IN_INSERT; FORALL_IN_UNION] THEN
  REWRITE_TAC[NOT_IN_EMPTY; IN_INSERT; IN_UNION; IN_ELIM_THM; IN_IMAGE] THEN
  REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN MATCH_MP_TAC BINARY_INDUCT THEN
  REWRITE_TAC[NUM_EQ_BINARY; UNWIND_THM1] THEN ARITH_TAC);;

let NUMSEG_LE_BINARY_ALT = prove
 (`{i | i <= 0} = {0} /\
   {i | i <= 2 * n} = IMAGE (\i. 2 * i) {i | i <= n} UNION
                      IMAGE (\i. 2 * i + 1) {i | i < n} /\
   {i | i <= 2 * n + 1} = IMAGE (\i. 2 * i) {i | i <= n} UNION
                          IMAGE (\i. 2 * i + 1) {i | i <= n}`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC;
    FORALL_IN_IMAGE; FORALL_IN_INSERT; FORALL_IN_UNION] THEN
  REWRITE_TAC[NOT_IN_EMPTY; IN_INSERT; IN_UNION; IN_ELIM_THM; IN_IMAGE] THEN
  REPEAT CONJ_TAC THEN TRY ARITH_TAC THEN MATCH_MP_TAC BINARY_INDUCT THEN
  REWRITE_TAC[NUM_EQ_BINARY; UNWIND_THM1] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Iteration over numeric segments.                                          *)
(* ------------------------------------------------------------------------- *)

let ITERATE_NUMSEG_LT = prove
 (`!op. monoidal op
        ==> (!f. iterate op {i | i < 0} f = neutral op:A) /\
            (!f. iterate op {i | i < 1} f = f 0) /\
            (!n f. iterate op {i | i < n + 1} f =
                   op (f n) (iterate op {i | i < n} f)) /\
            (!n f. iterate op {i | i < 2 * n} f =
                   op (iterate op {i | i < n} (\i. f(2 * i)))
                      (iterate op {i | i < n} (\i. f(2 * i + 1))))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[NUMSEG_LT_BINARY] THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; FINITE_EMPTY; FINITE_NUMSEG_LT; NOT_IN_EMPTY;
               MONOIDAL_AC; IN_ELIM_THM; LT_REFL] THEN
  GEN_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (\i. 2 * i) {i | i < n})
                         (IMAGE (\i. 2 * i + 1) {i | i < n})`
     (fun th ->
        ASM_SIMP_TAC[ITERATE_CLAUSES; ITERATE_UNION; ITERATE_IMAGE;
          FINITE_EMPTY; FINITE_NUMSEG_LT; FINITE_UNION; FINITE_IMAGE;
          NOT_IN_EMPTY; NUM_EQ_BINARY; o_DEF; MONOIDAL_AC; th]) THEN
  REWRITE_TAC[IN_DISJOINT; NOT_EXISTS_THM; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `j:num` THEN STRUCT_CASES_TAC (SPEC `j:num` NUM_CASES_BINARY) THEN
  REWRITE_TAC[NUM_EQ_BINARY]);;

let SUM_NUMSEG_LT = prove
 (`(!f. sum {i | i < 0} f = &0) /\
   (!f. sum {i | i < 1} f = f 0) /\
   (!n f. sum {i | i < n + 1} f = f n + sum {i | i < n} f) /\
   (!n f. sum {i | i < 2 * n} f =
          sum {i | i < n} (\i. f(2 * i)) +
          sum {i | i < n} (\i. f(2 * i + 1)))`,
  MP_TAC (MATCH_MP ITERATE_NUMSEG_LT MONOIDAL_REAL_ADD) THEN
  REWRITE_TAC[GSYM sum; NEUTRAL_REAL_ADD]);;
