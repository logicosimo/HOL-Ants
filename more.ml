(* ------------------------------------------------------------------------- *)
(* Vectors of nums.                                                          *)
(* ------------------------------------------------------------------------- *)

let vetor_add_num = new_definition
  `vetor_add_num (x:num^N) (y:num^N) : num^N = lambda i. x$i + y$i`;;

let VECTOR_ADD_NUM_COMPONENT = prove
 (`!x y:num^N i. vetor_add_num x y$i = x$i + y$i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vetor_add_num] THEN
  CLAIM_TAC "@k. k1 k2 eq" `?k. 1 <= k /\ k <= dimindex(:N) /\
                                (!x:num^N. x$i = x$k)` THENL
  [MATCH_ACCEPT_TAC FINITE_INDEX_INRANGE;
   ASM_SIMP_TAC[LAMBDA_BETA]]);;

(* ------------------------------------------------------------------------- *)
(* Sums of nums.                                                             *)
(* ------------------------------------------------------------------------- *)

let NSUM_3 = prove
 (`!f. nsum (1..3) f = f 1 + f 2 + f 3`,
  GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV NUMSEG_CONV) THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmata for reducing a system description in FOL.                         *)
(* ------------------------------------------------------------------------- *)

let IN_NEW_SYSTEM_ALT = prove
 (`!sys sys':N system.
     sys' IN NEW_SYSTEM sys <=>
     STI sys' = NEW_STI sys /\
     !i. 1 <= i /\ i <= dimindex (:N)
         ==> ANT sys'$i IN NEW_ANT (STI sys) (ANT sys$i)`,
  REWRITE_TAC[FORALL_SYSTEM_THM; NEW_SYSTEM; ANT; STI] THEN
  SET_TAC[SYSTEM_INJECTIVITY]);;

let DELTA_STI = new_definition
  `DELTA_STI (ant:(position#bool)^N):num^3 =
   lambda p. CARD {i | 1 <= i /\ i <= dimindex(:N) /\ FST (ant$i) = PP p}`;;

let DELTA_STI_COMPONENT = prove
 (`!sys:N system p.
      1 <= p /\ p <= 3
      ==> DELTA_STI (ant:(position#bool)^N)$p =
          nsum (1..dimindex(:N)) (\i. if FST (ant$i) = PP p then 1 else 0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DELTA_STI] THEN
  CLAIM_TAC "lt" `p <= dimindex(:3)` THENL
  [ASM_REWRITE_TAC[DIMINDEX_3];
   ASM_SIMP_TAC[LAMBDA_BETA] THEN POP_ASSUM (K ALL_TAC)] THEN
  CHEAT_TAC);;

let DELTA_STI_COMPONENT_ALT =
  let ptm = `p:num` in
  let pth = SPEC_ALL DELTA_STI_COMPONENT in
  let f ntm = GEN_ALL (INST[ntm,ptm] pth) in
  let pth = end_itlist CONJ (map f [`1`; `2`; `3`]) in
  CONV_RULE NUM_REDUCE_CONV pth;;

let NEW_STI_ALT = prove
 (`!sti':num^3 sys:N system.
     NEW_STI sys = vetor_add_num (STI sys) (DELTA_STI (ANT sys))`,
  REWRITE_TAC[FORALL_SYSTEM_THM; NEW_STI; STI; ANT] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REWRITE_TAC[VECTOR_ADD_NUM_COMPONENT] THEN
  ASM_SIMP_TAC[DELTA_STI_COMPONENT; LE_REFL; ARITH_LE; ARITH_LT; PP]);;

let NEW_ANT_ALT = prove
 (`!sti a a'.
     a' IN NEW_ANT sti a <=>
     (FST a = P1 ==> FST a' = (if SND a then P4 else P0) /\ SND a' = SND a) /\
     (FST a = P2 ==> FST a' = (if SND a then P3 else P0) /\ SND a' = SND a) /\
     (FST a = P3 ==> FST a' = (if SND a then P4 else P2) /\ SND a' = SND a) /\
     (FST a = P0 ==> (FST a' = P1 \/ FST a' = P2) /\ SND a') /\
     (FST a = P0 /\ FST a' = P1 ==> sti$2 <= sti$1) /\
     (FST a = P0 /\ FST a' = P2 ==> sti$1 <= sti$2) /\
     (FST a = P4 ==> (FST a' = P1 \/ FST a' = P3) /\ ~SND a') /\
     (FST a = P4 /\ FST a' = P1 ==> sti$3 <= sti$1) /\
     (FST a = P4 /\ FST a' = P3 ==> sti$1 <= sti$3)`,
 GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; NEW_ANT] THEN
 GEN_REWRITE_TAC I [FORALL_POSITION_THM] THEN
 REWRITE_TAC [IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM; PAIR_EQ;
              POSITION_DISTINCTNESS] THEN
 REWRITE_TAC[EXISTS_POSITION_THM; POSITION_DISTINCTNESS] THEN
 REWRITE_TAC[FORALL_POSITION_THM; POSITION_DISTINCTNESS] THEN
 MESON_TAC[]);;
