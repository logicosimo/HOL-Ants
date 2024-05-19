(* ========================================================================= *)
(* Formiche Miscellanea                                                      *)
(* ========================================================================= *)

let PAIR_EXTENSION = prove
 (`!p q:A#B. p = q <=> FST p = FST q /\ SND p = SND q`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

let LAMBDA_3 = prove
 (`(lambda) f : A^3 = vector[f 1; f 2; f 3]`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC LAMBDA_BETA THEN
  REWRITE_TAC[DIMINDEX_3] THEN NUM_REDUCE_TAC);;

let list_of_seq_ALT = prove
 (`!n s. list_of_seq s (SUC n) = CONS (s 0:A) (list_of_seq (s o SUC) n)`,
  INDUCT_TAC THENL [REWRITE_TAC[list_of_seq; APPEND]; ALL_TAC] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [list_of_seq] THEN
  FIRST_ASSUM (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THEN
  REWRITE_TAC[APPEND] THEN AP_TERM_TAC THEN REWRITE_TAC[list_of_seq; o_THM]);;

let list_of_vector = new_definition
  `list_of_vector (v:A^N) = list_of_seq (\i. v$SUC i) (dimindex(:N))`;;

let LENGTH_LIST_OF_VECTOR = prove
 (`!x:A^N. LENGTH (list_of_vector x) = dimindex(:N)`,
  REWRITE_TAC[list_of_vector; LENGTH_LIST_OF_SEQ]);;

let EL_LIST_OF_VECTOR = prove
 (`!v:A^N i. i < dimindex(:N) ==> EL i (list_of_vector v) = v$(SUC i)`,
  SIMP_TAC [list_of_vector; EL_LIST_OF_SEQ]);;

g `!v:A^N. vector(list_of_vector v) = v`;;
e (GEN_TAC THEN REWRITE_TAC[CART_EQ]);;
e (INTRO_TAC "!i; i1 i2");;
e (REWRITE_TAC[vector]);;
e (ASM_SIMP_TAC[LAMBDA_BETA]);;
e (IMP_REWRITE_TAC[EL_LIST_OF_VECTOR]);;
e CONJ_TAC;;
e (AP_TERM_TAC THEN ASM_ARITH_TAC);;
e ASM_ARITH_TAC;;
let VECTOR_LIST_OF_VECTOR = top_thm();;

g `!n s l. LENGTH l = n /\ (!i. i < n ==> s i : A = EL i l)
           ==> list_of_seq s n = l`;;
e INDUCT_TAC;;
 e (REWRITE_TAC[LENGTH_EQ_NIL; FORALL_UNWIND_THM2; IMP_CONJ; list_of_seq]);;
e (INTRO_TAC "!s l");;
e (STRUCT_CASES_TAC (ISPEC `l:A list` (cases "list")) THEN
   REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ]);;
e (INTRO_TAC "len el");;
e (REWRITE_TAC[list_of_seq_ALT; CONS_11]);;
e CONJ_TAC;;
 e (REMOVE_THEN "el" (MP_TAC o SPEC `0`));;
 e (REWRITE_TAC[EL; HD; LT_0]);;
e (FIRST_X_ASSUM MATCH_MP_TAC);;
e (ASM_REWRITE_TAC[o_THM]);;
e (INTRO_TAC "!i; i");;
e (REMOVE_THEN "el" (MP_TAC o SPEC `SUC i`));;
e (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]);;
e (REWRITE_TAC[EL; TL]);;
let LIST_OF_SEQ_UNIQUE = top_thm();;

g `!l. LENGTH l = dimindex(:N) ==> list_of_vector (vector l:A^N) = l`;;
e (INTRO_TAC "!l; l");;
e (REWRITE_TAC[list_of_vector]);;
e (MATCH_MP_TAC LIST_OF_SEQ_UNIQUE);;
e (ASM_REWRITE_TAC[vector]);;
e (INTRO_TAC "!i; i");;
e (SUBGOAL_THEN `1 <= SUC i /\ SUC i <= dimindex(:N)` (fun th -> SIMP_TAC[LAMBDA_BETA; th]));;
 e ASM_ARITH_TAC;;
e (AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;
let LIST_OF_VECTOR_VECTOR = top_thm();;

let LISTCOLLECT = new_definition
  `LISTCOLLECT k u =
   {l:A list | LENGTH l = k /\ !i. i < k ==> EL i l IN u i}`;;

let IN_LISTCOLLECT = prove
 (`!l. l IN LISTCOLLECT k u <=>
       LENGTH l = k /\ !i. i < k ==> EL i l IN u i`,
  REWRITE_TAC[LISTCOLLECT; IN_ELIM_THM]);;

let FORALL_IN_LISTCOLLECT = prove
 (`!P k u. (!l. l IN LISTCOLLECT k u ==> P l) <=>
           (!l. LENGTH l = k /\ (!i. i < k ==> EL i l IN u i) ==> P l)`,
  REWRITE_TAC[LISTCOLLECT; FORALL_IN_GSPEC]);;

let LISTCOLLECT_CLAUSES = prove
 (`(!u. LISTCOLLECT 0 u = {[]:A list}) /\
   (!u. LISTCOLLECT (SUC k) u =
        SETBIND (\x:A. IMAGE (CONS x) (LISTCOLLECT k (u o SUC))) (u 0))`,
  REWRITE_TAC[LISTCOLLECT] THEN CONJ_TAC THENL
  [REWRITE_TAC[LENGTH_EQ_NIL; ARITH_RULE `!i. ~(i < 0)`] THEN SET_TAC[];
   ALL_TAC] THEN
  GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; FORALL_IN_SETBIND] THEN
  CONJ_TAC THENL
  [INTRO_TAC "!l; len l" THEN REWRITE_TAC[IN_SETBIND] THEN
   EXISTS_TAC `EL 0 l:A` THEN
   CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `TL l:A list` THEN
   CONJ_TAC THENL
   [REMOVE_THEN "len" MP_TAC THEN
    STRUCT_CASES_TAC (ISPEC `l:A list` (cases "list")) THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; CONS_11; EL; HD; TL; IN_ELIM_THM];
    ALL_TAC] THEN
   POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN
   STRUCT_CASES_TAC (ISPEC `l:A list` (cases "list")) THEN
   REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; TL; o_THM] THEN
   INTRO_TAC "el len" THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
   INTRO_TAC "!i; i" THEN FIRST_X_ASSUM (MP_TAC o SPEC `SUC i`) THEN
   ASM_REWRITE_TAC[LT_SUC; EL; TL];
   ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM;
              FORALL_IN_IMAGE; FORALL_IN_GSPEC; o_THM] THEN
  INTRO_TAC "!x; x; ![l]; len; el" THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; LENGTH] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[EL; HD; TL; LT_SUC]);;

g `(!u. LISTCOLLECT 0 u = {[]:A list}) /\
   (!k u. LISTCOLLECT (SUC k) u =
          SETBIND (\l. IMAGE (\x. CONS x l) (u 0:A->bool))
                  (LISTCOLLECT k (u o SUC)))`;;
e (CONJ_TAC THEN REPEAT GEN_TAC THEN
   MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET] THEN
   REWRITE_TAC[FORALL_IN_LISTCOLLECT; FORALL_IN_INSERT; NOT_IN_EMPTY]);;
 e (REWRITE_TAC[LENGTH_EQ_NIL; IMP_CONJ; FORALL_UNWIND_THM2]);;
 e (REWRITE_TAC[IN_INSERT; IN_LISTCOLLECT; LENGTH; LT]);;
e CONJ_TAC;;
 e (INTRO_TAC "![l]; len el");;
 e (REWRITE_TAC[IN_SETBIND]);;
 e (EXISTS_TAC `TL l:A list`);;
 e CONJ_TAC;;
  e (REWRITE_TAC[IN_LISTCOLLECT]);;
  e (SUBGOAL_THEN `~(l:A list = [])`
       (fun th -> REWRITE_TAC[MATCH_MP LENGTH_TL th]));;
   e (DISCH_THEN SUBST_VAR_TAC);;
   e (REMOVE_THEN "len" MP_TAC);;
   e (REWRITE_TAC[LENGTH; NOT_SUC]);;
  e (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]);;
  e (INTRO_TAC "!i; i" THEN REMOVE_THEN "el" (MP_TAC o SPEC `SUC i`));;
  e (ASM_REWRITE_TAC[LT_SUC; EL; o_THM]);;
 e (REWRITE_TAC[IN_IMAGE]);;
 e (EXISTS_TAC `HD l:A`);;
 e (POP_ASSUM_LIST (MP_TAC o end_itlist CONJ));;
 e (STRUCT_CASES_TAC (ISPEC `l:A list` (cases "list")));;
  e (REWRITE_TAC[NOT_CONS_NIL; LENGTH; NOT_SUC]);;
 e (REWRITE_TAC[CONS_11; HD; TL; LENGTH; SUC_INJ]);;
 e (INTRO_TAC "el len");;
 e (REMOVE_THEN "el" (MP_TAC o SPEC `0`));;
 e (REWRITE_TAC[EL; HD; LT_0]);;
(* <== *)
e (REWRITE_TAC[FORALL_IN_SETBIND; IMP_CONJ; RIGHT_FORALL_IMP_THM;
               FORALL_IN_LISTCOLLECT; FORALL_IN_IMAGE; o_THM]);;
e (INTRO_TAC "![l]; len; el; !x; x");;
e (ASM_REWRITE_TAC[IN_LISTCOLLECT; LENGTH; SUC_INJ]);;
e INDUCT_TAC;;
 e (ASM_REWRITE_TAC[EL; HD]);;
e (ASM_REWRITE_TAC[LT_SUC; EL; TL]);;
let LISTCOLLECT_CLAUSES = top_thm();;
