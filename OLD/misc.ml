(* ========================================================================= *)
(* Miscellanea.                                                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Rewriting rules for computations.                                         *)
(* ------------------------------------------------------------------------- *)

let get_ants_thl,add_ants_thl =
  let thl:thm list ref = ref [] in
  let get_ants_thl() = !thl
  and add_ants_thl l = thl := l @ !thl in
  get_ants_thl,add_ants_thl;;

(* ------------------------------------------------------------------------- *)
(* Counting elements.                                                        *)
(* ------------------------------------------------------------------------- *)

let COUNT = define
  `(!s P:A->bool. COUNT NONE s P = NONE) /\
   (!acc s P:A->bool.
      COUNT (SOME acc) s P =
      if FINITE s
      then SOME (acc + CARD {x | x | x IN s /\ P x})
      else NONE)`;;

let CARD_EQ_COUNT = prove
 (`!s P:A->bool.
     FINITE s
     ==> CARD {x:A | x IN s /\ P x} = GETOPTION (COUNT (SOME 0) s P)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[COUNT; ADD; GETOPTION]);;

let COUNT_CLAUSES = prove
 (`(!s P:A->bool. COUNT NONE s P = NONE) /\
   (!acc P:A->bool. COUNT acc {} P = acc) /\
   (!acc x:A s P. COUNT (SOME acc) (x INSERT s) P =
                  COUNT (SOME (acc + if ~(x IN s) /\ P x then 1 else 0)) s P)`,
  REWRITE_TAC[COUNT; FORALL_OPTION_THM; FINITE_EMPTY; FINITE_INSERT] THEN
  REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; ADD_0] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
  [ALL_TAC;
   SUBGOAL_THEN `{y:A | y IN x INSERT s /\ P y} = {y | y IN s /\ P y}`
     SUBST1_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[injectivity "option"] THEN ARITH_TAC]] THEN
  SUBGOAL_THEN `{y:A | y IN x INSERT s /\ P y} = x INSERT {y | y IN s /\ P y}`
    SUBST1_TAC THENL
  [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {y:A | y IN s /\ P y}`
   (fun th -> ASM_SIMP_TAC[CARD_CLAUSES; th; FINITE_INSERT]) THENL
  [MATCH_MP_TAC FINITE_SUBSET THEN ASM SET_TAC[];
   ASM_REWRITE_TAC[IN_ELIM_THM; injectivity "option"] THEN ARITH_TAC]);;

let COUNT_UNION = prove
 (`!acc s t P:A->bool.
     DISJOINT s t
     ==> COUNT acc (s UNION t) P = COUNT (COUNT acc s P) t P`,
  REWRITE_TAC[FORALL_OPTION_THM; COUNT; FINITE_UNION; DISJOINT] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `FINITE (s:A->bool)` THEN ASM_REWRITE_TAC[COUNT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[COUNT; injectivity "option"] THEN
  SUBGOAL_THEN
    `{x:A | x IN s UNION t /\ P x} =
     {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`
    (fun th -> ASM_SIMP_TAC[th]) THENL
  [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `CARD ({x:A | x IN s /\ P x} UNION {x | x IN t /\ P x}) =
     CARD {x | x IN s /\ P x} + CARD {x | x IN t /\ P x}`
    SUBST1_TAC THENL
  [MATCH_MP_TAC CARD_UNION THEN
   CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
   ASM SET_TAC[];
   ARITH_TAC]);;

add_ants_thl [COUNT_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Set operations.                                                           *)
(* ------------------------------------------------------------------------- *)

let SETALL = new_definition
  `SETALL P s <=> (!x:A. x IN s ==> P x)`;;

let SETALL_CLAUSES = prove
 (`(!P:A->bool. SETALL P {}) /\
   (!P x:A s. SETALL P (x INSERT s) <=> P x /\ SETALL P s)`,
  REWRITE_TAC[SETALL] THEN SET_TAC[]);;

add_ants_thl [SETALL_CLAUSES];;

let SETFILTER = new_definition
  `SETFILTER (P:A->bool) s = {x | x IN s /\ P x}`;;

let SETFILTER_CLAUSES = prove
 (`(!P. SETFILTER P {} = {}) /\
   (!P x:A s. SETFILTER P (x INSERT s) =
              if P x then x INSERT SETFILTER P s else SETFILTER P s)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; NOT_IN_EMPTY;
           SETFILTER; FORALL_IN_GSPEC; FORALL_IN_INSERT; IMP_CONJ] THENL
  [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
   REPEAT GEN_TAC THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

add_ants_thl [SETFILTER_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Collect.                                                                  *)
(* ------------------------------------------------------------------------- *)

let COLLECT = new_definition
  `COLLECT (u:A->B->bool) : (A->B)->bool = {f : A -> B | !x. f x IN u x}`;;

let COLLECT_CONST = prove
 (`!s:B->bool. COLLECT (\x:A. s) = {f | !x. f x IN s}`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; COLLECT]);;

let COLLECT_o = prove
 (`!f:C->A u:A->B->bool.
     (!x y. f x = f y ==> x = y) /\
     (!y. ?x. f x = y)
     ==> COLLECT (u o f) = IMAGE (\g. g o f) (COLLECT u)`,
  INTRO_TAC "!f u; inj surj" THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; COLLECT;
              FORALL_IN_GSPEC; FORALL_IN_IMAGE; o_THM] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; o_THM] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![g]; g" THEN
   EXISTS_TAC `g:C->B o inverse (f:C->A)` THEN
   REWRITE_TAC[GSYM o_ASSOC; o_THM] THEN
   HYP_TAC "inj" (REWRITE_RULE[INJECTIVE_INVERSE_o]) THEN
   ASM_REWRITE_TAC[I_O_ID] THEN
   GEN_TAC THEN
   CLAIM_TAC "+" `u (x:A):B->bool = u (f (inverse f (x:A):C))` THENL
   [AP_TERM_TAC THEN
   HYP_TAC "surj" (REWRITE_RULE[SURJECTIVE_INVERSE]) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "![g]; g; !x" THEN ASM_REWRITE_TAC[]);;

let COLLECT_o_ALT = prove
 (`!f:C->A u:A->B->bool.
     (!x y. f x = f y ==> x = y) /\
     (!y. ?x. f x = y)
     ==> COLLECT u = IMAGE (\g. g o inverse f) (COLLECT (u o f))`,
  INTRO_TAC "!f u; inj surj" THEN
  SUBGOAL_THEN `u:A->B->bool = (u o f:C->A) o inverse f`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
  [HYP_TAC "surj" (REWRITE_RULE[SURJECTIVE_INVERSE_o]) THEN
   ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID];
   ALL_TAC] THEN
  MP_TAC (ISPECL [`inverse (f:C->A)`; `u:A->B->bool o f:C->A`] COLLECT_o) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    POP_ASSUM (MP_TAC o AP_TERM `f:C->A`) THEN
    HYP_TAC "surj" (REWRITE_RULE[SURJECTIVE_INVERSE]) THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN EXISTS_TAC `f (y:C):A` THEN
    HYP_TAC "inj" (REWRITE_RULE[INJECTIVE_INVERSE]) THEN
    ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let COLLECT_o_ALT2 = prove
 (`!f:A->C u:A->B->bool.
     (!x y. f x = f y ==> x = y) /\
     (!y. ?x. f x = y)
     ==> COLLECT u = IMAGE (\g. g o f) (COLLECT (u o inverse f))`,
  CHEAT_TAC);;
  (* INTRO_TAC "!f u; inj surj" THEN
  SUBGOAL_THEN `u:A->B->bool = (u o f:C->A) o inverse f`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
  [HYP_TAC "surj" (REWRITE_RULE[SURJECTIVE_INVERSE_o]) THEN
   ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID];
   ALL_TAC] THEN
  MP_TAC (ISPECL [`inverse (f:C->A)`; `u:A->B->bool o f:C->A`] COLLECT_o) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    POP_ASSUM (MP_TAC o AP_TERM `f:C->A`) THEN
    HYP_TAC "surj" (REWRITE_RULE[SURJECTIVE_INVERSE]) THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN EXISTS_TAC `f (y:C):A` THEN
    HYP_TAC "inj" (REWRITE_RULE[INJECTIVE_INVERSE]) THEN
    ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);; *)

let COLLECT_EQ_SETBIND = prove
 (`!u:num->A->bool.
     COLLECT u =
     SETBIND (\x:A. IMAGE (\f:num->A n. if n = 0 then x else f (PRE n))
                          (COLLECT (u o SUC)))
         (u 0)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_SETBIND;
              COLLECT; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_SETBIND; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              FORALL_IN_IMAGE; FORALL_IN_GSPEC; o_THM] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  CONJ_TAC THENL
  [INTRO_TAC "!f; f" THEN
   EXISTS_TAC `f 0:A` THEN
   ASM_REWRITE_TAC[FUN_EQ_THM] THEN
   EXISTS_TAC `f:num->A o SUC` THEN
   ASM_REWRITE_TAC[o_THM] THEN
   INTRO_TAC "![n]" THEN
   COND_CASES_TAC THENL [ASM_MESON_TAC[]; AP_TERM_TAC THEN ASM_ARITH_TAC];
   ALL_TAC] THEN
  INTRO_TAC "!x; x; !f; f; ![n]" THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN ASM_REWRITE_TAC[PRE]);;

add_ants_thl [COLLECT_EQ_SETBIND];;
