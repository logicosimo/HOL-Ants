load_path := "/workspaces/hol-light-devcontainer/code/HOL-Ants" :: !load_path;;

needs "setbind.ml";;
needs "conv.ml";;
needs "comp.ml";;
loadt "formiche_misc.ml";;

(* ------------------------------------------------------------------------- *)
(* Rewriting rules for computations.                                         *)
(* ------------------------------------------------------------------------- *)

let get_ants_thl,add_ants_thl =
  let thl:thm list ref = ref [] in
  let get_ants_thl() = !thl
  and add_ants_thl l = thl := l @ !thl in
  get_ants_thl,add_ants_thl;;

let ANTS_COMPUTE_CONV : conv = fun tm -> COMPUTE_CONV (get_ants_thl()) tm;;

let run_conv (conv:conv) tm = rhs(concl(conv tm));;

add_ants_thl [NOT_IN_EMPTY; IN_INSERT; UNION_EMPTY; INSERT_UNION;
              IMAGE_CLAUSES; SETBIND_CLAUSES];;
add_ants_thl [PAIR_EQ; CONS_11; NOT_CONS_NIL];;
add_ants_thl [MESON [] `T = F <=> F`; MESON [] `F = T <=> F`];;

let VECTOR_EQ_2 = prove
 (`!x x' y y'. vector[x; y]:A^2 = vector[x'; y'] <=>
               x = x' /\ y = y'`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let VECTOR_EQ_3 = prove
 (`!x x' y y' z z'.
     vector[x; y; z]:A^3 = vector[x'; y'; z'] <=>
     x = x' /\ y = y' /\ z = z'`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3]);;

let VECTOR_EQ_4 = prove
 (`!w w' x x' y y' z z'.
     vector[x; y; z; w]:A^4 = vector[x'; y'; z'; w'] <=>
     x = x' /\ y = y' /\ z = z' /\ w = w'`,
  REWRITE_TAC[CART_EQ; DIMINDEX_4; FORALL_4; VECTOR_4]);;

add_ants_thl [VECTOR_EQ_2; VECTOR_EQ_3; VECTOR_EQ_4];;

(* ------------------------------------------------------------------------- *)
(* Positions.                                                               ` *)
(* ------------------------------------------------------------------------- *)

let position_INDUCT,position_RECUR = define_type
  "position = P0 | P1 | P2 | P3 | P4";;

let POSITION_CASES = cases "position";;
let POSITION_DISTINCTNESS = distinctness "position";;

let FORALL_POSITION_THM = prove
 (`!P. (!p:position. P p) <=> P P0 /\ P P1 /\ P P2 /\ P P3 /\ P P4`,
  METIS_TAC[cases "position"]);;

let EXISTS_POSITION_THM = prove
 (`!P. (?p:position. P p) <=> P P0 \/ P P1 \/ P P2 \/ P P3 \/ P P4`,
  METIS_TAC[cases "position"]);;

let PP = define
  `PP 0 = P0 /\
   PP 1 = P1 /\
   PP 2 = P2 /\
   PP 3 = P3 /\
   PP 4 = P4`;;

add_ants_thl [POSITION_DISTINCTNESS; PP];;

(* ------------------------------------------------------------------------- *)
(* System.                                                                   *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("ant",`:position#bool`);;

let system_INDUCT,system_RECUR = define_type
  "system = System (ant^N) (num^3)";;

let SYSTEM_INJECTIVITY = injectivity "system";;
let SYSTEM_CASES = cases "system";;

let ANT = define
  `ANT (System ant sti : N system) = ant`;;

let STI = define
  `STI (System ant sti : N system) = sti`;;

let FORALL_SYSTEM_THM = prove
 (`!P. (!sys:N system. P sys) <=> (!ant sti. P (System ant sti))`,
  METIS_TAC[cases "system"]);;

let EXISTS_SYSTEM_THM = prove
 (`!P. (?sys:N system. P sys) <=> (?ant sti. P (System ant sti))`,
  METIS_TAC[cases "system"]);;

add_ants_thl [SYSTEM_INJECTIVITY];;

(* ------------------------------------------------------------------------- *)
(* Transition.                                                               *)
(* ------------------------------------------------------------------------- *)

let NEW_STI_DEF = define
  `NEW_STI (System ant sti : N system) : num^3 =
   lambda p. sti$p +
             nsum (1..dimindex(:N))
                  (\i. if FST(ant$i) = PP p then 1 else 0)`;;

let NEW_STI = REWRITE_RULE[LAMBDA_3; PP] NEW_STI_DEF;;

let NEW_ANT = define
  `NEW_ANT (sti:num^3) (pos,dir) =
   if pos = P1 then {((if dir then P4 else P0),dir)} else
   if pos = P2 then {((if dir then P3 else P0),dir)} else
   if pos = P3 then {((if dir then P4 else P2),dir)} else
   if pos = P0
   then {(pos,T) | sti$2 <= sti$1 /\ pos = P1 \/
                   sti$1 <= sti$2 /\ pos = P2}
   else {(pos,F) | sti$3 <= sti$1 /\ pos = P1 \/
                   sti$1 <= sti$3 /\ pos = P3}`;;

let NEW_ANT_THM = prove
 (`!pos dir.
     NEW_ANT (sti:num^3) (pos,dir) =
     if pos = P1 then {((if dir then P4 else P0),dir)} else
     if pos = P2 then {((if dir then P3 else P0),dir)} else
     if pos = P3 then {((if dir then P4 else P2),dir)} else
     if pos = P0
     then (if sti$2 <= sti$1 then {(P1,T)} else {}) UNION
          (if sti$1 <= sti$2 then {(P2,T)} else {})
     else (if sti$3 <= sti$1 then {(P1,F)} else {}) UNION
          (if sti$1 <= sti$3 then {(P3,F)} else {})`,
  REWRITE_TAC[NEW_ANT; FORALL_POSITION_THM; FORALL_BOOL_THM;
              distinctness "position"] THEN
  SET_TAC[]);;

let NEW_SYSTEM = define
  `NEW_SYSTEM (sys:N system) : N system -> bool =
   {System ant' (NEW_STI sys) | ant':ant^N |
    !i. 1 <= i /\ i <= dimindex(:N)
        ==> ant'$i IN NEW_ANT (STI sys) (ANT sys$i)}`;;

g `!sys:N system.
     NEW_SYSTEM sys =
     let sti' = NEW_STI sys in
     IMAGE (\a. System (vector a) (NEW_STI sys) : N system)
           (LISTCOLLECT (dimindex(:N))
                        (\i. NEW_ANT (STI sys) (ANT sys$SUC i)))`;;
e (REWRITE_TAC[FORALL_SYSTEM_THM]);;
e (REPEAT GEN_TAC THEN LET_TAC);;
e (REWRITE_TAC[NEW_SYSTEM; ANT; STI]);;
e (MATCH_MP_TAC SUBSET_ANTISYM THEN
   REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; FORALL_IN_IMAGE; FORALL_IN_LISTCOLLECT]);;
e CONJ_TAC;;
 e (INTRO_TAC "!ant'; ant'");;
 e (ASM_REWRITE_TAC[IN_IMAGE; injectivity "system"]);;
 e (EXISTS_TAC `list_of_vector (ant':ant^N)`);;
 e (REWRITE_TAC[VECTOR_LIST_OF_VECTOR]);;
 e (REWRITE_TAC[IN_LISTCOLLECT; LENGTH_LIST_OF_VECTOR]);;
 e (SIMP_TAC[EL_LIST_OF_VECTOR]);;
 e (REPEAT STRIP_TAC);;
 e (FIRST_X_ASSUM MATCH_MP_TAC);;
 e ASM_ARITH_TAC;;
(* <== *)
e (INTRO_TAC "![l]; len el");;
e (REWRITE_TAC[IN_ELIM_THM]);;
e (EXISTS_TAC `vector l:ant^N`);;
e (ASM_REWRITE_TAC[injectivity "system"]);;
e (INTRO_TAC "!i; i1 i2");;
e (REWRITE_TAC[vector]);;
e (ASM_SIMP_TAC[LAMBDA_BETA]);;
e (REMOVE_THEN "el" (MP_TAC o SPEC `i - 1`));;
e (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]);;
e (ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> SUC (i - 1) = i`]);;
let NEW_SYSTEM_ALT = top_thm();;


(* ========================================================================= *)
(* ========================================================================= *)
(*                                                                           *)
(*                   Simulations                                             *)
(*                                                                           *)
(* ========================================================================= *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* 2 ants.                                                                   *)
(* ------------------------------------------------------------------------- *)

let LISTCOLLECT_2 =
  (TOP_SWEEP_CONV num_CONV THENC
   REWRITE_CONV[LISTCOLLECT_CLAUSES;
                SETBIND_CLAUSES; o_THM; UNION_EMPTY] THENC
   NUM_REDUCE_CONV)
  `LISTCOLLECT 2 (u:num->A->bool)`;;

let condth1 = prove
 (`!f:A->B b s t.
     IMAGE f (if b then s else t) = if b then IMAGE f s else IMAGE f t`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let condth2 = prove
 (`!x:A b s t.
     x IN (if b then s else t) <=> if b then x IN s else x IN t`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let NEW_SYSTEM_2 =
  CONV_RULE
    (REWRITE_CONV[ANT; STI; NEW_STI; VECTOR_2; VECTOR_3] THENC
     TOP_DEPTH_CONV DIMINDEX_CONV THENC TOP_DEPTH_CONV NUMSEG_CONV THENC
     SIMP_CONV[NSUM_CLAUSES; FINITE_EMPTY; FINITE_INSERT] THENC
     TOP_DEPTH_CONV DIMINDEX_CONV THENC
     REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; ADD_0; LISTCOLLECT_2] THENC
    NUM_REDUCE_CONV THENC
    REWRITE_CONV[NEW_ANT_THM; VECTOR_2; VECTOR_3] THENC
    ONCE_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[condth1; IMAGE_CLAUSES; IMAGE_UNION])
  (ISPEC `System (vector[(pos1,dir1); (pos2,dir2)])
                 (vector[s1; s2; s3]) : 2 system`
         NEW_SYSTEM_ALT);;

add_ants_thl [NEW_SYSTEM_2];;

let tm =
  time (run_conv (TOP_SWEEP_CONV num_CONV THENC
                  REWRITE_CONV[ITER] THENC
                  ANTS_COMPUTE_CONV))
  `ITER 30 (SETBIND NEW_SYSTEM)
           {System (vector[(P1,T); (P2,F)])
                   (vector[0; 0; 0]) : 2 system}`;;

(* ------------------------------------------------------------------------- *)
(* 3 ants.                                                                   *)
(* ------------------------------------------------------------------------- *)

let LISTCOLLECT_3 =
  (TOP_SWEEP_CONV num_CONV THENC
   REWRITE_CONV[LISTCOLLECT_CLAUSES;
                SETBIND_CLAUSES; o_THM; UNION_EMPTY] THENC
   NUM_REDUCE_CONV)
  `LISTCOLLECT 3 (u:num->A->bool)`;;

let NEW_SYSTEM_3 =
  CONV_RULE
    (REWRITE_CONV[ANT; STI; NEW_STI; VECTOR_3] THENC
     TOP_DEPTH_CONV DIMINDEX_CONV THENC TOP_DEPTH_CONV NUMSEG_CONV THENC
     SIMP_CONV[NSUM_CLAUSES; FINITE_EMPTY; FINITE_INSERT] THENC
     TOP_DEPTH_CONV DIMINDEX_CONV THENC
     REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; ADD_0; LISTCOLLECT_3] THENC
    NUM_REDUCE_CONV THENC
    REWRITE_CONV[NEW_ANT_THM; VECTOR_3] THENC
    ONCE_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[condth1; IMAGE_CLAUSES; IMAGE_UNION])
  (ISPEC `System (vector[(pos1,dir1); (pos2,dir2); (pos3,dir3)])
                 (vector[s1; s2; s3]) : 3 system`
         NEW_SYSTEM_ALT);;

add_ants_thl [NEW_SYSTEM_3];;

let tm =
  time (run_conv (TOP_SWEEP_CONV num_CONV THENC
                  REWRITE_CONV[ITER] THENC
                  ANTS_COMPUTE_CONV))
  `ITER 20 (SETBIND NEW_SYSTEM)
           {System (vector[(P0,T); (P1,F); (P2,F)])
                   (vector[0; 0; 0]) : 3 system}`;;

(* ------------------------------------------------------------------------- *)
(* 4 ants.                                                                   *)
(* ------------------------------------------------------------------------- *)

let LISTCOLLECT_4 =
  (TOP_SWEEP_CONV num_CONV THENC
   REWRITE_CONV[LISTCOLLECT_CLAUSES;
                SETBIND_CLAUSES; o_THM; UNION_EMPTY] THENC
   NUM_REDUCE_CONV)
  `LISTCOLLECT 4 (u:num->A->bool)`;;

let NEW_SYSTEM_4 =
  CONV_RULE
    (REWRITE_CONV[ANT; STI; NEW_STI; VECTOR_4] THENC
     TOP_DEPTH_CONV DIMINDEX_CONV THENC TOP_DEPTH_CONV NUMSEG_CONV THENC
     SIMP_CONV[NSUM_CLAUSES; FINITE_EMPTY; FINITE_INSERT] THENC
     TOP_DEPTH_CONV DIMINDEX_CONV THENC
     REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; ADD_0; LISTCOLLECT_4] THENC
    NUM_REDUCE_CONV THENC
    REWRITE_CONV[NEW_ANT_THM; VECTOR_3; VECTOR_4] THENC
    ONCE_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[condth1; IMAGE_CLAUSES; IMAGE_UNION])
  (ISPEC `System (vector[(pos1,dir1); (pos2,dir2); (pos3,dir3); (pos4,dir4)])
                 (vector[s1; s2; s3]) : 4 system`
         NEW_SYSTEM_ALT);;

add_ants_thl [NEW_SYSTEM_4];;

let tm =
  time (run_conv (TOP_SWEEP_CONV num_CONV THENC
                  REWRITE_CONV[ITER] THENC
                  ANTS_COMPUTE_CONV))
  `ITER 10 (SETBIND NEW_SYSTEM)
           {System (vector[(P0,T); (P1,F); (P2,F); (P4,F)])
                   (vector[0; 0; 0]) : 4 system}`;;




(* ========================================================================= *)
(* Formal proof.                                                             *)
(* ========================================================================= *)

let INVARIANT_STI = new_definition
  `INVARIANT_STI (sti:num^3) <=> sti$1 > MAX (sti$2) (sti$3)`;;

let INVARIANT = new_definition
  `INVARIANT (sys:N system) <=> INVARIANT_STI (STI sys) /\
                                INVARIANT_STI (NEW_STI sys)`;;

(* g `!sys sys':N system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (ONCE_REWRITE_TAC[FORALL_SYSTEM_THM] THEN GEN_TAC THEN GEN_TAC);;
e (REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM]);;
e (INTRO_TAC "i");;
e (REWRITE_TAC[NEW_SYSTEM; FORALL_IN_GSPEC; STI; ANT]);;
e (INTRO_TAC "!ant'; ant'");;
e (HYP_TAC "i : i1 i2" (REWRITE_RULE[INVARIANT; STI]));;
e (ASM_REWRITE_TAC[INVARIANT; STI]);;
e (HYP_TAC "i1 -> i1'" (REWRITE_RULE[INVARIANT_STI; VECTOR_3]));;
e (HYP_TAC "i2 -> i2'" (REWRITE_RULE[NEW_STI; INVARIANT_STI; VECTOR_3]));;
e (REWRITE_TAC[NEW_STI; INVARIANT_STI; VECTOR_3]);; *)


g `!sys sys':2 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (ONCE_REWRITE_TAC[FORALL_SYSTEM_THM] THEN GEN_TAC THEN GEN_TAC);;
e (REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM]);;
e (INTRO_TAC "i");;
e (REWRITE_TAC[NEW_SYSTEM; FORALL_IN_GSPEC; STI; ANT]);;
e (REWRITE_TAC[DIMINDEX_2; FORALL_2]);;
e GEN_TAC;;
e (DESTRUCT_TAC "@p01 d01. ant1" (ISPEC `(ant:ant^2)$1` PAIR_SURJECTIVE));;
e (DESTRUCT_TAC "@p02 d02. ant2" (ISPEC `(ant:ant^2)$2` PAIR_SURJECTIVE));;
e (DESTRUCT_TAC "@p11 d11. ant'1" (ISPEC `(ant':ant^2)$1` PAIR_SURJECTIVE));;
e (DESTRUCT_TAC "@p12 d12. ant'2" (ISPEC `(ant':ant^2)$2` PAIR_SURJECTIVE));;
e (ASM_REWRITE_TAC[NEW_ANT_THM; condth2; IN_INSERT; NOT_IN_EMPTY; PAIR_EQ; IN_UNION]);;
e (REWRITE_TAC[MESON[] `(if b then c else F) <=> b /\ c`]);;
e (INTRO_TAC "ant'");;
e (REMOVE_THEN "i" MP_TAC);;
e (REWRITE_TAC[INVARIANT; STI]);;
e (SIMP_TAC[]);;
e (REWRITE_TAC[NEW_STI; DIMINDEX_2; VECTOR_3]);;
e (CONV_TAC (ONCE_DEPTH_CONV NUMSEG_CONV));;
e (ASM_SIMP_TAC[NSUM_CLAUSES; FINITE_EMPTY; FINITE_INSERT; NOT_IN_EMPTY;
                IN_INSERT; ARITH_EQ; ADD_0]);;
e (REWRITE_TAC[INVARIANT_STI; VECTOR_3]);;
e (INTRO_TAC "sti0 sti1");;
e (REMOVE_THEN "ant'" MP_TAC);;
e (SUBGOAL_THEN `sti:num^3$2 <= sti$1 /\ ~(sti$1 <= sti$2) /\ sti$3 <= sti$1 /\ ~(sti$1 <= sti$3)`
    (fun th -> REWRITE_TAC[th]));;
 e ASM_ARITH_TAC;;
e (REMOVE_THEN "sti1" MP_TAC);;
e (POP_ASSUM_LIST (MP_TAC o end_itlist CONJ));;
e (STRUCT_CASES_TAC (SPEC `p01:position` (cases "position")) THEN
   REWRITE_TAC[distinctness "position"; ADD] THEN
   REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   REWRITE_TAC[distinctness "position"] THEN
   TRY (POP_ASSUM_LIST (MP_TAC o end_itlist CONJ)) THEN
   STRUCT_CASES_TAC (SPEC `p02:position` (cases "position")) THEN
   REWRITE_TAC[distinctness "position"; ADD; ADD_0] THEN
   REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   ASM_REWRITE_TAC[distinctness "position"] THEN TRY ASM_ARITH_TAC THEN
   POP_ASSUM_LIST (MP_TAC o end_itlist CONJ) THEN
   BOOL_CASES_TAC `d01:bool` THEN REWRITE_TAC[distinctness "position"] THEN
   BOOL_CASES_TAC `d02:bool` THEN REWRITE_TAC[distinctness "position"] THEN
   REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   ASM_REWRITE_TAC[distinctness "position"] THEN TRY ASM_ARITH_TAC);;
