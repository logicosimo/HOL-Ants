(* ========================================================================= *)
(* Modelling framework for an idealised system of foraging ants.             *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2023-2024.              *)
(* ========================================================================= *)

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

let NEW_STI_COMPONENT = prove
 (`!p. 1 <= p /\ p <= 3
       ==> NEW_STI (System ant sti : N system) $ p =
           sti$p + nsum (1..dimindex(:N))
                        (\i. if FST(ant$i) = PP p then 1 else 0)`,
  SIMP_TAC[NEW_STI_DEF; LAMBDA_BETA; DIMINDEX_3]);;

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
   REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; FORALL_IN_IMAGE;
               FORALL_IN_LISTCOLLECT]);;
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

g `!sys sys':N system.
     sys' IN NEW_SYSTEM sys <=>
     STI sys' = NEW_STI sys /\
     list_of_vector (ANT sys') IN LISTCOLLECT (dimindex(:N))
                                  (\i. NEW_ANT (STI sys) (ANT sys$SUC i))`;;
e (SUBGOAL_THEN
    `!sys sys':N system.
       sys' IN NEW_SYSTEM sys ==>
       STI sys' = NEW_STI sys /\
       list_of_vector (ANT sys') IN LISTCOLLECT (dimindex(:N))
                                  (\i. NEW_ANT (STI sys) (ANT sys$SUC i))`
    MP_TAC);;
 e (GEN_TAC THEN REWRITE_TAC[NEW_SYSTEM_ALT]);;
 e LET_TAC;;
 e (REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_LISTCOLLECT]);;
 e (REWRITE_TAC[ANT; STI]);;
 e (SIMP_TAC[LIST_OF_VECTOR_VECTOR]);;
 e (REWRITE_TAC[IN_LISTCOLLECT]);;
e (SUBGOAL_THEN
    `!sys sys':N system.
       STI sys' = NEW_STI sys /\
       list_of_vector (ANT sys') IN LISTCOLLECT (dimindex(:N))
                                  (\i. NEW_ANT (STI sys) (ANT sys$SUC i))
       ==> sys' IN NEW_SYSTEM sys`
    (fun th -> MESON_TAC[th]));;
e GEN_TAC;;
e (REWRITE_TAC[FORALL_SYSTEM_THM; ANT; STI]);;
e (INTRO_TAC "![ant'] [sti']; sti' ant'");;
e (REWRITE_TAC[NEW_SYSTEM_ALT]);;
e (REMOVE_THEN "sti'" SUBST_VAR_TAC);;
e (CONV_TAC (ONCE_DEPTH_CONV let_CONV));;
e (REWRITE_TAC[IN_IMAGE]);;
e (EXISTS_TAC `list_of_vector(ant':ant^N)`);;
e (ASM_REWRITE_TAC[injectivity "system"; VECTOR_LIST_OF_VECTOR]);;
let IN_NEW_SYSTEM = top_thm();;

(* ========================================================================= *)
(* Simulations                                                               *)
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

search[`f (if b then x else y) = aa`];;

let APP_COND = prove
 (`!f:A->B b x y. f (if b then x else y) = if b then f x else f y`,
  REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC COND_RAND);;

let IMAGE_COND = prove
 (`!f:A->B b s t.
     IMAGE f (if b then s else t) = if b then IMAGE f s else IMAGE f t`,
  REWRITE_TAC[ISPEC `IMAGE f` APP_COND]);;

let IN_COND = prove
 (`!x:A b s t.
     x IN (if b then s else t) <=> if b then x IN s else x IN t`,
  REWRITE_TAC[ISPEC `(IN) x` APP_COND]);;

let SETBIND_COND = prove
 (`!f:A->B->bool b s t.
     SETBIND f (if b then s else t) = if b then SETBIND f s else SETBIND f t`,
  REWRITE_TAC[ISPEC `SETBIND f` APP_COND]);;

(* NEW_SYSTEM for two ants *)
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
    REWRITE_CONV[IMAGE_COND; IMAGE_CLAUSES; IMAGE_UNION])
  (ISPEC `System (vector[(pos1,dir1); (pos2,dir2)])
                 (vector[s1; s2; s3]) : 2 system`
         NEW_SYSTEM_ALT);;

add_ants_thl [NEW_SYSTEM_2];;

(* 
let tm =
  time (run_conv (TOP_SWEEP_CONV num_CONV THENC
                  REWRITE_CONV[ITER] THENC
                  ANTS_COMPUTE_CONV))
  `ITER 10 (SETBIND NEW_SYSTEM)
           {System (vector[(P1,T); (P2,F)])
                   (vector[0; 0; 0]) : 2 system}`;;

CPU time (user): 0.376958
val tm : term =
  `{System (vector [P1,F; P1,T]) (vector [9; 1; 0]),
    System (vector [P1,F; P0,F]) (vector [8; 2; 1]),
    System (vector [P4,T; P0,F]) (vector [7; 3; 2]),
    System (vector [P4,T; P1,F]) (vector [5; 4; 3]),
    System (vector [P3,T; P1,F]) (vector [4; 5; 3])}`
*)

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
    REWRITE_CONV[IMAGE_COND; IMAGE_CLAUSES; IMAGE_UNION])
  (ISPEC `System (vector[(pos1,dir1); (pos2,dir2); (pos3,dir3)])
                 (vector[s1; s2; s3]) : 3 system`
         NEW_SYSTEM_ALT);;

add_ants_thl [NEW_SYSTEM_3];;

(* 
let tm =
  time (run_conv (TOP_SWEEP_CONV num_CONV THENC
                  REWRITE_CONV[ITER] THENC
                  ANTS_COMPUTE_CONV))
  `ITER 10 (SETBIND NEW_SYSTEM)
           {System (vector[(P0,T); (P1,F); (P2,F)])
                   (vector[0; 0; 0]) : 3 system}`;;

CPU time (user): 3.947183
val tm : term =
  `{System (vector [P4,T; P1,T; P1,T]) (vector [14; 1; 0]),
    System (vector [P4,T; P0,F; P1,T]) (vector [13; 2; 1]),
    System (vector [P4,T; P1,T; P0,F]) (vector [13; 2; 1]),
    System (vector [P4,T; P0,F; P0,F]) (vector [12; 3; 2]),
    System (vector [P1,T; P0,F; P0,F]) (vector [10; 4; 3]),
    System (vector [P1,T; P1,T; P1,T]) (vector [12; 2; 1]),
    System (vector [P1,T; P0,F; P1,T]) (vector [11; 3; 2]),
    System (vector [P1,T; P1,F; P1,T]) (vector [9; 4; 3]),
    System (vector [P1,T; P1,T; P0,F]) (vector [11; 3; 2]),
    System (vector [P1,T; P1,T; P1,F]) (vector [9; 4; 3]),
    System (vector [P2,F; P4,T; P4,T]) (vector [2; 9; 9]),
    System (vector [P3,F; P4,T; P4,T]) (vector [1; 10; 9])}`
*)

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
    REWRITE_CONV[IMAGE_COND; IMAGE_CLAUSES; IMAGE_UNION])
  (ISPEC `System (vector[(pos1,dir1); (pos2,dir2); (pos3,dir3); (pos4,dir4)])
                 (vector[s1; s2; s3]) : 4 system`
         NEW_SYSTEM_ALT);;

add_ants_thl [NEW_SYSTEM_4];;

(* 
let tm =
  time (run_conv (TOP_SWEEP_CONV num_CONV THENC
                  REWRITE_CONV[ITER] THENC
                  ANTS_COMPUTE_CONV))
  `ITER 5 (SETBIND NEW_SYSTEM)
           {System (vector[(P0,T); (P1,F); (P2,F); (P4,F)])
                   (vector[0; 0; 0]) : 4 system}`;;

CPU time (user): 16.375348
val tm : term =
  `{System (vector [P1,T; P0,F; P0,F; P1,F]) (vector [9; 1; 0]),
    System (vector [P1,T; P1,F; P0,F; P1,F]) (vector [7; 2; 1]),
    System (vector [P1,T; P0,F; P1,F; P1,F]) (vector [7; 2; 1]),
    System (vector [P1,T; P1,F; P1,F; P1,F]) (vector [5; 3; 2]),
    System (vector [P0,F; P0,F; P0,F; P1,F]) (vector [8; 2; 1]),
    System (vector [P0,F; P1,F; P0,F; P1,F]) (vector [6; 3; 2]),
    System (vector [P0,F; P1,F; P0,F; P4,T]) (vector [5; 4; 3]),
    System (vector [P0,F; P0,F; P1,F; P1,F]) (vector [6; 3; 2]),
    System (vector [P0,F; P0,F; P1,F; P4,T]) (vector [5; 4; 3]),
    System (vector [P0,F; P1,F; P1,F; P1,F]) (vector [4; 4; 3]),
    System (vector [P0,F; P3,F; P1,F; P1,F]) (vector [4; 4; 3]),
    System (vector [P0,F; P1,F; P3,F; P1,F]) (vector [4; 4; 3]),
    System (vector [P0,F; P3,F; P3,F; P1,F]) (vector [4; 4; 3]),
    System (vector [P0,F; P1,F; P1,F; P3,F]) (vector [4; 4; 3]),
    System (vector [P0,F; P3,F; P1,F; P3,F]) (vector [4; 4; 3]),
    System (vector [P0,F; P1,F; P3,F; P3,F]) (vector [4; 4; 3]),
    System (vector [P0,F; P3,F; P3,F; P3,F]) (vector [4; 4; 3]),
    System (vector [P0,F; P3,F; P3,F; P4,T]) (vector [3; 5; 4]),
    System (vector [P1,T; P0,F; P0,F; P4,T]) (vector [8; 2; 1]),
    System (vector [P1,T; P1,F; P0,F; P4,T]) (vector [6; 3; 2]),
    System (vector [P1,T; P1,F; P0,F; P3,T]) (vector [5; 4; 2]),
    System (vector [P1,T; P0,F; P1,F; P4,T]) (vector [6; 3; 2]),
    System (vector [P1,T; P0,F; P1,F; P3,T]) (vector [5; 4; 2]),
    System (vector [P2,T; P1,F; P1,F; P3,T]) (vector [3; 5; 3]),
    System (vector [P2,T; P3,F; P1,F; P3,T]) (vector [3; 5; 3]),
    System (vector [P2,T; P1,F; P3,F; P3,T]) (vector [3; 5; 3]),
    System (vector [P2,T; P3,F; P3,F; P3,T]) (vector [3; 5; 3]),
    System (vector [P0,F; P0,F; P0,F; P4,T]) (vector [7; 3; 2]),
    System (vector [P0,F; P0,F; P0,F; P3,T]) (vector [6; 4; 2]),
    System (vector [P0,F; P3,F; P0,F; P3,T]) (vector [4; 5; 3]),
    System (vector [P2,F; P3,F; P0,F; P3,T]) (vector [3; 5; 4]),
    System (vector [P0,F; P3,F; P2,F; P3,T]) (vector [3; 5; 4]),
    System (vector [P2,F; P3,F; P2,F; P3,T]) (vector [2; 5; 5]),
    System (vector [P0,F; P0,F; P3,F; P3,T]) (vector [4; 5; 3]),
    System (vector [P2,F; P0,F; P3,F; P3,T]) (vector [3; 5; 4]),
    System (vector [P0,F; P2,F; P3,F; P3,T]) (vector [3; 5; 4]),
    System (vector [P2,F; P2,F; P3,F; P3,T]) (vector [2; 5; 5]),
    System (vector [P2,F; P3,F; P3,F; P3,T]) (vector [1; 6; 5])}`
*)

(* ========================================================================= *)
(* Formal proof.                                                             *)
(* ========================================================================= *)

let INVARIANT_STI = new_definition
  `INVARIANT_STI (sti:num^3) <=> sti$1 > MAX (sti$2) (sti$3)`;;

let INVARIANT = new_definition
  `INVARIANT (sys:N system) <=> (!s t. s IN NEW_SYSTEM sys /\
                                       t IN NEW_SYSTEM s
                                       ==> INVARIANT_STI (STI sys) /\
                                           INVARIANT_STI (STI s) /\
                                           INVARIANT_STI (STI t))`;;

g `!sti p d p' d'.
     INVARIANT_STI sti
     ==> ((p',d') IN NEW_ANT sti (p,d) <=>
          (p = P0 /\ p' = P1 /\ d') \/
          (p = P4 /\ p' = P1 /\ ~d') \/
          (p = P1 /\ d /\ p' = P4 /\ d') \/
          (p = P1 /\ ~d /\ p' = P0 /\ ~d') \/
          (p = P2 /\ d /\ p' = P3 /\ d') \/
          (p = P2 /\ ~d /\ p' = P0 /\ ~d') \/
          (p = P3 /\ d /\ p' = P4 /\ d') \/
          (p = P3 /\ ~d /\ p' = P2 /\ ~d'))`;;
e (REWRITE_TAC[FORALL_VECTOR_3; INVARIANT_STI; VECTOR_3]);;
e (REWRITE_TAC[ARITH_RULE `!x y z. x > MAX y z <=> y < x /\ z < x`]);;
e (REPEAT GEN_TAC THEN INTRO_TAC "sti");;
e (REWRITE_TAC[NEW_ANT; VECTOR_3; IN_COND; IN_ELIM_THM; IN_INSERT;
               NOT_IN_EMPTY; PAIR_EQ]);;
e (REWRITE_TAC[EXISTS_POSITION_THM; distinctness "position"]);;
e (STRUCT_CASES_TAC (SPEC `p:position` POSITION_CASES) THEN
   REWRITE_TAC[distinctness "position"] THEN
   STRUCT_CASES_TAC (SPEC `p':position` POSITION_CASES) THEN
   REWRITE_TAC[distinctness "position"; DE_MORGAN_THM; NOT_LE] THEN
   ASM_SIMP_TAC[LT_IMP_LE] THEN REPEAT COND_CASES_TAC THEN
   ASM_REWRITE_TAC[distinctness "position"]);;
let INVARIANT_IN_NEW_ANT = top_thm();;

g `!sti a a'.
     INVARIANT_STI sti
     ==> (a' IN NEW_ANT sti a <=>
          (FST a = P0 /\ FST a' = P1 /\ SND a') \/
          (FST a = P4 /\ FST a' = P1 /\ ~SND a') \/
          (FST a = P1 /\ SND a /\ FST a' = P4 /\ SND a') \/
          (FST a = P1 /\ ~SND a /\ FST a' = P0 /\ ~SND a') \/
          (FST a = P2 /\ SND a /\ FST a' = P3 /\ SND a') \/
          (FST a = P2 /\ ~SND a /\ FST a' = P0 /\ ~SND a') \/
          (FST a = P3 /\ SND a /\ FST a' = P4 /\ SND a') \/
          (FST a = P3 /\ ~SND a /\ FST a' = P2 /\ ~SND a'))`;;
e (REWRITE_TAC[FORALL_PAIR_THM; INVARIANT_IN_NEW_ANT]);;
let INVARIANT_IN_NEW_ANT_ALT = top_thm();;

g `!P. (!i. i < n ==> P i) <=> (!i. 1 <= i /\ i <= n ==> P (PRE i))`;;
e (GEN_TAC THEN EQ_TAC);;
e (INTRO_TAC "hp; !i; i");;
e (FIRST_X_ASSUM MATCH_MP_TAC);;
e ASM_ARITH_TAC;;
e (INTRO_TAC "hp; !i; i");;
e (FIRST_X_ASSUM (MP_TAC o SPEC `SUC i`));;
e (REWRITE_TAC[PRE]);;
e (DISCH_THEN MATCH_MP_TAC);;
e ASM_ARITH_TAC;;
let FORALL_LT_THM = top_thm();;

g `!sys sys':N system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT]);;
e (SUBGOAL_THEN
     `!s0 s1 s2 s3:N system.
      s1 IN NEW_SYSTEM s0 /\
      s2 IN NEW_SYSTEM s1 /\
      s3 IN NEW_SYSTEM s2 /\
      INVARIANT_STI (STI s0) /\
      INVARIANT_STI (STI s1) /\
      INVARIANT_STI (STI s2)
      ==> INVARIANT_STI (STI s3)`
    (fun th -> MESON_TAC[th]));;
e (REWRITE_TAC[FORALL_SYSTEM_THM; IN_NEW_SYSTEM; STI; ANT]);;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC[IN_LISTCOLLECT]);;
e (REWRITE_TAC[LENGTH_LIST_OF_VECTOR]);;
e (SIMP_TAC[EL_LIST_OF_VECTOR]);;
e (REWRITE_TAC[FORALL_LT_THM]);;
e (SIMP_TAC[ARITH_RULE `!i. 1 <= i ==> SUC(PRE i) = i`]);;
e (INTRO_TAC "(sti' ant') (sti'' ant'') (sti''' _) i0 i1 i2");;
e (HYP_TAC "sti'" GSYM);;
e (HYP_TAC "sti''" GSYM);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[INVARIANT_STI; NEW_STI; VECTOR_3]);;
e (SUBGOAL_THEN
     `nsum (1..dimindex (:N))
           (\i. if FST (ant'':ant^N$i) = P2 then 1 else 0) = 0`
     SUBST1_TAC);;
 e (MATCH_MP_TAC NSUM_EQ_0);;
 e (REWRITE_TAC[IN_NUMSEG] THEN INTRO_TAC "![i]; i");;
 e (REMOVE_THEN "ant''" (IMP_RES_THEN MP_TAC));;
 e (ASM_SIMP_TAC[INVARIANT_IN_NEW_ANT_ALT]);;
 e (REMOVE_THEN "i1" (K ALL_TAC));;
 e (STRUCT_CASES_TAC (SPEC `FST(ant'':ant^N$i)` POSITION_CASES) THEN
    REWRITE_TAC[POSITION_DISTINCTNESS]);;
 e (REMOVE_THEN "ant'" (IMP_RES_THEN MP_TAC));;
 e (ASM_SIMP_TAC[INVARIANT_IN_NEW_ANT_ALT]);;
 e (REMOVE_THEN "i0" (K ALL_TAC));;
 e (STRUCT_CASES_TAC (SPEC `FST(ant':ant^N$i)` POSITION_CASES) THEN
    REWRITE_TAC[POSITION_DISTINCTNESS]);;
 e (MESON_TAC[]);;
e (SUBGOAL_THEN
     `nsum (1..dimindex (:N))
           (\i. if FST (ant'':ant^N$i) = P3 then 1 else 0) = 0`
     SUBST1_TAC);;
 e (MATCH_MP_TAC NSUM_EQ_0);;
 e (REWRITE_TAC[IN_NUMSEG] THEN INTRO_TAC "![i]; i");;
 e (REMOVE_THEN "ant''" (IMP_RES_THEN MP_TAC));;
 e (ASM_SIMP_TAC[INVARIANT_IN_NEW_ANT_ALT]);;
 e (REMOVE_THEN "i1" (K ALL_TAC));;
 e (STRUCT_CASES_TAC (SPEC `FST(ant'':ant^N$i)` POSITION_CASES) THEN
    REWRITE_TAC[POSITION_DISTINCTNESS]);;
 e (REMOVE_THEN "ant'" (IMP_RES_THEN MP_TAC));;
 e (ASM_SIMP_TAC[INVARIANT_IN_NEW_ANT_ALT]);;
 e (REMOVE_THEN "i0" (K ALL_TAC));;
 e (STRUCT_CASES_TAC (SPEC `FST(ant':ant^N$i)` POSITION_CASES) THEN
    REWRITE_TAC[POSITION_DISTINCTNESS]);;
 e (MESON_TAC[]);;
e (REMOVE_THEN "i2" MP_TAC);;
e (REWRITE_TAC[INVARIANT_STI]);;
e ARITH_TAC;;
let INVARIANT_THM = top_thm();;

let INVARIANT_ANT = new_definition
  `INVARIANT_ANT (ant:ant^N) <=>
   (!i. 1 <= i /\ i <= dimindex(:N) ==> FST(ant$i) IN {P0,P1,P4})`;;

g `!sys sys' sys'':N system.
     sys' IN NEW_SYSTEM sys /\
     sys'' IN NEW_SYSTEM sys' /\
     INVARIANT_STI (STI sys) /\
     INVARIANT_STI (STI sys')
     ==> INVARIANT_ANT (ANT sys'')`;;
e (REWRITE_TAC[FORALL_SYSTEM_THM; IN_NEW_SYSTEM; STI; ANT]);;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC[IN_LISTCOLLECT; LENGTH_LIST_OF_VECTOR]);;
e (SIMP_TAC[EL_LIST_OF_VECTOR]);;
e (REWRITE_TAC[FORALL_LT_THM]);;
e (SIMP_TAC[ARITH_RULE `!i. 1 <= i ==> SUC(PRE i) = i`]);;
e (INTRO_TAC "(sti' ant') (sti'' ant'') inv0 inv1");;
e (REWRITE_TAC[NOT_IN_EMPTY; IN_INSERT]);;
e (HYP_TAC "sti'" GSYM);;
e (HYP_TAC "sti''" GSYM);;
e (REWRITE_TAC[INVARIANT_ANT; NOT_IN_EMPTY; IN_INSERT]);;
e (INTRO_TAC "!i; i");;
e (REMOVE_THEN "ant''" (MP_TAC o SPEC `i:num`));;
e (ASM_SIMP_TAC[INVARIANT_IN_NEW_ANT_ALT]);;
e (STRIP_TAC THEN ASM_SIMP_TAC[POSITION_DISTINCTNESS]);;
 e (REMOVE_THEN "ant'" (MP_TAC o SPEC `i:num`));;
 e (ASM_SIMP_TAC[INVARIANT_IN_NEW_ANT_ALT; POSITION_DISTINCTNESS]);;
e (REMOVE_THEN "ant'" (MP_TAC o SPEC `i:num`));;
e (ASM_SIMP_TAC[INVARIANT_IN_NEW_ANT_ALT; POSITION_DISTINCTNESS]);;
let INVARIANT_ANT_THM = top_thm();;
