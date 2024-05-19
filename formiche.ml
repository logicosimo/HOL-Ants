load_path := "/workspaces/hol-light-devcontainer/code/HOL-Ants" :: !load_path;;

needs "formiche_misc.ml";;
needs "setbind.ml";;

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

let ant_INDUCT,ant_RECUR = define_type
  "ant = Ant(position#bool)";;

let ANT_INJECTIVITY = injectivity "ant";;
let ANT_CASES = cases "ant";;

let POS = define
  `POS (Ant(pos,dir)) = pos`;;

let DIR = define
  `DIR (Ant(pos,dir)) = dir`;;

let system_INDUCT,system_RECUR = define_type
  "system = System(ant^N # num^3)";;

let SYSTEM_INJECTIVITY = injectivity "system";;
let SYSTEM_CASES = cases "system";;

let ANT = define
  `ANT (System(ant:ant^N,sti)) = ant`;;

let STI = define
  `STI (System(ant,sti)) = sti`;;

let NEW_STI_DEF = define
  `NEW_STI (System(ant:ant^N,sti)) : num^3 =
   lambda p. sti$p +
             nsum (1..dimindex(:N))
                  (\i. if POS(ant$i) = PP p then 1 else 0)`;;

let NEW_STI = REWRITE_RULE[LAMBDA_3; PP] NEW_STI_DEF;;

let NEW_ANT = define
  `NEW_ANT (sti:num^3) (Ant(pos,dir)) =
   if pos = P1 then {Ant((if dir then P4 else P0),dir)} else
   if pos = P2 then {Ant((if dir then P3 else P0),dir)} else
   if pos = P3 then {Ant((if dir then P4 else P3),dir)} else
   if pos = P0
   then {Ant(pos,T) | sti$2 <= sti$1 /\ pos = P1 \/
                      sti$1 <= sti$2 /\ pos = P2}
   else {Ant(pos,F) | sti$3 <= sti$1 /\ pos = P1 \/
                      sti$1 <= sti$3 /\ pos = P3}`;;

let NEW_ANT_THM = prove
 (`!pos dir.
     NEW_ANT (sti:num^3) (Ant(pos,dir)) =
     if pos = P1 then {Ant((if dir then P4 else P0),dir)} else
     if pos = P2 then {Ant((if dir then P3 else P0),dir)} else
     if pos = P3 then {Ant((if dir then P4 else P3),dir)} else
     if pos = P0
     then (if sti$2 <= sti$1 then {Ant(P1,T)} else {}) UNION
          (if sti$1 <= sti$2 then {Ant(P2,T)} else {})
     else (if sti$3 <= sti$1 then {Ant(P1,F)} else {}) UNION
          (if sti$1 <= sti$3 then {Ant(P3,F)} else {})`,
  REWRITE_TAC[NEW_ANT; FORALL_POSITION_THM; FORALL_BOOL_THM;
              distinctness "position"] THEN
  SET_TAC[]);;

let NEW_SYSTEM = define
  `NEW_SYSTEM (sys:N system) : N system -> bool =
   {System(ant',NEW_STI sys) | ant':ant^N |
    !i. 1 <= i /\ i <= dimindex(:N)
        ==> ant'$i IN NEW_ANT (STI sys) (ANT sys$i)}`;;

g `!sys:N system.
     NEW_SYSTEM sys =
     let sti' = NEW_STI sys in
     IMAGE (\a. System(vector a:ant^N,NEW_STI sys))
           (LISTCOLLECT (dimindex(:N))
                        (\i. NEW_ANT (STI sys) (ANT sys$SUC i)))`;;
e GEN_TAC;;
e (CLAIM_TAC "@ant sti. sys"  `?ant:ant^N sti. sys = System(ant,sti)`);;
 e (STRUCT_CASES_TAC (ISPEC `sys:N system` (cases "system")));;
 e (REWRITE_TAC[injectivity "system"; PAIR_EXTENSION]);;
 e (MESON_TAC[FST; SND]);;
e (POP_ASSUM SUBST_VAR_TAC);;
e LET_TAC;;
e (REWRITE_TAC[NEW_SYSTEM; ANT; STI]);;
e (MATCH_MP_TAC SUBSET_ANTISYM THEN
   REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; FORALL_IN_IMAGE; FORALL_IN_LISTCOLLECT]);;
e CONJ_TAC;;
 e (INTRO_TAC "!ant'; ant'");;
 e (ASM_REWRITE_TAC[IN_IMAGE; injectivity "system"; PAIR_EQ]);;
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
(*                   SIMULAZIONI                                             *)
(*                                                                           *)
(* ========================================================================= *)
(* ========================================================================= *)

(REWRITE_CONV[NEW_SYSTEM_ALT; DIMINDEX_2; ANT; STI] THENC TOP_SWEEP_CONV let_CONV THENC
 TOP_SWEEP_CONV num_CONV THENC
 REWRITE_CONV[LISTCOLLECT_CLAUSES; SETBIND_CLAUSES; UNION_EMPTY; INSERT_UNION; o_THM] THENC
 NUM_REDUCE_CONV THENC
 REWRITE_CONV[VECTOR_2; VECTOR_3; NEW_ANT_THM; distinctness "position";
              IMAGE_CLAUSES; IMAGE_UNION] THENC
 NUM_REDUCE_CONV THENC
 REWRITE_CONV[INSERT_UNION; UNION_EMPTY; IMAGE_CLAUSES; SETBIND_CLAUSES;
  IN_INSERT; NOT_IN_EMPTY; CONS_11; injectivity "ant"; PAIR_EQ;
  distinctness "position"; NEW_STI; VECTOR_3; VECTOR_2; DIMINDEX_2] THENC
 ONCE_DEPTH_CONV NUMSEG_CONV THENC
 SIMP_CONV[NSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THENC
 REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; VECTOR_2; VECTOR_3; POS;
   distinctness "position"] THENC
 NUM_REDUCE_CONV THENC
 ALL_CONV)
`NEW_SYSTEM (System(
   vector[Ant(P1,F);Ant(P0,T)]:ant^2,
   vector[0;0;0]:num^3
 ))`;;
