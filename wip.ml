let ANTS_COMPUTE_CONV : conv = fun tm -> COMPUTE_CONV (get_ants_thl()) tm;;

let run_conv (conv:conv) tm = rhs(concl(conv tm));;

add_ants_thl [IMAGE_CLAUSES; SETBIND_CLAUSES];;
add_ants_thl [IN_FORWARD_MOVES_EXPLICIT];;

add_ants_thl [KEYS_UPDATE];;

let FUNDICT_INSERT = prove
 (`!f:A->B k ks. FUNDICT (k INSERT ks) f = UPDATE (FUNDICT ks f) k (f k)`,
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_FUNDICT; KEYS_UPDATE; FORALL_IN_INSERT; GET_FUNDICT; GET_UPDATE] THEN
  REWRITE_TAC[IN_INSERT] THEN
  MESON_TAC[]);;

add_ants_thl [FUNDICT_INSERT];;
add_ants_thl [KEYS_EMPTYDICT];;

let FUNDICT_EMPTY = prove
 (`!f:A->B. FUNDICT {} f = EMPTYDICT`,
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_FUNDICT; KEYS_EMPTYDICT; NOT_IN_EMPTY]);;

add_ants_thl [FUNDICT_EMPTY];;
add_ants_thl [DICT_COLLECT_UPDATE];;
add_ants_thl [DELETE_INSERT];;
add_ants_thl [UNION_EMPTY; INSERT_UNION];;
add_ants_thl [EMPTY_DELETE];;
add_ants_thl [DICT_RESTRICT_EMPTY];;
add_ants_thl [DICT_COLLECT_EMPTYDICT];;
add_ants_thl [GET_UPDATE];;
add_ants_thl [DICT_RESTRICT_INSERT];;
(* add_ants_thl [ANT_UPDATE_ENVIRONMENT];; *)
add_ants_thl [NOT_IN_EMPTY; IN_INSERT];;
add_ants_thl [DICT_GET_EXTENSION];;
add_ants_thl [PAIR_EQ];;

let FORALL_IN_KEYS_UPDATE = prove
 (`!d:(A,B)dict k0 v.
     (!k. k IN KEYS (UPDATE d k0 v) ==> P k) <=>
     P k0 /\
     (!k. k IN KEYS d ==> P k)`,
  REWRITE_TAC[KEYS_UPDATE; FORALL_IN_INSERT] THEN MESON_TAC[]);;

add_ants_thl [FORALL_IN_KEYS_UPDATE];;

let FORALL_IN_KEYS_EMPTYDICT = prove
 (`!d:(A,B)dict.
     !k. k IN KEYS EMPTYDICT ==> P k`,
  REWRITE_TAC[KEYS_EMPTYDICT; NOT_IN_EMPTY]);;

add_ants_thl [FORALL_IN_KEYS_UPDATE];;

      (* let ants =
         UPDATE
           (UPDATE (UPDATE EMPTYDICT (Ident 0) (Position 1,Forward,ANT))
             (Ident 1) (Position 2,Forward,ANT))
           (Ident 2) (Position 3,Backward,ANT) in *)

      (* let ants = UPDATE EMPTYDICT (Ident 0) (Position 1,Forward,ANT) in *)

(* TODO *)
let DICT_COLLECT_EQ_EMPTY = prove
 (`!d:(K,V->bool)dict.
     DICT_COLLECT d = {} <=> ?k. k IN KEYS d /\ GET d k = {}`,
  GEN_TAC THEN
  TRANS_TAC EQ_TRANS `!f:K->V. ?k. k IN KEYS d /\ ~(f k IN GET d k)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[DICT_COLLECT; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
   ASM_MESON_TAC[];
   CHEAT_TAC]);;

(* let ITERSETBIND = define
  `(!f:A->A->bool s:A->bool. ITERSETBIND 0 f s = s) /\
   (!n f:A->A->bool s:A->bool. ITERSETBIND (SUC n) f s =
                               SETBIND n ) /\ *)

g `!s t. FINITE (KEYS (SYSTEM_AGENTS s)) /\ t IN ANT_UPDATE_SYSTEM s
         ==> FINITE (KEYS (SYSTEM_AGENTS t))`;;
e CHEAT_TAC;;
let FINITE_AGENTS_ANT_UPDATE_SYSTEM = top_thm();;

let IN_LET_THM = prove
 (`!x a b c. x:A IN LET (\a1,2,. LET_END c) b <=> LET (\a. LET_END x IN c) b`,
  REWRITE_TAC[LET_DEF; LET_END_DEF]);;

let PAIR_EXTENSION = prove
 (`!p q:A#B. p = q <=> FST p = FST q /\ SND p = SND q`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

g `!ag sys.
     ag IN ANT_UPDATE_AGENTS sys <=>
     KEYS ag = KEYS (SYSTEM_AGENTS sys) /\
     (!k pos dir log pos' dir' log'.
        k IN KEYS (SYSTEM_AGENTS sys) /\
        GET (SYSTEM_AGENTS sys) k = pos,dir,log /\
        GET ag k = pos',dir',log'
        ==> log = log' /\
            dir',pos' IN AGENT_STEP log (Input (dir,pos,SYSTEM_ENVIRONMENT sys)))`;;
e (REPEAT GEN_TAC);;
e (CLAIM_TAC "@env d. sys" `?env d. sys = System(env,d)`);;
 e (STRUCT_CASES_TAC (SPEC `sys:system` (cases "system")));;
 e (REWRITE_TAC[injectivity "system"]);;
 e (REWRITE_TAC[PAIR_SURJECTIVE]);;
e (POP_ASSUM SUBST_VAR_TAC);;
e (REWRITE_TAC[ANT_UPDATE_AGENTS; SYSTEM_ENVIRONMENT; SYSTEM_AGENTS]);;
e (REWRITE_TAC[IN_DICT_COLLECT; KEYS_FUNDICT; GET_FUNDICT]);;
e (SIMP_TAC[]);;
e (MATCH_MP_TAC (MESON [] `(A ==> B = C) ==> (A /\ B <=> A /\ C)`));;
e (INTRO_TAC "keys");;
e (EQ_TAC THEN REPEAT GEN_TAC);;
 e (INTRO_TAC "hp" THEN REPEAT GEN_TAC);;
 e (INTRO_TAC "k a b");;
 e (FIRST_X_ASSUM (fun th -> (FIRST_ASSUM (MP_TAC  o MATCH_MP th))));;
 e (CONV_TAC (TOP_SWEEP_CONV let_CONV));;
 e LET_TAC;;
 e (REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM]);;
 e STRIP_TAC;;
 e (ASM_MESON_TAC[PAIR_EQ]);;
e (INTRO_TAC "hp; !k; k");;
e (CONV_TAC (TOP_SWEEP_CONV let_CONV));;
e (REMOVE_THEN "hp" (MP_TAC o SPEC `k:num`));;
e LET_TAC;;
e (ASM_REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ]);;
e (DISCH_THEN (MP_TAC o SPECL[`pos:num`; `dir:direction`; `log:(direction,num#num#num#num,num)agent`]));;
e (REWRITE_TAC[]);;
e (REWRITE_TAC[PAIR_EXTENSION]);;
e (ASM_MESON_TAC[]);;
let ANT_UPDATE_AGENTS_THM = top_thm();;

let INVARIANT1 = new_definition
  `INVARIANT1 (s1,s2,s3) <=> s1 > MAX s2 s3`;;

let INVARIANT2 = new_definition
  `INVARIANT2 sys <=> INVARIANT1 (SYSTEM_ENVIRONMENT sys) /\
                      INVARIANT1 (ANT_UPDATE_ENVIRONMENT sys)`;;

g `!s:system.
     let (s1,s2,s3) = SYSTEM_ENVIRONMENT s in
     let ag = SYSTEM_AGENTS s in
     FINITE (KEYS ag) /\
     INVARIANT2 s
     ==> (!s'. s' IN ANT_UPDATE_SYSTEM s ==> INVARIANT2 s')`;;
e GEN_TAC;;
e (CLAIM_TAC "@sti ag. s" `?sti ag. s = System(sti,ag)`);;
 e (STRUCT_CASES_TAC (SPEC `s:system` (cases "system")));;
 e (REWRITE_TAC[injectivity "system"]);;
 e (MESON_TAC[PAIR_SURJECTIVE]);;
e (POP_ASSUM SUBST_VAR_TAC);;
e (REWRITE_TAC[SYSTEM_ENVIRONMENT; SYSTEM_AGENTS]);;
e (CONV_TAC (TOP_DEPTH_CONV let_CONV));;
e LET_TAC;;
e (POP_ASSUM (K ALL_TAC));;
e (INTRO_TAC "inf inv2");;
e (HYP_TAC "inv2: i1 i2" (REWRITE_RULE[INVARIANT2]));;
e (HYP_TAC "i1" (REWRITE_RULE[SYSTEM_ENVIRONMENT; INVARIANT1]));;
e (HYP_TAC "i2 -> i2'" (REWRITE_RULE[ANT_UPDATE_ENVIRONMENT; SYSTEM_ENVIRONMENT; SYSTEM_AGENTS]));;
e (HYP_TAC "i2'" (CONV_RULE (TOP_SWEEP_CONV let_CONV)));;
e (HYP_TAC "i2'" (REWRITE_RULE[INVARIANT1]));;
e (REWRITE_TAC[ANT_UPDATE_SYSTEM; UPDATE_SYSTEM]);;
e (REWRITE_TAC[FORALL_IN_IMAGE; ANT_UPDATE_AGENTS_THM]);;
e (REWRITE_TAC[SYSTEM_ENVIRONMENT; SYSTEM_AGENTS]);;
e (INTRO_TAC "![ag']; keys ag'");;
e (ASM_REWRITE_TAC[INVARIANT2; SYSTEM_ENVIRONMENT]);;

e (REWRITE_TAC[ANT_UPDATE_ENVIRONMENT; SYSTEM_ENVIRONMENT; SYSTEM_AGENTS]);;
e (CONV_TAC (DEPTH_CONV let_CONV));;
e (REWRITE_TAC[INVARIANT1]);;
(* (map dest_var o variables o snd o top_goal) ();; *)
e (SUBGOAL_THEN
    `CARD {id:num | id IN KEYS ag' /\ FST (GET (ag':(num,num#direction#(direction,num#num#num#num,num)agent)dict) id) = 1} =
     CARD {id:num | id IN KEYS ag /\ FST (GET ag id) = 0} +
     CARD {id:num | id IN KEYS ag /\ FST (GET (ag:(num,num#direction#(direction,num#num#num#num,num)agent)dict) id) = 4}`
    SUBST1_TAC);;
e (SUBGOAL_THEN
     `!s t u:num->bool. FINITE s /\ FINITE t /\ DISJOINT s t /\ u = s UNION t
                        ==> CARD u = CARD s + CARD t`
     MATCH_MP_TAC);;
 e (REPEAT GEN_TAC THEN INTRO_TAC "s t disj u");;
 e (REMOVE_THEN "u" SUBST_VAR_TAC);;
 e (MATCH_MP_TAC CARD_UNION);;
 e (ASM_REWRITE_TAC[]);;
 e (REMOVE_THEN "disj" MP_TAC THEN SET_TAC[]);;
e CONJ_TAC;;
 e (MATCH_MP_TAC FINITE_SUBSET);;
 e (EXISTS_TAC `KEYS (ag:(num,num#direction#(direction,num#num#num#num,num)agent)dict)`);;
 e CONJ_TAC;;
  e (ASM_MESON_TAC[]);;
 e (REWRITE_TAC[SUBSET; FORALL_IN_GSPEC]);;
 e (MESON_TAC[]);;
e CONJ_TAC;;
 e (MATCH_MP_TAC FINITE_SUBSET);;
 e (EXISTS_TAC `KEYS (ag:(num,num#direction#(direction,num#num#num#num,num)agent)dict)`);;
 e CONJ_TAC;;
  e (ASM_MESON_TAC[]);;
 e (REWRITE_TAC[SUBSET; FORALL_IN_GSPEC]);;
 e (MESON_TAC[]);;
e CONJ_TAC;;
 e (REWRITE_TAC[DISJOINT; EXTENSION; NOT_IN_EMPTY; IN_INTER]);;
 e (REWRITE_TAC[IN_ELIM_THM]);;
 e (MESON_TAC[ARITH_RULE `~(0 = 4)`]);;
e (MATCH_MP_TAC SUBSET_ANTISYM);;
e CONJ_TAC;;
 e (REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNION]);;
 e (INTRO_TAC "!id; id pos");;


 e (LABEL_ABBREV_TAC
      `dir = FST (SND (GET (ag:(num,num#direction#(direction,num#num#num#num,num)agent)dict) id))`);;
 e (POP_ASSUM MP_TAC);;
 e (STRUCT_CASES_TAC (SPEC `dir:direction` (cases "direction")));;
  e (INTRO_TAC "dir");;
  e DISJ1_TAC;;
 e (HYP_TAC "ag'" (SPECL[`id:num`; `0`; `Forward`]));;
  e (REWRITE_TAC[IN_ELIM_THM]);;
  e CONJ_TAC;;
   e (ASM_MESON_TAC[]);;

  e (HYP_TAC "ag': +" (SPECL
       [ `SND (SND (GET (ag:(num,num#direction#(direction,num#num#num#num,num)agent)dict) id))`;
         `1`;
         `Forward`;
         `SND (SND (GET (ag:(num,num#direction#(direction,num#num#num#num,num)agent)dict) id))`;
       ]));;
  e (ASM_REWRITE_TAC[]);;
  e ANTS_TAC;;
   e (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]);;
   e CONJ_TAC;;
    e (ASM_REWRITE_TAC[PAIR_EXTENSION]);;

(type_of o rand o lhand o snd o top_goal) ();;




g `!s:system.
     let (s1,s2,s3) = SYSTEM_ENVIRONMENT s in
     let ag = SYSTEM_AGENTS s in
     FINITE (KEYS ag) /\
     s1 > s2 + s3 /\
     CARD {a | a IN KEYS ag /\ FST (GET ag a) = 1}
     >
     CARD {a | a IN KEYS ag /\ FST (GET ag a) = 2} +
     CARD {a | a IN KEYS ag /\ FST (GET ag a) = 3}
     ==>
     let u = ITER 2 (SETBIND ANT_UPDATE_SYSTEM) {s} in
     !s'. s' IN u
          ==> let ag' = SYSTEM_AGENTS s' in
              (!a. a IN KEYS ag' ==> FST (GET ag' a) IN {0,1,4})`;;
e GEN_TAC;;
e (LET_TAC THEN POP_ASSUM (LABEL_TAC "s123"));;
e (LET_TAC THEN POP_ASSUM (LABEL_TAC "ag"));;
e (INTRO_TAC "fin sti ag");;
e LET_TAC;;
e (POP_ASSUM (LABEL_TAC "u"));;
e (HYP_TAC "u" (REWRITE_RULE[TWO; ONE; ITER]));;
e (ABBREV_TAC `v = SETBIND ANT_UPDATE_SYSTEM {s}`);;
e (POP_ASSUM (LABEL_TAC "v"));;
e (HYP_TAC "v" (REWRITE_RULE[SETBIND_CLAUSES; UNION_EMPTY]));;
e (CLAIM_TAC "rmk"
     `!t. t IN v
          ==>
          let (t1,t2,t3) = SYSTEM_ENVIRONMENT t in
          let bg = SYSTEM_AGENTS t in
          FINITE (KEYS bg) /\
          t1 > t2 + t3 /\
          CARD {a | a IN KEYS bg /\ FST (GET bg a) = 1} >
          CARD {a | a IN KEYS bg /\ FST (GET bg a) = 2} +
          CARD {a | a IN KEYS bg /\ FST (GET bg a) = 3} /\
          (!a. a IN KEYS bg /\ FST (GET bg a) = 2
              ==> FST(SND(GET bg a)) = Backward) /\
          (!a. a IN KEYS bg /\ FST (GET bg a) = 3
              ==> FST(SND(GET bg a)) = Forward)`);;
 e (REMOVE_THEN "u" (K ALL_TAC));;
 e (INTRO_TAC "!t; t");;
 e (LET_TAC THEN POP_ASSUM (LABEL_TAC "t123"));;
 e (LET_TAC THEN POP_ASSUM (LABEL_TAC "bg"));;
 e CONJ_TAC;;
  e (REMOVE_THEN "bg" SUBST_VAR_TAC);;
  e (MATCH_MP_TAC FINITE_AGENTS_ANT_UPDATE_SYSTEM);;
  e (EXISTS_TAC `s:system`);;
  e (ASM_MESON_TAC[]);;
 e CONJ_TAC;;
  e (REMOVE_THEN "bg" (K ALL_TAC));;
  e (REMOVE_THEN "v" MP_TAC);;
  e (ASM_REWRITE_TAC[ANT_UPDATE_SYSTEM; UPDATE_SYSTEM; ANT_UPDATE_ENVIRONMENT]);;
  e (DISCH_THEN SUBST_VAR_TAC);;
  e (REMOVE_THEN "t" MP_TAC);;
  e (REWRITE_TAC[IN_IMAGE]);;
  e (INTRO_TAC "@x. t _");;
  e (POP_ASSUM SUBST_VAR_TAC);;
  e (REMOVE_THEN "t123" MP_TAC);;
  e (REWRITE_TAC[SYSTEM_ENVIRONMENT]);;
  e (CONV_TAC (TOP_SWEEP_CONV let_CONV));;
  e (REWRITE_TAC[PAIR_EQ]);;
  e ASM_ARITH_TAC;;
 e CONJ_TAC;; 
  e (REMOVE_THEN "t123" (K ALL_TAC));;
  e (REMOVE_THEN "bg" SUBST_VAR_TAC);;
  e (REMOVE_THEN "v" SUBST_VAR_TAC);;
  e (REMOVE_THEN "t" MP_TAC);;
  e (REWRITE_TAC[ANT_UPDATE_SYSTEM; UPDATE_SYSTEM; IN_IMAGE]);;
  e (INTRO_TAC "@d. t d");;
  e (REMOVE_THEN "t" SUBST_VAR_TAC);;
  e (REWRITE_TAC[SYSTEM_AGENTS]);;
  e (REMOVE_THEN "d" MP_TAC);;
  e (REWRITE_TAC[ANT_UPDATE_AGENTS_THM]);;
  e (INTRO_TAC "keys ag");;

{a | a IN KEYS d /\ FST (GET d a) = 1} =
{a | a IN KEYS d /\ FST (GET d a) = 0 \/ FST (GET d a) = 0}


  (* search[`DICT_COLLECT`];; *)
  e (ASM_REWRITE_TAC[IN_DICT_COLLECT; KEYS_FUNDICT; GET_FUNDICT]);;
  e (SIMP_TAC[]);;

(* ----------------------------------------------------------------------- *)
(* ----------------------------------------------------------------------- *)
(*    SIMULAZIONI                                                          *)
(* ----------------------------------------------------------------------- *)
(* ----------------------------------------------------------------------- *)

add_ants_thl [FINITE_EMPTY; FINITE_INSERT; GETOPTION];;

(* Una formica, 2 step. *)
let tm0 = time (run_conv
   (ANTS_COMPUTE_CONV THENC REWRITE_CONV[]))
  `SETBIND ANT_UPDATE_SYSTEM
   (ANT_UPDATE_SYSTEM
     (let sti = (0,0,0) in
      let ants = (UPDATE EMPTYDICT 0 (1,Forward,ANT)) in
      System(sti,ants):system))`;;

(* 2 formiche, 2 step. *)
let tm0 = time (run_conv
   (ANTS_COMPUTE_CONV THENC REWRITE_CONV[]))
  `SETBIND ANT_UPDATE_SYSTEM
   (ANT_UPDATE_SYSTEM
     (let sti = (0,0,0) in
      let ants =
        UPDATE (UPDATE EMPTYDICT 0 (1,Forward,ANT)) 1 (2,Forward,ANT) in
      System(sti,ants):system))`;;

(* 3 formiche, 2 step. *)
let tm0 = time (run_conv
   (ANTS_COMPUTE_CONV THENC REWRITE_CONV[]))
  `SETBIND ANT_UPDATE_SYSTEM
   (ANT_UPDATE_SYSTEM
     (let sti = (0,0,0) in
      let ants =
         UPDATE
           (UPDATE (UPDATE EMPTYDICT 0 (1,Forward,ANT))
             1 (2,Forward,ANT))
             2 (3,Backward,ANT) in
      System(sti,ants):system))`;;

let tm0 = time (run_conv
   (ANTS_COMPUTE_CONV THENC REWRITE_CONV[]))
  `SETBIND ANT_UPDATE_SYSTEM
   (SETBIND ANT_UPDATE_SYSTEM
   (ANT_UPDATE_SYSTEM
     (let sti = (0,0,0) in
      let ants =
         UPDATE
           (UPDATE (UPDATE EMPTYDICT 0 (1,Forward,ANT))
             1 (2,Forward,ANT))
             2 (3,Backward,ANT) in
      System(sti,ants):system)))`;;

(* 4 formiche, 3 step *)
let tm0 = time (run_conv
   (ANTS_COMPUTE_CONV THENC
    REWRITE_CONV[]))
  `SETBIND ANT_UPDATE_SYSTEM
   (SETBIND ANT_UPDATE_SYSTEM
   (ANT_UPDATE_SYSTEM
     (let sti = (0,0,0) in
      let ants =
        UPDATE (UPDATE (UPDATE (UPDATE EMPTYDICT 0 (1,Forward,ANT))
                               1 (0,Forward,ANT))
               2 (2,Forward,ANT))
        3 (3,Backward,ANT) in
      System(sti,ants):system)))`;;





let DICTMERGE_TRIE = prove
 (`!op:A->A->A d e.
     DICT_MERGE op (Dict (DICTTRIE d)) (Dict (DICTTRIE e)) =
     Dict (DICTTRIE (DICTMERGE op d e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DICT_MERGE; DICTTRIE] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; LOOKUP; DICTMERGE]);;


(lhand o rand o lhand o rand o rand) tm0;;



(* VECCHIE SIMULAZIONI *)

(* --------------------------------------------------- *)
let tm0 = time (run_conv
   (ANTS_COMPUTE_CONV THENC
    REWRITE_CONV[]))
  `ANT_UPDATE_SYSTEM
     (let sti = (\pos. 0) in
      let ants =
         UPDATE
           (UPDATE (UPDATE EMPTYDICT (Ident 0) (Position 1,Forward,ANT))
             (Ident 1) (Position 2,Forward,ANT))
           (Ident 2) (Position 3,Backward,ANT) in
      System(sti,ants):system)`;;


let get_binop tm = rator (rator tm);;
get_binop tm0;;
lhand tm0;;

let tm1 = mk_icomb (`ANT_UPDATE_SYSTEM`,lhand tm0);;
type_of tm1;;

let etm = `{}:(position->num,ident,position,direction,perception,position)system->bool`;;

g (mk_eq(tm1,etm));;
e (REWRITE_TAC[ANT_UPDATE_SYSTEM]);;
e (REWRITE_TAC[UPDATE_SYSTEM]);;
e (GEN_REWRITE_TAC I [IMAGE_EQ_EMPTY]);;
e (REWRITE_TAC[ANT_UPDATE_AGENTS]);;
e (REWRITE_TAC[DICT_COLLECT_EQ_EMPTY]);;
e (REWRITE_TAC[KEYS_FUNDICT; SYSTEM_AGENTS; KEYS_UPDATE; KEYS_EMPTYDICT]);;
e (REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY]);;
e (CONV_TAC ANTS_COMPUTE_CONV);;


e (REWRITE_TAC[GET_FUNDICT; IN_INSERT]);;
e (REWRITE_TAC[GET_UPDATE]);;
e (CONV_TAC (ONCE_DEPTH_CONV let_CONV));;
e (CONV_TAC ANTS_COMPUTE_CONV);;
e (REWRITE_TAC[IMAGE_EQ_EMPTY]);;
e (REWRITE_TAC[SYSTEM_AGENTS; KEYS_UPDATE; GET_UPDATE; IMAGE_EQ_EMPTY; MK_INPUT; injectivity "ident"; ARITH_EQ]);;
e (CONV_TAC ANTS_COMPUTE_CONV);;
e (CONV_TAC (TOP_DEPTH_CONV let_CONV));;
e (REWRITE_TAC[]);;

GET_FUNDICT;;


search[`KEYS`; `SYSTEM_AGENTS`];;
DICT_COLLECT;;


let tm2 = time (run_conv
   (ANTS_COMPUTE_CONV THENC
    REWRITE_CONV[]))
   (mk_icomb (`ANT_UPDATE_SYSTEM`,lhand tm0));;


(* ------------------------------------------------------------------------ *)

let tm0 = time (
   (ANTS_COMPUTE_CONV THENC
    REWRITE_CONV[]))
  `SETBIND ANT_UPDATE_SYSTEM
   (ANT_UPDATE_SYSTEM
     (let sti = (\pos. 0) in
      let ants =
         UPDATE
           (UPDATE (UPDATE EMPTYDICT (Ident 0) (Position 1,Forward,ANT))
             (Ident 1) (Position 2,Forward,ANT))
           (Ident 2) (Position 3,Backward,ANT) in
      System(sti,ants):system))`;;

let tm0 = time (run_conv
   (ANTS_COMPUTE_CONV THENC
    REWRITE_CONV[]))
  `SETBIND ANT_UPDATE_SYSTEM
   (ANT_UPDATE_SYSTEM
     (let sti = (\pos. 0) in
      let ants = (UPDATE EMPTYDICT (Ident 0) (Position 1,Forward,ANT)) in
      System(sti,ants):system))`;;

g `!s f:A->B->bool. SETBIND f s = {} <=> !x. x IN s ==> f x = {}`;;
e (REPEAT GEN_TAC THEN REWRITE_TAC[SETBIND; EMPTY_UNIONS]);;
e (SET_TAC[]);;
let SETBIND_EQ_EMPTY = top_thm();;


g `SETBIND ANT_UPDATE_SYSTEM
   (ANT_UPDATE_SYSTEM
     (let sti = (\pos. 0) in
      let ants = (UPDATE EMPTYDICT (Ident 0) (Position 1,Forward,ANT)) in
      System(sti,ants):system)) = {}`;;
e (REWRITE_TAC[SETBIND_EQ_EMPTY]);;
e (CONV_TAC (ONCE_DEPTH_CONV (CHANGED_CONV ANTS_COMPUTE_CONV)));;
e (REWRITE_TAC[IN_SING]);;


let tm1 = length (dest_setenum tm0);;

DICT_GET_EXTENSION;;

let tm1 = (get_binop o rand o rand o rand) tm0;;
let tm1 = (get_binop o rand o rand o rand o rand) tm0;;
let tm1 = (get_binop o lhand o rand o rand o rand) tm0;;

ANTS_COMPUTE_CONV `{Ident 1,Ident 2,Ident 3} UNION {Ident 2,Ident 5}`;;
INSERT_UNION;;
INSERT_UNION;;

search[`DICT_RESTRICT`; `UPDATE`];;

search[`DICT_RESTRICT`; `{}`];;

search[`FUNDICT`; `INSERT`];;

let `KEYS (SYSTEM_AGENTS sys)`
let DICT_COLLECT_FUNDICT = 

let tm1 = rand (rand tm0);;

let tm2 = (RAND_CONV ANTS_COMPUTE_CONV THENC
 REWRITE_CONV[SETBIND_CLAUSES; UNION_EMPTY] THENC
 ONCE_REWRITE_CONV[COLLECT_IDENT_REINDEX] THENC
 ONCE_REWRITE_CONV[COLLECT_EQ_SETBIND] THENC
 REWRITE_CONV[o_THM]
) tm1;;

let tm3 = funpow 3 rand (rhs (concl tm2));;
ANTS_COMPUTE_CONV tm3;;


let tm0 = time (run_conv
   (ANTS_COMPUTE_CONV THENC
    ONCE_REWRITE_CONV[COLLECT_IDENT_REINDEX] THENC
    ONCE_REWRITE_CONV[COLLECT_EQ_SETBIND] THENC
    ANTS_COMPUTE_CONV))
  `ANT_UPDATE_SYSTEM
     (let sti = (\pos. 0) in
      let ants = (\id. match id with
                       | Ident 0 -> Position 1,Forward,ANT
                       | Ident 1 -> Position 2,Forward,ANT
                       | Ident 2 -> Position 3,Backward,ANT
                       | Ident _ -> Position 0,Forward,DUMBANT) in
                       System(sti,ants):system)`;;

1;;
rand (rand (rand tm0));;
