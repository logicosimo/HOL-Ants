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


(* ----------------------------------------------------------------------- *)
(* ----------------------------------------------------------------------- *)
(*    SIMULAZIONI  *)
(* ----------------------------------------------------------------------- *)
(* ----------------------------------------------------------------------- *)

add_ants_thl [FINITE_EMPTY; FINITE_INSERT; GETOPTION];;


(* Una formica, 2 step. *)
let tm0 = time (run_conv
   (ANTS_COMPUTE_CONV THENC
    REWRITE_CONV[]))
  `SETBIND ANT_UPDATE_SYSTEM
   (ANT_UPDATE_SYSTEM
     (let sti = (0,0,0) in
      let ants = (UPDATE EMPTYDICT 0 (1,Forward,ANT)) in
      System(sti,ants):system))`;;

(* 2 formiche, 2 step. *)
let tm0 = time (run_conv
   (ANTS_COMPUTE_CONV THENC
    REWRITE_CONV[]))
  `SETBIND ANT_UPDATE_SYSTEM
   (ANT_UPDATE_SYSTEM
     (let sti = (0,0,0) in
      let ants =
        UPDATE (UPDATE EMPTYDICT 0 (1,Forward,ANT)) 1 (2,Forward,ANT) in
      System(sti,ants):system))`;;

(* 3 formiche, 2 step. *)
let tm0 = time (run_conv
   (ANTS_COMPUTE_CONV THENC
    REWRITE_CONV[]))
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
   (ANTS_COMPUTE_CONV THENC
    REWRITE_CONV[]))
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
