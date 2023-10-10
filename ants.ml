prioritize_num();;

(* needs "Agents/dict.ml";; *)
(* needs "Agents/setbind.ml";; *)

(* ------------------------------------------------------------------------- *)
(* Status for ants.                                                          *)
(* ------------------------------------------------------------------------- *)

let direction_INDUCT,direction_RECUR = define_type
  "direction = Forward | Backward";;

(* ------------------------------------------------------------------------- *)
(* Positions and moves.                                                      *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("position",`:num`);;

let VALID_POSITIONS = new_definition
  `VALID_POSITIONS : position -> bool = {0,1,2,3,4}`;;

let IN_VALID_POSITIONS =
  REWRITE_CONV[VALID_POSITIONS; IN_INSERT; NOT_IN_EMPTY]
    `i IN VALID_POSITIONS`;;

let FORWARD_MOVES = new_definition
  `FORWARD_MOVES = {(0,1),(1,4),(0,2),(2,3),(3,4)}`;;

let IN_FORWARD_MOVES_EXPLICIT =
  REWRITE_CONV[FORWARD_MOVES; IN_INSERT; NOT_IN_EMPTY; PAIR_EQ]
    `(i,j) IN FORWARD_MOVES`;;

let BACKWARD_MOVES = new_definition
  `BACKWARD_MOVES = {(i,j) | (j,i) IN FORWARD_MOVES}`;;

let IN_BACKWARD_FORWARD_MOVES = prove
 (`!i j. (i,j) IN BACKWARD_MOVES <=> (j,i) IN FORWARD_MOVES`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BACKWARD_MOVES; IN_ELIM_THM; PAIR_EQ] THEN
  MESON_TAC[]);;

let IN_BACKWARD_MOVES_EXPLICIT =
  REWRITE_CONV[IN_BACKWARD_FORWARD_MOVES; IN_FORWARD_MOVES_EXPLICIT]
    `(i,j) IN BACKWARD_MOVES`;;

let MOVES = new_definition
  `MOVES = FORWARD_MOVES UNION BACKWARD_MOVES`;;

let IN_MOVES_THM = prove
 (`!m. m IN MOVES <=> m IN FORWARD_MOVES \/ m IN BACKWARD_MOVES`,
  REWRITE_TAC[MOVES; IN_UNION]);;

let IN_MOVES_EXPLICT =
  REWRITE_CONV[IN_MOVES_THM; IN_FORWARD_MOVES_EXPLICIT;
               IN_BACKWARD_MOVES_EXPLICIT; GSYM DISJ_ASSOC]
    `(i,j) IN MOVES`;;

(* ------------------------------------------------------------------------- *)
(* Lemmata.                                                                  *)
(* ------------------------------------------------------------------------- *)

let DISJ_IMP_THM = MESON[]
  `((A \/ B) ==> C) <=> (A ==> C) /\ (B ==> C)`;;

let FORALL_IN_FORWARD_MOVES =
  REWRITE_CONV[IN_FORWARD_MOVES_EXPLICIT; FORALL_AND_THM; IMP_CONJ;
               RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2; DISJ_IMP_THM]
    `(!i j. (i,j) IN FORWARD_MOVES ==> P i j)`;;

let FORALL_IN_BACKWARD_MOVES =
  REWRITE_CONV[IN_BACKWARD_MOVES_EXPLICIT; FORALL_AND_THM; IMP_CONJ;
               RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2; DISJ_IMP_THM]
    `(!i j. (i,j) IN BACKWARD_MOVES ==> P i j)`;;

(* ------------------------------------------------------------------------- *)
(* Sanity checks.                                                            *)
(* ------------------------------------------------------------------------- *)

let FORWARD_MOVES_IN_VALID_POSITIONS = prove
 (`!i j. (i,j) IN FORWARD_MOVES
         ==> i IN VALID_POSITIONS /\ j IN VALID_POSITIONS`,
  REWRITE_TAC[FORALL_IN_FORWARD_MOVES; IN_VALID_POSITIONS]);;

let BACKWARD_MOVES_IN_VALID_POSITIONS = prove
 (`!i j. (i,j) IN BACKWARD_MOVES
         ==> i IN VALID_POSITIONS /\ j IN VALID_POSITIONS`,
  REWRITE_TAC[FORALL_IN_BACKWARD_MOVES; IN_VALID_POSITIONS]);;

(* ------------------------------------------------------------------------- *)
(* Ants.                                                                     *)
(* ------------------------------------------------------------------------- *)

(* Uno stato è una coppia
     1. dizionario posizione->nat (ferormoni)  (stigmergy)
     2. dizionario idant->(posizione,direzione)  (ants)
 *)
let status_INDUCT,status_RECUR = define_type
  "status = Status ((position,num)dict # (num,(position#direction))dict)";;

let ST_STIGMERGY = define
  `ST_STIGMERGY (Status(sti,ants)) = sti`;;

let ST_ANTS = define
  `ST_ANTS (Status (sti,ants)) = ants`;;

(* `ANT_STEP:(num,num)dict->num->direction->num#direction->bool` *)
let ANT_STEP = new_definition
  `ANT_STEP (stigmergy:(position,num)dict) (i:position,dir:direction) :
     (position#direction)->bool =
     if i = 0 then
       if GET stigmergy 1 < GET stigmergy 2 then {(2,Forward)} else
       if GET stigmergy 2 < GET stigmergy 1 then {(1,Forward)} else
         {(1,Forward),(2,Forward)}
     else if i = 4 then
       if GET stigmergy 1 < GET stigmergy 3 then {(3,Backward)} else
       if GET stigmergy 3 < GET stigmergy 1 then {(1,Backward)} else
         {(1,Backward),(3,Backward)}
     else
       if i = 1 then {(4,dir)} else
       if i = 2 /\ dir = Forward then {(3,Forward)} else
       if i = 2 /\ dir = Backward then {(0,Backward)} else
       if i = 3 /\ dir = Forward then {(4,Forward)} else
       if i = 3 /\ dir = Backward then {(2,Backward)} else
       {}`;;

let UPDATE_STIGMERGY = new_definition
  `UPDATE_STIGMERGY (st:status) : (num,num)dict =
   DICT_MERGE (+) (ST_STIGMERGY st)
                  (DICT_MAP CARD
                            (DICT_TRANSPOSE (DICT_MAP FST (ST_ANTS st))))`;;

let EVOLUTION_STEP = new_definition
  `EVOLUTION_STEP (s:status) : status->bool =
   IMAGE (\ants. Status (UPDATE_STIGMERGY s,ants))
         (DICT_COLLECT (DICT_MAP (ANT_STEP (ST_STIGMERGY s))
                                 (ST_ANTS s)))`;;

needs "Library/iter.ml";;

let EVOLUTION = new_definition
  `EVOLUTION s k = ITER k (SETBIND EVOLUTION_STEP) {s}`;;

(
RAND_CONV (TOP_DEPTH_CONV num_CONV) THENC
REWRITE_CONV[EVOLUTION; ITER; SETBIND_CLAUSES; UNION_EMPTY; EVOLUTION_STEP;
             ST_ANTS; ST_STIGMERGY; ANT_STEP; DICT_MAP_DICT_UNION;
             DICT_MAP_PAIRDICT] THENC
NUM_REDUCE_CONV THENC
REWRITE_CONV[distinctness "direction"; DICT_COLLECT_DICT_UNION;
  KEYS_DICT_UNION; KEYS_PAIRDICT; DICT_COLLECT_PAIRDICT;
  IMAGE_CLAUSES; SETBIND_CLAUSES; UNION_EMPTY;
  SET_RULE `(r UNION s) DIFF t = (r DIFF t) UNION (s DIFF t)`;
  DIFF_INSERT; DIFF_EMPTY; DELETE_INSERT; EMPTY_DELETE; ARITH_EQ;
  INSERT_UNION; IN_INSERT; NOT_IN_EMPTY; DICT_RESTRICT_INSERT;
  DICT_RESTRICT_EMPTY;
  GET_DICT_UNION; GET_PAIRDICT; DICT_COLLECT_UPDATE; KEYS_UPDATE;
  KEYS_EMPTYDICT; EMPTY_DELETE; DICT_COLLECT_EMPTYDICT; GET_UPDATE;
  UPDATE_STIGMERGY; DICT_UNION_PAIRDICT; ST_ANTS; ST_STIGMERGY;
  DICT_MAP_UPDATE; DICT_MAP_PAIRDICT; DICT_MERGE_EMPTYDICT;
  DICT_TRANSPOSE_UPDATE; REMOVE_UPDATE; REMOVE_PAIRDICT;
  DICT_TRANSPOSE_PAIRDICT; DICT_MERGE_PAIRDICT; UPDATE_IDEMPOT] THENC
SIMP_CONV[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY;
          ARITH_EQ; ARITH_SUC] THENC
REWRITE_CONV[EVOLUTION_STEP; ST_ANTS; ST_STIGMERGY; ANT_STEP;
  DICT_MAP_UPDATE; DICT_MAP_EMPTYDICT; ARITH_EQ; GET_UPDATE; GET_PAIRDICT;
  distinctness "direction"; ARITH_LT; ARITH_LE;
  DICT_COLLECT_UPDATE; DICT_COLLECT_EMPTYDICT; KEYS_UPDATE; KEYS_EMPTYDICT;
  DICT_RESTRICT_INSERT; DICT_RESTRICT_EMPTY; DELETE_INSERT; EMPTY_DELETE;
  SETBIND_CLAUSES; UNION_EMPTY; IMAGE_CLAUSES;
  UPDATE_STIGMERGY; DICT_TRANSPOSE_UPDATE; DICT_TRANSPOSE_EMPTYDICT;
  REMOVE_UPDATE; REMOVE_EMPTYDICT;
  DICT_MERGE_PAIRDICT; IN_INSERT; NOT_IN_EMPTY; INSERT_UNION; UNION_EMPTY;
  DICT_MERGE_UPDATE; CARD_SING; ARITH_ADD; ARITH_SUC; UPDATE_IDEMPOT] THENC
SIMP_CONV[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY;
          ARITH_EQ; ARITH_SUC]
)
`EVOLUTION
       (Status(EMPTYDICT,
        DICT_UNION (0 => (1,Forward))
        (DICT_UNION (1 => (1,Backward))
        (DICT_UNION (2 => (2,Forward))
                    (3 => (3,Backward))))))
     2`;;
