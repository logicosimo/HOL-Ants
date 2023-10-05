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
  `ANT_STEP (stigmergy:(position,num)dict) (i:position) (dir:direction) :
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
   { Status (UPDATE_STIGMERGY s,ants) | ants |
     ants IN DICT_COLLECT
               (DICT_MAP (UNCURRY (ANT_STEP (ST_STIGMERGY s)))
                         (ST_ANTS s)) }`;;
let EVOLUTION = new_recursive_definition num_RECURSION
  `(!s. EVOLUTION s 0 = {s}) /\
   (!s i. EVOLUTION s (SUC i) =
          {s | s, s' | s IN EVOLUTION_STEP s' /\ s' IN (EVOLUTION s i)})`;;
