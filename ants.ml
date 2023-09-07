prioritize_num();;

needs "Agents/dict.ml";;

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

let DICT_COMBINE = new_definition
  `DICT_COMBINE (op:A->A->A) d1 d2 =
   Dict (\k:K. lifted op (LOOKUPOPT d1 k) (LOOKUPOPT d2 k))`;;

let OPTION_MAP = define
  `(!f:A->B. OPTION_MAP f NONE = NONE) /\
   (!f:A->B x. OPTION_MAP f (SOME x) = SOME (f x))`;;

let DICT_MAP = new_definition
  `DICT_MAP (f:A -> B) (d:(K,A)dict) : (K,B)dict =
   Dict(\k. OPTION_MAP f (LOOKUPOPT d k))`;;

(* ------------------------------------------------------------------------- *)

let status_INDUCT,status_RECUR = define_type
  "status = Status ((position,num)dict # (num,(position#direction))dict)";;

let ST_STIGMERGY = define
  `ST_STIGMERGY (Status (sti,ants)) = sti`;; 

let ST_ANTS = define
  `ST_ANTS (Status (sti,ants)) = ants`;; 

let ANT_STEP = new_definition
  `ANT_STEP (stigmergy:(position,num)dict) (i:position) (dir:direction) :
     (position#direction)->bool =
     if i = 0 then
       if LOOKUP stigmergy 1 < LOOKUP stigmergy 2 then {(2,Forward)} else
       if LOOKUP stigmergy 2 < LOOKUP stigmergy 1 then {(1,Forward)} else
         {(1,Forward),(2,Forward)}
     else if i = 4 then
       if LOOKUP stigmergy 1 < LOOKUP stigmergy 3 then {(3,Backward)} else
       if LOOKUP stigmergy 3 < LOOKUP stigmergy 1 then {(1,Backward)} else
         {(1,Backward),(3,Backward)}
     else
       if i = 1 then {(4,dir)} else
       if i = 2 /\ dir = Forward then {(3,Forward)} else
       if i = 2 /\ dir = Backward then {(0,Backward)} else
       if i = 3 /\ dir = Forward then {(4,Forward)} else
       if i = 3 /\ dir = Backward then {(2,Backward)} else
       {}`;;

(* `DICT_MAP (UNCURRY (ANT_STEP (ST_STIGMERGY s))) (ST_ANTS s)`;; *)

let DICT_COLLECT = new_definition
  `DICT_COLLECT (d:(K,V->bool)dict) : (K,V)dict->bool =
   {e | KEYS e = KEYS d /\ !k. k IN KEYS e ==> LOOKUP e k IN LOOKUP d k}`;;

(* type_of
`DICT_COLLECT (DICT_MAP (UNCURRY (ANT_STEP (ST_STIGMERGY s))) (ST_ANTS s))`;; *)

let EVOLUTION_STEP = new_definition
  `EVOLUTION_STEP (s:status) =
   { Status (
       DICT_COMBINE (+) (ST_STIGMERGY s)
         (Dict(\i:position.
                 if i IN VALID_POSITIONS then
                   SOME (CARD{a | ?d. LOOKUPOPT(ST_ANTS s) a = SOME(i,d)})
                 else
                   NONE
              )
         )
     ,
       ants
     )
   | ants |
     ants IN DICT_COLLECT
               (DICT_MAP (UNCURRY (ANT_STEP (ST_STIGMERGY s))) (ST_ANTS s))  
   }`;;

let EVOLUTION = new_recursive_definition num_RECURSION
  `(!s. EVOLUTION s 0 = {s}) /\
   (!s i. EVOLUTION s (SUC i) =
          {s | s, s' | s IN EVOLUTION_STEP s' /\ s' IN (EVOLUTION s i)})`;;
