(* ========================================================================= *)
(* Nondeterministic agents in HOL.                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Miscellanea.                                                              *)
(* ------------------------------------------------------------------------- *)

(* let ITERSETBIND = new_definition
  `ITERSETBIND (f:A->A->bool) (n:num) : (A->bool) -> (A->bool) =
   ITER n (SETBIND f)`;; *)

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

remove_type_abbrev "position";;

let MOVES_THM = prove
 (`MOVES = {(0,1),(1,4),(0,2),(2,3),(3,4),(1,0),(4,1),(2,0),(3,2),(4,3)}`,
  REWRITE_TAC[MOVES; GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_INSERT;
              NOT_IN_EMPTY; FORALL_IN_UNION] THEN
  REWRITE_TAC[FORALL_PAIR_THM; FORALL_IN_FORWARD_MOVES;
              FORALL_IN_BACKWARD_MOVES] THEN
  REWRITE_TAC[IN_UNION; IN_FORWARD_MOVES_EXPLICIT; IN_BACKWARD_MOVES_EXPLICIT;
              IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN
  ARITH_TAC);;

add_ants_thl[MOVES_THM];;

(* ------------------------------------------------------------------------- *)
(* Nondeterministic agents.                                                  *)
(*                                                                           *)
(* Descriptions of the type parameters:                                      *)
(*   A = internal status of the agent                                        *)
(*   B = perception                                                          *)
(*       (information gathered by the agent about the surrounding env)       *)
(*   C = action (possible choices made by the agent)                         *)
(* ------------------------------------------------------------------------- *)

let input_INDUCT,input_RECUR = define_type
  "input = Input(A#B)";;

let INPUT_STATUS = define
  `INPUT_STATUS (Input(stat:Stat,percpt:Percpt)) = stat`;;

let INPUT_PERCEPTION = define
  `INPUT_PERCEPTION (Input(stat:Stat,percpt:Percpt)) = percpt`;;

add_ants_thl[injectivity "input"; INPUT_STATUS; INPUT_PERCEPTION];;

let agent_INDUCT,agent_RECUR = define_type
  "agent = Agent((A,B)input->A#C->bool)";;

let AGENT_STEP = define
  `AGENT_STEP (Agent(a:(Stat,Percpt)input->Stat#Action->bool)) = a`;;

add_ants_thl[injectivity "agent"; AGENT_STEP];;

(* ------------------------------------------------------------------------- *)
(* Ant agents.                                                               *)
(* ------------------------------------------------------------------------- *)

let CHOOSE_POSITION = new_definition
  `CHOOSE_POSITION (sti:Pos->num) (positions:Pos->bool) : Pos->bool =
   {pos | pos IN positions /\
          !pos'. pos' IN positions ==> sti pos' <= sti pos}`;;

let CHOOSE_POSITION_THM = prove
  (`CHOOSE_POSITION (sti:Pos->num) (positions:Pos->bool) : Pos->bool =
    SETFILTER (\pos. SETALL (\pos'. sti pos' <= sti pos) positions)
              positions`,
   REWRITE_TAC[CHOOSE_POSITION; SETALL; SETFILTER]);;

add_ants_thl[CHOOSE_POSITION_THM];;

let direction_INDUCT,direction_RECUR = define_type
  "direction = Forward | Backward";;

add_ants_thl[distinctness "direction"];;

let location_INDUCT,location_RECUR = define_type
  "location = Nest | Dest | Path";;

add_ants_thl[distinctness "location"];;

let LOCATION = new_definition
  `LOCATION (pos:num) : location = match pos with
                                   | 0 -> Nest
                                   | 4 -> Dest
                                   | _ -> Path`;;

add_ants_thl[LOCATION];;

let UPDATE_DIRECTION = new_definition
  `UPDATE_DIRECTION loc dir = match loc with
                             | Nest -> Forward
                             | Dest -> Backward
                             | Path -> dir`;;

add_ants_thl[UPDATE_DIRECTION];;

let perception_INDUCT,perception_RECUR = define_type
  "perception = Perception(location #
                           (num->bool) #
                           (num->num) #
                           (num->direction))";;

let PERCEPTION_LOCATION = define
  `PERCEPTION_LOCATION (Perception(loc,nbh,sti,dirs)) = loc`;;

let PERCEPTION_NEIGHBORHOOD = define
  `PERCEPTION_NEIGHBORHOOD (Perception(loc,nbh,sti,dirs)) = nbh`;;

let PERCEPTION_STIGMERGY = define
  `PERCEPTION_STIGMERGY (Perception(loc,nbh,sti,dirs)) = sti`;;

let PERCEPTION_DIRECTIONS = define
  `PERCEPTION_DIRECTIONS (Perception(loc,nbh,sti,dirs)) = dirs`;;

add_ants_thl[injectivity "perception"; PERCEPTION_LOCATION;
  PERCEPTION_NEIGHBORHOOD; PERCEPTION_STIGMERGY; PERCEPTION_DIRECTIONS];;

let MK_PERCEPTION = new_definition
  `MK_PERCEPTION (sti:num->num) (pos:num) : perception =
   let loc:location = LOCATION pos in
   let i = pos in
   let positions = {j | i,j IN MOVES} in
   let dirs = \pos. if i,pos IN FORWARD_MOVES
                    then Forward
                    else Backward in
   Perception(loc,positions,sti,dirs)`;;

let MK_PERCEPTION_THM = prove
 (`MK_PERCEPTION (sti:num->num) (pos:num) : perception =
   let loc:location = LOCATION pos in
   let Position i = pos in
   let positions = IMAGE SND MOVES in
   let dirs = \pos. if i,pos IN FORWARD_MOVES
                    then Forward
                    else Backward in
   Perception(loc,positions,sti,dirs)`,
  CHEAT_TAC);;

add_ants_thl[injectivity "perception"; MK_PERCEPTION_THM];;

new_type_abbrev("status",`:direction`);;

let ACCESSIBLE_POSITIONS = new_definition
  `ACCESSIBLE_POSITIONS (inp:(status,perception)input) : num->bool =
   let percpt = INPUT_PERCEPTION inp in
   let dir = INPUT_STATUS inp in
   let nbh = PERCEPTION_NEIGHBORHOOD percpt in
   {pos | pos IN nbh /\ PERCEPTION_DIRECTIONS percpt pos = dir}`;;

let ACCESSIBLE_POSITIONS_THM = prove
 (`ACCESSIBLE_POSITIONS (inp:(status,perception)input) : num->bool =
   let percpt = INPUT_PERCEPTION inp in
   let dir = INPUT_STATUS inp in
   let nbh = PERCEPTION_NEIGHBORHOOD percpt in
   SETFILTER (\pos. PERCEPTION_DIRECTIONS percpt pos = dir) nbh`,
  REWRITE_TAC[ACCESSIBLE_POSITIONS; SETFILTER]);;

add_ants_thl[ACCESSIBLE_POSITIONS_THM];;

let UPDATE_POSITION = new_definition
  `UPDATE_POSITION (inp:(status,perception)input) : num->bool =
   let percpt = INPUT_PERCEPTION inp in
   let dir = INPUT_STATUS inp in
   CHOOSE_POSITION (PERCEPTION_STIGMERGY percpt) (ACCESSIBLE_POSITIONS inp)`;;

add_ants_thl[UPDATE_POSITION];;

new_type_abbrev("ant",`:(status,perception,num)agent`);;

let ANT = new_definition
  `ANT : ant =
   Agent(\inp:(status,perception)input.
           {UPDATE_DIRECTION (LOCATION pos) (INPUT_STATUS inp),pos | pos |
            pos IN UPDATE_POSITION inp})`;;

g `ANT : ant =
   Agent(\inp:(status,perception)input.
           IMAGE (\pos. UPDATE_DIRECTION (LOCATION pos) (INPUT_STATUS inp),pos)
                 (UPDATE_POSITION inp))`;;
e (REWRITE_TAC[ANT; injectivity "agent"]);;
e (ONCE_REWRITE_TAC[FUN_EQ_THM] THEN FIX_TAC "[inp]");;
e (REWRITE_TAC[]);;
e (SET_TAC[]);;
let ANT_THM = top_thm();;

add_ants_thl[ANT_THM];;
