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

(* Perception( location : location
             , neighborhood : num->bool
             , directions : num->direction
             )
 *)
let perception_INDUCT,perception_RECUR = define_type
  "perception = Perception(location #
                           (num->bool) #
                           (num->direction))";;

let PERCEPTION_LOCATION = define
  `PERCEPTION_LOCATION (Perception(loc,nbh,dirs)) = loc`;;

let PERCEPTION_NEIGHBORHOOD = define
  `PERCEPTION_NEIGHBORHOOD (Perception(loc,nbh,dirs)) = nbh`;;

let PERCEPTION_DIRECTIONS = define
  `PERCEPTION_DIRECTIONS (Perception(loc,nbh,dirs)) = dirs`;;

add_ants_thl[injectivity "perception"; PERCEPTION_LOCATION;
  PERCEPTION_NEIGHBORHOOD; PERCEPTION_DIRECTIONS];;

let MK_PERCEPTION = new_definition
  `MK_PERCEPTION (pos:num) : perception =
   let loc:location = LOCATION pos in
   let positions = {j | pos,j IN MOVES} in
   let dirs = \p. if pos,p IN FORWARD_MOVES
                    then Forward
                    else Backward in
   Perception(loc,positions,dirs)`;;

let MK_PERCEPTION_THM = prove
 (`MK_PERCEPTION (pos:num) : perception =
   let loc:location = LOCATION pos in
   let positions = IMAGE SND MOVES in
   let dirs = \p. if pos,p IN FORWARD_MOVES
                  then Forward
                  else Backward in
   Perception(loc,positions,dirs)`,
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
  `UPDATE_POSITION (pos:num) (dir:direction)
     (s1:num,s2:num,s3:num) : num->bool =
   match pos with
   | 0 -> if s1 < s2 then {2} else
          if s2 < s1 then {1} else
          {1,2}
   | 1 -> (match dir with Forward -> {4} | Backward -> {0}) 
   | 2 -> (match dir with Forward -> {3} | Backward -> {0}) 
   | 3 -> (match dir with Forward -> {4} | Backward -> {2}) 
   | 4 -> if s1 < s3 then {3} else
          if s3 < s1 then {1} else
          {1,3}`;;

add_ants_thl[UPDATE_POSITION];;

new_type_abbrev("ant",`:(status,num#(num#num#num),num)agent`);;

type_of `(ANT : ant = Agent f), f`;;

let ANT = new_definition
  `ANT : ant =
   Agent(\inp.
     let dir = INPUT_STATUS inp in
     let pos,sti = INPUT_PERCEPTION inp in
     IMAGE (\p. UPDATE_DIRECTION (LOCATION p) dir,p)
           (UPDATE_POSITION pos dir sti))`;;

(* let ANT_THM = prove
 (`!inp:(status,perception)input.
     AGENT_STEP ANT inp =
     IMAGE (\pos. UPDATE_DIRECTION (LOCATION pos) (INPUT_STATUS inp),pos)
           (UPDATE_POSITION inp)`,
  REWRITE_TAC[ANT; AGENT_STEP; injectivity "agent"] THEN SET_TAC[]);; *)

add_ants_thl[ANT];;
