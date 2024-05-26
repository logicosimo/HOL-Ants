(* ========================================================================= *)
(* Nondeterministic agents in HOL.                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Miscellanea.                                                              *)
(* ------------------------------------------------------------------------- *)

needs "Library/iter.ml";;
needs "code/HOL-Ants/setbind.ml";;
needs "code/HOL-Ants/dict.ml";;

let nmax = new_definition
  `nmax (s:A->bool) (f:A->num) =
   @m. (!x. x IN s ==> f x <= m) /\ (?x. x IN s /\ f x = m)`;;

let ITERSETBIND = new_definition
  `ITERSETBIND (f:A->A->bool) (n:num) : (A->bool) -> (A->bool) =
   ITER n (SETBIND f)`;;

let COLLECT = new_definition
  `COLLECT (u:A->B->bool) : (A->B)->bool = {f : A -> B | !x. f x IN u x}`;;

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

(* ------------------------------------------------------------------------- *)
(* Nondeterministic agents.                                                  *)
(*                                                                           *)
(* Descriptions of the type parameters:                                      *)
(*   A = internal status of the agent                                        *)
(*   B = perception                                                          *)
(*       (information gathered by the agent about the surrounding env)       *)
(*   C = action (possible choices made by the agent)                         *)
(* ------------------------------------------------------------------------- *)

let agent_INDUCT,agent_RECUR = define_type
  "agent = Agent(A#B->A#C->bool)";;

let AGENT_STEP = define
  `AGENT_STEP (Agent(a:Stat#Percpt->Stat#Action->bool)) = a`;;

(* ------------------------------------------------------------------------- *)
(* Ants.                                                                     *)
(* ------------------------------------------------------------------------- *)

let CHOOSE_POSITION = new_definition
  `CHOOSE_POSITION (sti:Pos->num) (positions:Pos->bool) : Pos->bool =
   {pos | pos IN positions /\ sti pos = nmax positions sti}`;;

let direction_INDUCT,direction_RECUR = define_type
  "direction = Forward | Backward";;

let location_INDUCT,location_RECUR = define_type
  "location = Nest | Dest | Path";;

let position_INDUCT,position_RECUR = define_type
  "position = Position num";;

let LOCATION = new_definition
  `LOCATION (pos:position) : location = match pos with
                                        | Position 0 -> Nest
                                        | Position 4 -> Dest
                                        | Position _ -> Path`;;

let UPADATE_DIRECTION = new_definition
  `UPADATE_DIRECTION loc dir = match loc with
                             | Nest -> Forward
                             | Dest -> Backward
                             | Path -> dir`;;

new_type_abbrev("status",`:direction`);;
new_type_abbrev("perception",`:location#(position,num#direction)dict`);;
new_type_abbrev("input",`:status#perception`);;

let PERCEPTION_STIGMERGY = new_definition
  `PERCEPTION_STIGMERGY (nbh:perception) : position->num =
   let loc,dict = nbh in
   GETDEFAULT (DICT_MAP FST dict) 0`;;

let PERCEPTION_DIRECTION = new_definition
  `PERCEPTION_DIRECTION (percpt:perception) : position->direction =
   let loc,dict = percpt in
   GET (DICT_MAP SND dict)`;;

let ACCESSIBLE_POSITIONS = new_definition
  `ACCESSIBLE_POSITIONS (inp:input) : position->bool =
   let (dir:status,inp:perception) = inp in
   {pos | pos IN KEYS (SND inp) /\ PERCEPTION_DIRECTION inp pos = dir}`;;

let UPDATE_POSITION = new_definition
  `UPDATE_POSITION (inp:input) : position->bool =
   let dir,percpt = inp in
   CHOOSE_POSITION (PERCEPTION_STIGMERGY percpt) (ACCESSIBLE_POSITIONS inp)`;;

new_type_abbrev("ant",`:(status,perception,position)agent`);;

let ANT = new_definition
  `ANT : ant =
   Agent(\inp:input.
            let dir,percpt = inp in
            let loc,dict = percpt in
            let newdir:status = UPADATE_DIRECTION loc dir in
            {newdir,pos | pos | pos IN UPDATE_POSITION inp})`;;

(* ========================================================================= *)
(* ========================================================================= *)
(* ========================================================================= *)

new_type_abbrev("ident",`:num`);;
new_type_abbrev("ants",
                `:( ident
                  , position#status#ant
                  ) dict`);;

let ANT_POSITION = new_definition
  `ANT_POSITION (ants:ants) (id:ident) : position =
   let pos,_ = GET ants id in
   pos`;;

let ANT_STATUS = new_definition
  `ANT_STATUS (ants:ants) (id:ident) : status =
   let pos,stat,_ = GET ants id in
   stat`;;

let ANT_AGENT = new_definition
  `ANT_AGENT (ants:ants) (id:ident) : ant =
   let pos,stat,ag = GET ants id in
   ag`;;

let GET_PERCEPTION = new_definition
  `GET_PERCEPTION (sti:position->num) (pos:position) : perception =
   let Position i = pos in
   let loc:location = LOCATION pos in
   let dict = Dict(\pos.
     let Position j = pos in
     if i,j IN FORWARD_MOVES then
       SOME (sti (Position j),Forward)
     else if i,j IN BACKWARD_MOVES then
       SOME (sti (Position j),Backward)
     else NONE) in
   loc,dict`;;

(* ------------------------------------------------------------------------- *)
(* System.                                                                   *)
(* ------------------------------------------------------------------------- *)

let system_INDUCT,system_RECUR = define_type
  "system = System((position->num)#ants)";;

let SYS_STIGMERGY = define
  `SYS_STIGMERGY (System(sti,ants)) : position->num = sti`;;

let SYS_ANTS = define
  `SYS_ANTS (System(sti,ants)) = ants`;;

let UPDATE_STIGMERGY = new_definition
  `UPDATE_STIGMERGY (sys:system) (pos:position) =
   SYS_STIGMERGY sys pos + CARD {id | ANT_POSITION (SYS_ANTS sys) id = pos}`;;

let SYS_INPUT = new_definition
  `SYS_INPUT (sys:system) (id:ident) : input =
   let ants = SYS_ANTS sys in
   let sti = SYS_STIGMERGY sys in
   let pos = ANT_POSITION ants id in
   let dir = ANT_STATUS ants id in
   let nbh = GET_PERCEPTION sti pos in
   let inp = dir,nbh in
   inp`;;

let ANT_STEP = new_definition
  `ANT_STEP (sys:system) (id:ident) : status#position->bool =
   let ants = SYS_ANTS sys in
   AGENT_STEP (ANT_AGENT ants id) (SYS_INPUT sys id)`;;

type_of `DICT_COLLECT (FUNDICT (KEYS (SYS_ANTS sys)) (ANT_STEP sys))`;;

let UPDATE_ANTS = new_definition
  `UPDATE_ANTS sys =
   DICT_COLLECT (FUNDICT (KEYS (SYS_ANTS sys)) (ANT_STEP sys))`;;


let UPDATE_SYSTEM = new_definition
  `UPDATE_SYSTEM (sys:system) =
   System(UPDATE_STIGMERGY sys,
          FUNDICT (KEYS (SYS_ANTS sys))
                  (COLLECT (ANT_STEP sys)))`;;