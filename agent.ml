(* ========================================================================= *)
(* Nondeterministic agents in HOL.                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Miscellanea.                                                              *)
(* ------------------------------------------------------------------------- *)

needs "Library/iter.ml";;
needs "code/HOL-Ants/setbind.ml";;
needs "code/HOL-Ants/dict.ml";;
needs "code/HOL-Ants/conv.ml";;
needs "code/HOL-Ants/comp.ml";;

let nmax = new_definition
  `nmax (s:A->bool) (f:A->num) =
   @m. (!x. x IN s ==> f x <= m) /\ (?x. x IN s /\ f x = m)`;;

let ITERSETBIND = new_definition
  `ITERSETBIND (f:A->A->bool) (n:num) : (A->bool) -> (A->bool) =
   ITER n (SETBIND f)`;;

let COLLECT = new_definition
  `COLLECT (u:A->B->bool) : (A->B)->bool = {f : A -> B | !x. f x IN u x}`;;

let COLLECT_CONST = prove
 (`!s:B->bool. COLLECT (\x:A. s) = {f | !x. f x IN s}`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; COLLECT]);;

let COLLECT_o = prove
 (`!f:C->A u:A->B->bool.
     (!x y. f x = f y ==> x = y) /\
     (!y. ?x. f x = y)
     ==> COLLECT (u o f) = IMAGE (\g. g o f) (COLLECT u)`,
  INTRO_TAC "!f u; inj surj" THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; COLLECT; FORALL_IN_GSPEC; FORALL_IN_IMAGE; o_THM] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; o_THM] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![g]; g" THEN
   EXISTS_TAC `g:C->B o inverse (f:C->A)` THEN
   REWRITE_TAC[GSYM o_ASSOC; o_THM] THEN
   HYP_TAC "inj" (REWRITE_RULE[INJECTIVE_INVERSE_o]) THEN
   ASM_REWRITE_TAC[I_O_ID] THEN
   GEN_TAC THEN
   CLAIM_TAC "+" `u (x:A):B->bool = u (f (inverse f (x:A):C))` THENL
   [AP_TERM_TAC THEN
   HYP_TAC "surj" (REWRITE_RULE[SURJECTIVE_INVERSE]) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "![g]; g; !x" THEN ASM_REWRITE_TAC[]);;

let COLLECT_o_ALT = prove
 (`!f:C->A u:A->B->bool.
     (!x y. f x = f y ==> x = y) /\
     (!y. ?x. f x = y)
     ==> COLLECT u = IMAGE (\g. g o inverse f) (COLLECT (u o f))`,
  INTRO_TAC "!f u; inj surj" THEN
  SUBGOAL_THEN `u:A->B->bool = (u o f:C->A) o inverse f`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
  [HYP_TAC "surj" (REWRITE_RULE[SURJECTIVE_INVERSE_o]) THEN
   ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID];
   ALL_TAC] THEN
  MP_TAC (ISPECL [`inverse (f:C->A)`; `u:A->B->bool o f:C->A`] COLLECT_o) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    POP_ASSUM (MP_TAC o AP_TERM `f:C->A`) THEN
    HYP_TAC "surj" (REWRITE_RULE[SURJECTIVE_INVERSE]) THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN EXISTS_TAC `f (y:C):A` THEN
    HYP_TAC "inj" (REWRITE_RULE[INJECTIVE_INVERSE]) THEN
    ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let COLLECT_o_ALT2 = prove
 (`!f:A->C u:A->B->bool.
     (!x y. f x = f y ==> x = y) /\
     (!y. ?x. f x = y)
     ==> COLLECT u = IMAGE (\g. g o f) (COLLECT (u o inverse f))`,
  CHEAT_TAC);;
  (* INTRO_TAC "!f u; inj surj" THEN
  SUBGOAL_THEN `u:A->B->bool = (u o f:C->A) o inverse f`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
  [HYP_TAC "surj" (REWRITE_RULE[SURJECTIVE_INVERSE_o]) THEN
   ASM_REWRITE_TAC[GSYM o_ASSOC; I_O_ID];
   ALL_TAC] THEN
  MP_TAC (ISPECL [`inverse (f:C->A)`; `u:A->B->bool o f:C->A`] COLLECT_o) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    POP_ASSUM (MP_TAC o AP_TERM `f:C->A`) THEN
    HYP_TAC "surj" (REWRITE_RULE[SURJECTIVE_INVERSE]) THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN EXISTS_TAC `f (y:C):A` THEN
    HYP_TAC "inj" (REWRITE_RULE[INJECTIVE_INVERSE]) THEN
    ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);; *)

let COLLECT_EQ_SETBIND = prove
 (`!u:num->A->bool.
     COLLECT u =
     SETBIND (\x:A. IMAGE (\f:num->A n. if n = 0 then x else f (PRE n))
                          (COLLECT (u o SUC)))
         (u 0)`,
  GEN_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_SETBIND;
              COLLECT; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_SETBIND; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              FORALL_IN_IMAGE; FORALL_IN_GSPEC; o_THM] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  CONJ_TAC THENL
  [INTRO_TAC "!f; f" THEN
   EXISTS_TAC `f 0:A` THEN
   ASM_REWRITE_TAC[FUN_EQ_THM] THEN
   EXISTS_TAC `f:num->A o SUC` THEN
   ASM_REWRITE_TAC[o_THM] THEN
   INTRO_TAC "![n]" THEN
   COND_CASES_TAC THENL [ASM_MESON_TAC[]; AP_TERM_TAC THEN ASM_ARITH_TAC];
   ALL_TAC] THEN
  INTRO_TAC "!x; x; !f; f; ![n]" THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN ASM_REWRITE_TAC[PRE]);;

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

let input_INDUCT,input_RECUR = define_type
  "input = Input(A#B)";;

let INPUT_STATUS = define
  `INPUT_STATUS (Input(stat:Stat,percpt:Percpt)) = stat`;;

let INPUT_PERCEPTION = define
  `INPUT_PERCEPTION (Input(stat:Stat,percpt:Percpt)) = percpt`;;

let agent_INDUCT,agent_RECUR = define_type
  "agent = Agent((A,B)input->A#C->bool)";;

let AGENT_STEP = define
  `AGENT_STEP (Agent(a:(Stat,Percpt)input->Stat#Action->bool)) = a`;;

(* ------------------------------------------------------------------------- *)
(* System.                                                                   *)
(* ------------------------------------------------------------------------- *)

(*
A = Environment (stigmergy) of the whole system
B = Ident (nomi agenti)
C = Agent attribute (position)

D = Agent internal status
E = Agent perception
F = Agent action
*)

let system_INDUCT,system_RECUR = define_type
  "system = System(A#
                   (B->C#D#(D,E,F)agent))";;

let SYSTEM_ENVIRONMENT = define
  `SYSTEM_ENVIRONMENT
    (System(env,agents):(Env,Id,Attr,Stat,Percpt,Action)system) =
    env`;;

let SYSTEM_AGENTS = define
  `SYSTEM_AGENTS
    (System(env,agents):(Env,Id,Attr,Stat,Percpt,Action)system) =
    agents`;;

let UPDATE_SYSTEM = new_definition
  `UPDATE_SYSTEM
     (update_environment :
       (Env,Id,Attr,Stat,Percpt,Action)system -> Env)
     (update_agents :
       (Env,Id,Attr,Stat,Percpt,Action)system ->
       (Id -> Attr#Stat#(Stat,Percpt,Action)agent) -> bool)
     (sys : (Env,Id,Attr,Stat,Percpt,Action)system) :
     (Env,Id,Attr,Stat,Percpt,Action)system -> bool =
    IMAGE (\a. System(update_environment sys,a))
          (update_agents sys)`;;

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

let POSITION_NUM = define
  `POSITION_NUM (Position i) = i`;;

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

let perception_INDUCT,perception_RECUR = define_type
  "perception = Perception(location #
                           (position->bool) #
                           (position->num) #
                           (position->direction))";;

let PERCEPTION_LOCATION = define
  `PERCEPTION_LOCATION (Perception(loc,nbh,sti,dirs)) = loc`;;

let PERCEPTION_NEIGHBORHOOD = define
  `PERCEPTION_NEIGHBORHOOD (Perception(loc,nbh,sti,dirs)) = nbh`;;

let PERCEPTION_STIGMERGY = define
  `PERCEPTION_STIGMERGY (Perception(loc,nbh,sti,dirs)) = sti`;;

let PERCEPTION_DIRECTIONS = define
  `PERCEPTION_DIRECTIONS (Perception(loc,nbh,sti,dirs)) = dirs`;;

new_type_abbrev("status",`:direction`);;

let ACCESSIBLE_POSITIONS = new_definition
  `ACCESSIBLE_POSITIONS (inp:(status,perception)input) : position->bool =
   let percpt = INPUT_PERCEPTION inp in
   let dir = INPUT_STATUS inp in
   let nbh = PERCEPTION_NEIGHBORHOOD percpt in
   {pos | pos IN nbh /\ PERCEPTION_DIRECTIONS percpt pos = dir}`;;

let UPDATE_POSITION = new_definition
  `UPDATE_POSITION (inp:(status,perception)input) : position->bool =
   let percpt = INPUT_PERCEPTION inp in
   let dir = INPUT_STATUS inp in
   CHOOSE_POSITION (PERCEPTION_STIGMERGY percpt) (ACCESSIBLE_POSITIONS inp)`;;

new_type_abbrev("ant",`:(status,perception,position)agent`);;

let ANT = new_definition
  `ANT : ant =
   Agent(\inp:(status,perception)input.
           let dir = INPUT_STATUS inp in
           let percpt = INPUT_PERCEPTION inp in
           let loc = PERCEPTION_LOCATION percpt in
           let newdir:status = UPADATE_DIRECTION loc dir in
           {newdir,pos | pos | pos IN UPDATE_POSITION inp})`;;

(* ------------------------------------------------------------------------- *)
(* System for ants.                                                          *)
(* ------------------------------------------------------------------------- *)

let ident_INDUCT,ident_RECUR = define_type
  "ident = Ident num";;

new_type_abbrev("antsys",
  `:(position->num,ident,position,direction,perception,position)system`);;

  (** Commento 1: Che cosa succede secondo ANT_UPDATE_ENVIRONMENT quando ci sono
    formiche "tonte" in una posizione (ad es, nel nido)? Siamo sicuri che stiamo
    descrivendo il giusto aggiornamento in combinazione con CHOOSE_POSITION??
    Si potrebbe fare un hack mettendo tutte le "tonte" in un punto morto, però
    così si rompe il modello. Bisogna pensarci
  **)

let ANT_UPDATE_ENVIRONMENT = new_definition
  `ANT_UPDATE_ENVIRONMENT (sys:antsys) (pos:position) : num =
   SYSTEM_ENVIRONMENT sys pos + CARD {id | FST (SYSTEM_AGENTS sys id) = pos}`;;

let perception_INDUCT,perception_RECUR = define_type
  "perception = Perception(location #
                           (position->bool) #
                           (position->num) #
                           (position->direction))";;

let MK_PERCEPTION = new_definition
  `MK_PERCEPTION (sti:position->num) (pos:position) : perception =
   let loc:location = LOCATION pos in
   let Position i = pos in
   let positions = {Position j | i,j IN MOVES} in
   let dirs = \pos. if i,POSITION_NUM pos IN FORWARD_MOVES
                    then Forward
                    else Backward in
   Perception(loc,positions,sti,dirs)`;;
   (* Perception(loc,positions,RESTRICTION positions sti,dirs)`;; 
      Distinzione tra global stigmergy e local stigmergy          *)

let MK_INPUT = new_definition
  `MK_INPUT (sys:antsys) (id:ident) : (direction,perception)input =
   let ag = SYSTEM_AGENTS sys id in
   let dir = FST(SND ag) in
   let percpt = MK_PERCEPTION (SYSTEM_ENVIRONMENT sys)
                              (FST ag) in
   Input(dir,percpt)`;;

let ANT_UPDATE_AGENTS = new_definition
  `ANT_UPDATE_AGENTS (sys:antsys) :
     (ident -> position#direction#(direction,perception,position)agent) -> bool =
   COLLECT
     (\id. let pos,dir,log = SYSTEM_AGENTS sys id in
           let inp = MK_INPUT sys id in
           IMAGE (\(dir,pos). pos,dir,log) (AGENT_STEP log inp))`;;

let ANT_UPDATE_SYSTEM = new_definition
  `ANT_UPDATE_SYSTEM : antsys->antsys->bool =
   UPDATE_SYSTEM ANT_UPDATE_ENVIRONMENT ANT_UPDATE_AGENTS`;;

let DUMBANT = new_definition
  `DUMBANT : ant =
   Agent(\inp:(direction,perception)input. {(INPUT_STATUS inp,Position 0)})`;;


(*
(REWRITE_CONV[ANT_UPDATE_SYSTEM; UPDATE_SYSTEM; ANT_UPDATE_ENVIRONMENT; ANT_UPDATE_SYSTEM] THENC
TOP_DEPTH_CONV let_CONV THENC
REWRITE_CONV[ANT_UPDATE_SYSTEM; UPDATE_SYSTEM; ANT_UPDATE_ENVIRONMENT; ANT_UPDATE_SYSTEM; ANT_UPDATE_AGENTS; MK_INPUT; MK_PERCEPTION] THENC
TOP_DEPTH_CONV let_CONV THENC
REWRITE_CONV[SYSTEM_ENVIRONMENT; SYSTEM_AGENTS; FORWARD_MOVES] THENC
TOP_DEPTH_CONV let_CONV THENC
ALL_CONV)
`ANT_UPDATE_SYSTEM
(let sti = (\pos. 0) in
 let ants = (\id. match id with
                 | Ident 0 -> Position 1,Forward,ANT
                 | Ident 1 -> Position 2,Forward,ANT
                 | Ident 2 -> Position 3,Backward,ANT
                 | Ident _ -> Position 0,Forward,DUMBANT) in
 System(sti,ants):antsys)`;;
*)

COMPUTE_CONV [ANT_UPDATE_SYSTEM; UPDATE_SYSTEM; ANT_UPDATE_AGENTS; MK_INPUT; AGENT_STEP]
`ANT_UPDATE_SYSTEM
(let sti = (\pos. 0) in
 let ants = (\id. match id with
                 | Ident 0 -> Position 1,Forward,ANT
                 | Ident 1 -> Position 2,Forward,ANT
                 | Ident 2 -> Position 3,Backward,ANT
                 | Ident _ -> Position 0,Forward,DUMBANT) in
 System(sti,ants):antsys)`;;
let th = it;;
let tm = rhs (concl th);;
rand tm;;


(* `SETBIND (\f:num->A. IMAGE (\x:A. \n:num. if n = 0 then x else f (PRE n)) (u 0))
         (COLLECT (u o SUC))`;; *)

let POSITION_SURJ = prove
 (`!y. ?x. Position x = y`,
  MESON_TAC[cases "position"]);;

let IDENT_SURJ = prove
 (`!y. ?x. Ident x = y`,
  MESON_TAC[cases "ident"]);;

let COLLECT_IDENT_REINDEX =
  REWRITE_RULE[injectivity "ident"; IDENT_SURJ] (ISPEC `Ident` COLLECT_o_ALT);;

(
COMPUTE_CONV [ANT_UPDATE_SYSTEM; UPDATE_SYSTEM;
              ANT_UPDATE_AGENTS; MK_INPUT; AGENT_STEP] THENC
ONCE_REWRITE_CONV[COLLECT_IDENT_REINDEX] THENC
ONCE_REWRITE_CONV[COLLECT_EQ_SETBIND] THENC
REWRITE_CONV[o_THM; MK_INPUT]
)
`ANT_UPDATE_SYSTEM
(let sti = (\pos. 0) in
 let ants = (\id. match id with
                 | Ident 0 -> Position 1,Forward,ANT
                 | Ident 1 -> Position 2,Forward,ANT
                 | Ident 2 -> Position 3,Backward,ANT
                 | Ident _ -> Position 0,Forward,DUMBANT) in
 System(sti,ants):antsys)`;;

(* let th = it;;
let tm = rhs (concl th);;
rand tm;;
dest_const(rator(rand tm));; *)

