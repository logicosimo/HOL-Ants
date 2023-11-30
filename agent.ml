(* ========================================================================= *)
(* Nondeterministic agents in HOL.                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Miscellanea.                                                              *)
(* ------------------------------------------------------------------------- *)

let get_ants_thl,add_ants_thl =
  let thl:thm list ref = ref [] in
  let get_ants_thl() = !thl
  and add_ants_thl l = thl := l @ !thl in
  get_ants_thl,add_ants_thl;;

let SETALL = new_definition
  `SETALL P s <=> (!x:A. x IN s ==> P x)`;;

let SETALL_CLAUSES = prove
 (`(!P:A->bool. SETALL P {}) /\
   (!P x:A s. SETALL P (x INSERT s) <=> P x /\ SETALL P s)`,
  REWRITE_TAC[SETALL] THEN SET_TAC[]);;

add_ants_thl [SETALL_CLAUSES];;

let SETFILTER = new_definition
  `SETFILTER (P:A->bool) s = {x | x IN s /\ P x}`;;

let SETFILTER_CLAUSES = prove
 (`(!P. SETFILTER P {} = {}) /\
   (!P x:A s. SETFILTER P (x INSERT s) =
              if P x then x INSERT SETFILTER P s else SETFILTER P s)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; NOT_IN_EMPTY;
           SETFILTER; FORALL_IN_GSPEC; FORALL_IN_INSERT; IMP_CONJ] THENL
  [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
   REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

add_ants_thl [SETFILTER_CLAUSES];;

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

add_ants_thl [COLLECT_EQ_SETBIND];;

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

add_ants_thl[injectivity "system"; SYSTEM_ENVIRONMENT; SYSTEM_AGENTS];;

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

add_ants_thl[UPDATE_SYSTEM];;

(* ------------------------------------------------------------------------- *)
(* Ants.                                                                     *)
(* ------------------------------------------------------------------------- *)

(* let CHOOSE_POSITION = new_definition
  `CHOOSE_POSITION (sti:Pos->num) (positions:Pos->bool) : Pos->bool =
   {pos | pos IN positions /\ sti pos = nmax positions sti}`;; *)

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

let position_INDUCT,position_RECUR = define_type
  "position = Position num";;

let POSITION_NUM = define
  `POSITION_NUM (Position i) = i`;;

add_ants_thl[injectivity "position"; POSITION_NUM];;

let LOCATION = new_definition
  `LOCATION (pos:position) : location = match pos with
                                        | Position 0 -> Nest
                                        | Position 4 -> Dest
                                        | Position _ -> Path`;;

add_ants_thl[LOCATION];;

let UPADATE_DIRECTION = new_definition
  `UPADATE_DIRECTION loc dir = match loc with
                             | Nest -> Forward
                             | Dest -> Backward
                             | Path -> dir`;;

add_ants_thl[UPADATE_DIRECTION];;

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

add_ants_thl[injectivity "perception"; PERCEPTION_LOCATION;
  PERCEPTION_NEIGHBORHOOD; PERCEPTION_STIGMERGY; PERCEPTION_DIRECTIONS];;

new_type_abbrev("status",`:direction`);;

let ACCESSIBLE_POSITIONS = new_definition
  `ACCESSIBLE_POSITIONS (inp:(status,perception)input) : position->bool =
   let percpt = INPUT_PERCEPTION inp in
   let dir = INPUT_STATUS inp in
   let nbh = PERCEPTION_NEIGHBORHOOD percpt in
   {pos | pos IN nbh /\ PERCEPTION_DIRECTIONS percpt pos = dir}`;;

let ACCESSIBLE_POSITIONS_THM = prove
 (`ACCESSIBLE_POSITIONS (inp:(status,perception)input) : position->bool =
   let percpt = INPUT_PERCEPTION inp in
   let dir = INPUT_STATUS inp in
   let nbh = PERCEPTION_NEIGHBORHOOD percpt in
   SETFILTER (\pos. PERCEPTION_DIRECTIONS percpt pos = dir) nbh`,
  REWRITE_TAC[ACCESSIBLE_POSITIONS; SETFILTER]);;

add_ants_thl[ACCESSIBLE_POSITIONS_THM];;

let UPDATE_POSITION = new_definition
  `UPDATE_POSITION (inp:(status,perception)input) : position->bool =
   let percpt = INPUT_PERCEPTION inp in
   let dir = INPUT_STATUS inp in
   CHOOSE_POSITION (PERCEPTION_STIGMERGY percpt) (ACCESSIBLE_POSITIONS inp)`;;

add_ants_thl[UPDATE_POSITION];;

new_type_abbrev("ant",`:(status,perception,position)agent`);;

let ANT = new_definition
  `ANT : ant =
   Agent(\inp:(status,perception)input.
           let dir = INPUT_STATUS inp in
           let percpt = INPUT_PERCEPTION inp in
           let loc = PERCEPTION_LOCATION percpt in
           let newdir:status = UPADATE_DIRECTION loc dir in
           {newdir,pos | pos | pos IN UPDATE_POSITION inp})`;;

g `ANT : ant =
   Agent(\inp:(status,perception)input.
           let dir = INPUT_STATUS inp in
           let percpt = INPUT_PERCEPTION inp in
           let loc = PERCEPTION_LOCATION percpt in
           let newdir:status = UPADATE_DIRECTION loc dir in
           IMAGE (\pos. newdir,pos) (UPDATE_POSITION inp))`;;
e (REWRITE_TAC[ANT; injectivity "agent"]);;
e (ONCE_REWRITE_TAC[FUN_EQ_THM] THEN FIX_TAC "[inp]");;
e (REWRITE_TAC[]);;
e (CONV_TAC (TOP_SWEEP_CONV let_CONV));;
e (SET_TAC[]);;
let ANT_THM = top_thm();;

add_ants_thl[ANT_THM];;

(* ------------------------------------------------------------------------- *)
(* System for ants.                                                          *)
(* ------------------------------------------------------------------------- *)

let ident_INDUCT,ident_RECUR = define_type
  "ident = Ident num";;

add_ants_thl[injectivity "ident"];;

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

let MK_PERCEPTION_THM = prove
 (`MK_PERCEPTION (sti:position->num) (pos:position) : perception =
   let loc:location = LOCATION pos in
   let Position i = pos in
   let positions = IMAGE (\(i,j). Position j) MOVES in
   let dirs = \pos. if i,POSITION_NUM pos IN FORWARD_MOVES
                    then Forward
                    else Backward in
   Perception(loc,positions,sti,dirs)`,
  CHEAT_TAC);;

add_ants_thl[injectivity "perception"; MK_PERCEPTION_THM];;

let MK_INPUT = new_definition
  `MK_INPUT (sys:antsys) (id:ident) : (direction,perception)input =
   let ag = SYSTEM_AGENTS sys id in
   let dir = FST(SND ag) in
   let percpt = MK_PERCEPTION (SYSTEM_ENVIRONMENT sys)
                              (FST ag) in
   Input(dir,percpt)`;;

add_ants_thl[MK_INPUT];;

let ANT_UPDATE_AGENTS = new_definition
  `ANT_UPDATE_AGENTS (sys:antsys) :
     (ident -> position#direction#(direction,perception,position)agent) -> bool =
   COLLECT
     (\id. let pos,dir,log = SYSTEM_AGENTS sys id in
           let inp = MK_INPUT sys id in
           IMAGE (\(dir,pos). pos,dir,log) (AGENT_STEP log inp))`;;

let IDENT_SURJ = prove
 (`!y. ?x. Ident x = y`,
  MESON_TAC[cases "ident"]);;

let COLLECT_IDENT_REINDEX =
  REWRITE_RULE[injectivity "ident"; IDENT_SURJ] (ISPEC `Ident` COLLECT_o_ALT);;

(* ONCE_REWRITE_RULE[COLLECT_EQ_SETBIND]
  (ONCE_REWRITE_RULE[COLLECT_IDENT_REINDEX] ANT_UPDATE_AGENTS);; *)

let ANT_UPDATE_SYSTEM = new_definition
  `ANT_UPDATE_SYSTEM : antsys->antsys->bool =
   UPDATE_SYSTEM ANT_UPDATE_ENVIRONMENT ANT_UPDATE_AGENTS`;;

add_ants_thl[ANT_UPDATE_AGENTS; ANT_UPDATE_SYSTEM];;

let DUMBANT = new_definition
  `DUMBANT : ant =
   Agent(\inp:(direction,perception)input. {(INPUT_STATUS inp,Position 0)})`;;

add_ants_thl[DUMBANT];;

(* let POSITION_SURJ = prove
 (`!y. ?x. Position x = y`,
  MESON_TAC[cases "position"]);;



let BACKWARD_MOVES_THM = prove
 (`BACKWARD_MOVES = {(1,0), (4,1), (2,0), (3,2), (4,3)}`,
  CHEAT_TAC);; *)