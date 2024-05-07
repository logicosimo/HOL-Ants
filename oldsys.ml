
(*
A = Environment (stigmergy) of the whole system
B = Ident (nomi agenti)
C = Agent attribute (position)

D = Agent internal status
E = Agent perception
F = Agent action
*)


(* let system_tybij =
 (new_type_definition "system" ("System","Dest_System") o prove)
 (`?sys:(A#(B,C#D#(D,E,F)agent)dict). FINITE (KEYS (SND sys))`,
  REWRITE_TAC[EXISTS_PAIR_THM] THEN
  EXISTS_TAC `EMPTYDICT:(B,C#D#(D,E,F)agent)dict` THEN
  REWRITE_TAC[KEYS_EMPTYDICT; FINITE_EMPTY]);;

let SYSTEM_ENVIRONMENT_DEF = define
  `SYSTEM_ENVIRONMENT (sys:(Env,Id,Attr,Stat,Percpt,Action)system) : Env =
   FST (Dest_System sys)`;;

let SYSTEM_AGENTS_DEF = define
  `SYSTEM_AGENTS (sys:(Env,Id,Attr,Stat,Percpt,Action)system) :
     (Id,Attr#Stat#(Stat,Percpt,Action)agent)dict =
   SND (Dest_System sys)`;;

let FINITE_SYSTEM_AGENTS = prove
 (`!sys:(Env,Id,Attr,Stat,Percpt,Action)system.
     FINITE (KEYS (SYSTEM_AGENTS sys))`,
  REWRITE_TAC[SYSTEM_AGENTS_DEF; system_tybij]);;

let FST_SND_EQ = prove
 (`!p x:A y:B. FST p = x /\ SND p = y <=> p = x,y`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

let SYSTEM_PROJECTIONS = prove
 (`!env:Env agents:(Id,Attr#Stat#(Stat,Percpt,Action)agent)dict.
     FINITE (KEYS agents)
     ==> SYSTEM_ENVIRONMENT (System (env,agents)) = env /\
         SYSTEM_AGENTS (System (env,agents)) = agents`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SYSTEM_ENVIRONMENT_DEF; SYSTEM_AGENTS_DEF; FST_SND_EQ] THEN
  ASM_REWRITE_TAC[GSYM system_tybij]);; *)



(* ------------------------------------------------------------------------- *)


(*
A = num->num option - Environment (stigmergy) of the whole system
B = num - Ident (nomi agenti)
C = num - Agent attribute (position)

D = direction - Agent internal status
E = rimosso - Agent perception
F = (num#direction) - njuova posizione,nuova direzione - Agent action
*)

let system_INDUCT,system_RECUR = define_type
  "system = System((num->num option)#
                   (num,num#direction#(D,E,F)agent)dict)";;

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
       (Id,Attr#Stat#(Stat,Percpt,Action)agent)dict -> bool)
     (sys : (Env,Id,Attr,Stat,Percpt,Action)system) :
     (Env,Id,Attr,Stat,Percpt,Action)system -> bool =
    IMAGE (\a. System(update_environment sys,a))
          (update_agents sys)`;;

add_ants_thl[UPDATE_SYSTEM];;

(* ------------------------------------------------------------------------- *)
(* Ants.                                                                     *)
(* ------------------------------------------------------------------------- *)

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
   SYSTEM_ENVIRONMENT sys pos +
   CARD {id | id IN KEYS (SYSTEM_AGENTS sys) /\
              FST (GET (SYSTEM_AGENTS sys) id) = pos}`;;

let ANT_UPDATE_ENVIRONMENT_THM = prove
 (`ANT_UPDATE_ENVIRONMENT (sys:antsys) (pos:position) : num =
   SYSTEM_ENVIRONMENT sys pos +
   if FINITE (KEYS (SYSTEM_AGENTS sys))
   then GETOPTION (COUNT (SOME 0)
                          (KEYS (SYSTEM_AGENTS sys))
                          (\id. FST (GET (SYSTEM_AGENTS sys) id) = pos))
   else CARD {id | id IN KEYS (SYSTEM_AGENTS sys) /\
                   FST (GET (SYSTEM_AGENTS sys) id) = pos}`,
  REWRITE_TAC[ANT_UPDATE_ENVIRONMENT] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CARD_EQ_COUNT]);;

add_ants_thl[ANT_UPDATE_ENVIRONMENT_THM];;

let ANT_UPDATE_ENVIRONMENT_THM2 = prove
 (`ANT_UPDATE_ENVIRONMENT (sys:antsys) = \pos.
   SYSTEM_ENVIRONMENT sys pos +
   if FINITE (KEYS (SYSTEM_AGENTS sys))
   then GETOPTION (COUNT (SOME 0)
                          (KEYS (SYSTEM_AGENTS sys))
                          (\id. FST (GET (SYSTEM_AGENTS sys) id) = pos))
   else CARD {id | id IN KEYS (SYSTEM_AGENTS sys) /\
                   FST (GET (SYSTEM_AGENTS sys) id) = pos}`,
  REWRITE_TAC[FUN_EQ_THM; ANT_UPDATE_ENVIRONMENT_THM]);;

add_ants_thl[ANT_UPDATE_ENVIRONMENT_THM2];;

let MK_INPUT = new_definition
  `MK_INPUT (sys:antsys) (id:ident) : (direction,perception)input =
   let ag = GET (SYSTEM_AGENTS sys) id in
   let dir = FST(SND ag) in
   let percpt = MK_PERCEPTION (SYSTEM_ENVIRONMENT sys)
                              (FST ag) in
   Input(dir,percpt)`;;

add_ants_thl[MK_INPUT];;

let ANT_UPDATE_AGENTS = new_definition
  `ANT_UPDATE_AGENTS (sys:antsys) :
     (ident,position#direction#(direction,perception,position)agent)dict ->
     bool =
   DICT_COLLECT
     (FUNDICT (KEYS (SYSTEM_AGENTS sys))
       (\id. let pos,dir,log = GET (SYSTEM_AGENTS sys) id in
             let inp = MK_INPUT sys id in
             IMAGE (\(dir,pos). pos,dir,log) (AGENT_STEP log inp)))`;;

let IDENT_SURJ = prove
 (`!y. ?x. Ident x = y`,
  MESON_TAC[cases "ident"]);;

(* let COLLECT_IDENT_REINDEX =
  REWRITE_RULE[injectivity "ident"; IDENT_SURJ]
    (ISPEC `Ident` COLLECT_o_ALT);; *)

(* ONCE_REWRITE_RULE[COLLECT_EQ_SETBIND]
  (ONCE_REWRITE_RULE[COLLECT_IDENT_REINDEX] ANT_UPDATE_AGENTS);; *)

let ANT_UPDATE_SYSTEM = new_definition
  `ANT_UPDATE_SYSTEM : antsys->antsys->bool =
   UPDATE_SYSTEM ANT_UPDATE_ENVIRONMENT ANT_UPDATE_AGENTS`;;

add_ants_thl[ANT_UPDATE_AGENTS; ANT_UPDATE_SYSTEM];;
(* add_ants_thl[ANT_UPDATE_AGENTS_ALT; ANT_UPDATE_SYSTEM];; *)

(* let DUMBANT = new_definition
  `DUMBANT : ant =
   Agent(\inp:(direction,perception)input. {(INPUT_STATUS inp,Position 0)})`;;

add_ants_thl[DUMBANT];; *)

(* let POSITION_SURJ = prove
 (`!y. ?x. Position x = y`,
  MESON_TAC[cases "position"]);;
*)