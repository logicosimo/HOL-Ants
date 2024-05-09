(* ========================================================================= *)
(* Systems of agents.                                                        *)
(* ========================================================================= *)

(*
System(env,agents)
env:num->num (position->stigmergy)
agents: num#
        direction#
        (direction,num->num,num)agent)dict

A = num->num option - Environment (stigmergy) of the whole system
B = num - Ident (nomi agenti)
C = num - Agent attribute (position)

D = direction - Agent internal status
E = rimosso - Agent perception
F = (num#direction) - njuova posizione,nuova direzione - Agent action
*)

let system_INDUCT,system_RECUR = define_type
  "system = System((num->num)#
                   (num,
                    num#
                    direction#
                    (direction,perception,num)agent)dict)";;

let SYSTEM_ENVIRONMENT = define
  `SYSTEM_ENVIRONMENT (System(env,agents)) = env`;;

let SYSTEM_AGENTS = define
  `SYSTEM_AGENTS (System(env,agents)) = agents`;;

add_ants_thl[injectivity "system"; SYSTEM_ENVIRONMENT; SYSTEM_AGENTS];;

let UPDATE_SYSTEM = new_definition
  `UPDATE_SYSTEM
     (update_environment : system -> (num->num))
     (update_agents : system -> (num,num#direction#(direction,perception,num)agent)dict -> bool)
     (sys : system) : system -> bool =
    IMAGE (\a. System(update_environment sys,a)) (update_agents sys)`;;

add_ants_thl[UPDATE_SYSTEM];;

(* ------------------------------------------------------------------------- *)
(* System for ants.                                                          *)
(* ------------------------------------------------------------------------- *)

let ANT_UPDATE_ENVIRONMENT = new_definition
  `ANT_UPDATE_ENVIRONMENT (sys:system) (pos:num) : num =
   SYSTEM_ENVIRONMENT sys pos +
   CARD {id | id IN KEYS (SYSTEM_AGENTS sys) /\
              FST (GET (SYSTEM_AGENTS sys) id) = pos}`;;

let ANT_UPDATE_ENVIRONMENT_THM = prove
 (`ANT_UPDATE_ENVIRONMENT (sys:system) (pos:num) : num =
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

(*
let NUMFUN = new_defintion
  `NUMFUN l i = if i < LENGTH l then EL i l else 0`;;

NUMFUN [] i = 0
NUMFUN (CONS h t) 0 = h
NUMFUN (CONS h t) 0 = h
NUMFUN [3;4;2;3;5] n
*)


(* let ANT_UPDATE_ENVIRONMENT_THM2 = prove
 (`ANT_UPDATE_ENVIRONMENT (sys:system) = \pos.
   SYSTEM_ENVIRONMENT sys pos +
   if FINITE (KEYS (SYSTEM_AGENTS sys))
   then GETOPTION (COUNT (SOME 0)
                          (KEYS (SYSTEM_AGENTS sys))
                          (\id. FST (GET (SYSTEM_AGENTS sys) id) = pos))
   else CARD {id | id IN KEYS (SYSTEM_AGENTS sys) /\
                   FST (GET (SYSTEM_AGENTS sys) id) = pos}`,
  REWRITE_TAC[FUN_EQ_THM; ANT_UPDATE_ENVIRONMENT_THM]);;

add_ants_thl[ANT_UPDATE_ENVIRONMENT_THM2];; *)

let MK_INPUT = new_definition
  `MK_INPUT (sys:system) (id:num) : (direction,perception)input =
   let ag = GET (SYSTEM_AGENTS sys) id in
   let dir = FST(SND ag) in
   let percpt = MK_PERCEPTION (\pos. SYSTEM_ENVIRONMENT sys pos)
                              (FST ag) in
   Input(dir,percpt)`;;

add_ants_thl[MK_INPUT];;

let ANT_UPDATE_AGENTS = new_definition
  `ANT_UPDATE_AGENTS (sys:system) :
     (num,num#direction#(direction,perception,num)agent)dict ->
     bool =
   DICT_COLLECT
     (FUNDICT (KEYS (SYSTEM_AGENTS sys))
       (\id. let pos,dir,log = GET (SYSTEM_AGENTS sys) id in
             let inp = MK_INPUT sys id in
             IMAGE (\(dir,pos). pos,dir,log) (AGENT_STEP log inp)))`;;

let ANT_UPDATE_SYSTEM = new_definition
  `ANT_UPDATE_SYSTEM : system->system->bool =
   UPDATE_SYSTEM ANT_UPDATE_ENVIRONMENT ANT_UPDATE_AGENTS`;;

add_ants_thl[ANT_UPDATE_AGENTS; ANT_UPDATE_SYSTEM];;
