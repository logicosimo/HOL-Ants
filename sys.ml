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
  "system = System((num#num#num)#
                   (num,
                    num#
                    direction#
                    (direction,num#(num#num#num),num)agent)dict)";;

let SYSTEM_ENVIRONMENT = define
  `SYSTEM_ENVIRONMENT (System(env,agents)) = env`;;

let SYSTEM_AGENTS = define
  `SYSTEM_AGENTS (System(env,agents)) = agents`;;

add_ants_thl[injectivity "system"; SYSTEM_ENVIRONMENT; SYSTEM_AGENTS];;

let UPDATE_SYSTEM = new_definition
  `UPDATE_SYSTEM
     (update_environment : system -> (num#num#num))
     (update_agents : system -> (num,num#direction#(direction,num#(num#num#num),num)agent)dict -> bool)
     (sys : system) : system -> bool =
    IMAGE (\a. System(update_environment sys,a)) (update_agents sys)`;;

add_ants_thl[UPDATE_SYSTEM];;

(* ------------------------------------------------------------------------- *)
(* System for ants.                                                          *)
(* ------------------------------------------------------------------------- *)

let ANT_UPDATE_ENVIRONMENT = new_definition
  `ANT_UPDATE_ENVIRONMENT (sys:system) : (num#num#num) =
   let s1,s2,s3 = SYSTEM_ENVIRONMENT sys in
   let t1 = s1 + CARD {id | id IN KEYS (SYSTEM_AGENTS sys) /\
                            FST (GET (SYSTEM_AGENTS sys) id) = 1} in
   let t2 = s2 + CARD {id | id IN KEYS (SYSTEM_AGENTS sys) /\
                            FST (GET (SYSTEM_AGENTS sys) id) = 2} in
   let t3 = s3 + CARD {id | id IN KEYS (SYSTEM_AGENTS sys) /\
                            FST (GET (SYSTEM_AGENTS sys) id) = 3} in
   (t1,t2,t3)`;;

let ANT_UPDATE_ENVIRONMENT_THM = prove
 (`ANT_UPDATE_ENVIRONMENT (sys:system) : (num#num#num) =
   let s1,s2,s3 = SYSTEM_ENVIRONMENT sys in
   let t1 = s1 +
     if FINITE (KEYS (SYSTEM_AGENTS sys)) then
       GETOPTION (COUNT (SOME 0)
                          (KEYS (SYSTEM_AGENTS sys))
                          (\id. FST (GET (SYSTEM_AGENTS sys) id) = 1))
     else
       CARD {id | id IN KEYS (SYSTEM_AGENTS sys) /\
                  FST (GET (SYSTEM_AGENTS sys) id) = 1} in
   let t2 = s2 +
     if FINITE (KEYS (SYSTEM_AGENTS sys)) then
       GETOPTION (COUNT (SOME 0)
                          (KEYS (SYSTEM_AGENTS sys))
                          (\id. FST (GET (SYSTEM_AGENTS sys) id) = 2))
     else
       CARD {id | id IN KEYS (SYSTEM_AGENTS sys) /\
                  FST (GET (SYSTEM_AGENTS sys) id) = 2} in
   let t3 = s3 +
     if FINITE (KEYS (SYSTEM_AGENTS sys)) then
       GETOPTION (COUNT (SOME 0)
                          (KEYS (SYSTEM_AGENTS sys))
                          (\id. FST (GET (SYSTEM_AGENTS sys) id) = 3))
     else
       CARD {id | id IN KEYS (SYSTEM_AGENTS sys) /\
                  FST (GET (SYSTEM_AGENTS sys) id) = 3} in
   (t1,t2,t3)`,
  REWRITE_TAC[ANT_UPDATE_ENVIRONMENT] THEN
  CONV_TAC (TOP_SWEEP_CONV let_CONV) THEN
  REWRITE_TAC[PAIR_EQ] THEN REPEAT CONJ_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[CARD_EQ_COUNT]);;

add_ants_thl[ANT_UPDATE_ENVIRONMENT_THM];;

(* let MK_INPUT = new_definition
  `MK_INPUT (sys:system) (id:num) : (direction,perception)input =
   let ag = GET (SYSTEM_AGENTS sys) id in
   let dir = FST(SND ag) in
   let percpt = MK_PERCEPTION (\pos. SYSTEM_ENVIRONMENT sys pos)
                              (FST ag) in
   Input(dir,percpt)`;;

add_ants_thl[MK_INPUT];; *)

(* let ANT_UPDATE_AGENTS = new_definition
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
   UPDATE_SYSTEM ANT_UPDATE_ENVIRONMENT ANT_UPDATE_AGENTS`;; *)


let ANT_UPDATE_AGENTS = new_definition
  `ANT_UPDATE_AGENTS (sys:system) : (num,num#direction#ant)dict -> bool =
   DICT_COLLECT
     (FUNDICT (KEYS (SYSTEM_AGENTS sys))
       (\id. let pos,dir,log = GET (SYSTEM_AGENTS sys) id in
             let inp:(direction,num#(num#num#num))input = Input(dir,(pos,SYSTEM_ENVIRONMENT sys)) in
             IMAGE (\(dir,pos). pos,dir,log) (AGENT_STEP log inp)))`;;

let ANT_UPDATE_SYSTEM = new_definition
  `ANT_UPDATE_SYSTEM : system->system->bool =
   UPDATE_SYSTEM ANT_UPDATE_ENVIRONMENT ANT_UPDATE_AGENTS`;;

add_ants_thl[ANT_UPDATE_AGENTS; ANT_UPDATE_SYSTEM];;
