(* ========================================================================= *)
(* Dictionaries (partial functions).                                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Options.                                                                  *)
(* ------------------------------------------------------------------------- *)

let GETOPTION = define
  `!x:A. GETOPTION (SOME x) = x`;;

let DEFAULT = define
  `(!a x:A. DEFAULT a (SOME x) = x) /\
   (!a:A. DEFAULT a NONE = a)`;;

let ISSOME_RULES,ISSOME_INDUCT,ISSOME_CASES = new_inductive_definition
  `!a. ISSOME (SOME a)`;;

let ISSOME = prove
 (`(!x:A. ISSOME (SOME x)) /\
   ~ISSOME (NONE:A option)`,
  REWRITE_TAC[ISSOME_RULES] THEN REWRITE_TAC[ISSOME_CASES; option_DISTINCT]);;

let ISNONE_RULES,ISNONE_INDUCT,ISNONE_CASES = new_inductive_definition
  `ISNONE NONE:bool`;;

let ISNONE = prove
 (`(!x:A. ~ISNONE (SOME x)) /\
   ISNONE (NONE:A option)`,
  REWRITE_TAC[ISNONE_RULES] THEN REWRITE_TAC[ISNONE_CASES; option_DISTINCT]);;

let NOT_ISSOME = prove
 (`!x:A option. ~ISSOME x <=> ISNONE x`,
  REWRITE_TAC[FORALL_OPTION; ISSOME; ISNONE]);;

let NOT_ISNONE = prove
 (`!x:A option. ~ISNONE x <=> ISSOME x`,
  REWRITE_TAC[FORALL_OPTION; ISSOME; ISNONE]);;

let OPTION_EXTENSION = prove
 (`!x y:A option. x = y <=> (ISSOME x <=> ISSOME y) /\
                            GETOPTION x = GETOPTION y`,
  REWRITE_TAC[FORALL_OPTION; ISSOME; GETOPTION; option_DISTINCT; option_INJ]);;

(* ------------------------------------------------------------------------- *)
(* Dictionaries.                                                             *)
(* ------------------------------------------------------------------------- *)

let dict_INDUCT,dict_RECUR = define_type
  "dict = Dict (A -> B option)";;

let LOOKUPOPT = define
  `LOOKUPOPT (Dict d:(A,B)dict) k = d k`;;

let LOOKUPOPT_INJ = prove
 (`!d1 d2:(A,B)dict. LOOKUPOPT d1 = LOOKUPOPT d2 ==> d1 = d2`,
  MATCH_MP_TAC dict_INDUCT THEN INTRO_TAC "![d1]" THEN
  MATCH_MP_TAC dict_INDUCT THEN INTRO_TAC "![d2]" THEN
  REWRITE_TAC[FUN_EQ_THM; LOOKUPOPT; injectivity "dict"]);;

let LOOKUPOPT_EQ = prove
 (`!d1 d2:(A,B)dict. LOOKUPOPT d1 = LOOKUPOPT d2 <=> d1 = d2`,
  MESON_TAC[LOOKUPOPT_INJ]);;

let KEYS = define
  `KEYS (d:(A,B)dict) = {k | ISSOME (LOOKUPOPT d k)}`;;

let IN_KEYS = prove
 (`!k d:(A,B)dict. k IN KEYS d <=> ISSOME (LOOKUPOPT d k)`,
  REWRITE_TAC[KEYS; IN_ELIM_THM]);;

let LOOKUPOPT_EQ_NONE_EQ = prove
 (`!d:(A,B)dict k. LOOKUPOPT d k = NONE <=> ~(k IN KEYS d)`,
  REWRITE_TAC[IN_KEYS] THEN MESON_TAC[ISSOME; cases "option"]);;

let LOOKUPOPT_EQ_NONE = prove
 (`!d:(A,B)dict k. ~(k IN KEYS d) ==> LOOKUPOPT d k = NONE`,
  MESON_TAC[LOOKUPOPT_EQ_NONE_EQ]);;

let DICT_LOOKUPOPT_EXTENSION = prove
 (`!d1 d2:(A,B)dict.
     d1 = d2 <=> (!k. LOOKUPOPT d1 k = LOOKUPOPT d2 k)`,
  REWRITE_TAC[GSYM LOOKUPOPT_EQ; FUN_EQ_THM]);;

let LOOKUP = new_definition
  `LOOKUP (d:(A,B)dict) k = GETOPTION (LOOKUPOPT d k)`;;

let LOOKUPDEFAULT = new_definition
  `LOOKUPDEFAULT (d:(A,B)dict) a k = DEFAULT a (LOOKUPOPT d k)`;;

let DICT_LOOKUP_EXTENSION = prove
 (`!d1 d2:(A,B)dict.
     d1 = d2 <=> KEYS d1 = KEYS d2 /\
                 (!k. k IN KEYS d1 ==> LOOKUP d1 k = LOOKUP d2 k)`,
  SUBGOAL_THEN
    `!d1 d2:(A,B)dict.
       KEYS d1 = KEYS d2 /\
       (!k. k IN KEYS d1 ==> LOOKUP d1 k = LOOKUP d2 k)
       ==> LOOKUPOPT d1 = LOOKUPOPT d2`
    (fun th -> ASM_MESON_TAC[th; LOOKUPOPT_INJ]) THEN
  REWRITE_TAC[EXTENSION; IN_KEYS; LOOKUP; LOOKUPOPT] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  INTRO_TAC "![k]" THEN REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC `k:A`)) THEN
  STRUCT_CASES_TAC (ISPEC `LOOKUPOPT (d1:(A,B)dict) k` (cases "option")) THEN
  STRUCT_CASES_TAC (ISPEC `LOOKUPOPT (d2:(A,B)dict) k` (cases "option")) THEN
  REWRITE_TAC[ISSOME; GETOPTION; option_INJ]);;

(* ------------------------------------------------------------------------- *)
(* Empty dictionary.                                                         *)
(* ------------------------------------------------------------------------- *)

let EMPTYDICT = new_definition
  `EMPTYDICT : (A,B)dict = Dict(\k. NONE)`;;

let LOOKUPOPT_EMPTYDICT = prove
 (`!k. LOOKUPOPT (EMPTYDICT:(A,B)dict) k = NONE`,
  REWRITE_TAC[EMPTYDICT; LOOKUPOPT]);;

let KEYS_EMPTYDICT = prove
 (`KEYS (EMPTYDICT:(A,B)dict) = {}`,
  REWRITE_TAC[EXTENSION; IN_KEYS; NOT_IN_EMPTY; LOOKUPOPT_EMPTYDICT; ISSOME]);;

let LOOKUP_EMPTYDICT = prove
 (`!k. LOOKUP (EMPTYDICT:(A,B)dict) k = GETOPTION NONE`,
  REWRITE_TAC[LOOKUP; LOOKUPOPT_EMPTYDICT]);;

let LOOKUPDEFAULT_EMPTYDICT = prove
 (`!a k. LOOKUPDEFAULT (EMPTYDICT:(A,B)dict) a k = a`,
  REWRITE_TAC[LOOKUPDEFAULT; LOOKUPOPT_EMPTYDICT; DEFAULT]);;

(* ------------------------------------------------------------------------- *)
(* Updating a dictionary.                                                    *)
(* ------------------------------------------------------------------------- *)

let UPDATE = new_definition
  `UPDATE (d:(A,B)dict) k0 v0 =
   Dict(\k. if k = k0 then SOME v0 else LOOKUPOPT d k)`;;

let LOOKUPOPT_UPDATE = prove
 (`!d k0 v0 k. LOOKUPOPT (UPDATE (d:(A,B)dict) k0 v0) k =
               if k = k0 then SOME v0 else LOOKUPOPT d k`,
  REWRITE_TAC[LOOKUPOPT; UPDATE]);;

let KEYS_UPDATE = prove
 (`!d k0:A v0:B. KEYS (UPDATE d k0 v0) = k0 INSERT KEYS d`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_KEYS; LOOKUPOPT_UPDATE; IN_INSERT] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[ISSOME_RULES]);;

let LOOKUP_UPDATE = prove
 (`!d k0 v0 k. LOOKUP (UPDATE (d:(A,B)dict) k0 v0) k =
               if k = k0 then v0 else LOOKUP d k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOKUP; LOOKUPOPT_UPDATE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GETOPTION]);;

let LOOKUPDEFAULT_UPDATE = prove
 (`!d k0 v0 a k. LOOKUPDEFAULT (UPDATE (d:(A,B)dict) k0 v0) a k =
                 if k = k0 then v0 else LOOKUPDEFAULT d a k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOKUPDEFAULT; LOOKUPOPT_UPDATE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DEFAULT]);;

(* ------------------------------------------------------------------------- *)
(* Removing an association from a dictionary.                                *)
(* ------------------------------------------------------------------------- *)

let REMOVE = new_definition
  `REMOVE (d:(A,B)dict) k0 = Dict(\k. if k = k0 then NONE else LOOKUPOPT d k)`;;

let LOOKUPOPT_REMOVE = prove
 (`!d k0 k. LOOKUPOPT (REMOVE (d:(A,B)dict) k0) k =
               if k = k0 then NONE else LOOKUPOPT d k`,
  REWRITE_TAC[LOOKUPOPT; REMOVE]);;

let KEYS_REMOVE = prove
 (`!d:(A,B)dict k. KEYS (REMOVE d k) = KEYS d DELETE k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_KEYS; LOOKUPOPT_REMOVE; IN_DELETE] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ISSOME]);;

let LOOKUP_REMOVE = prove
 (`!d k0 k. LOOKUP (REMOVE (d:(A,B)dict) k0) k =
            if k = k0 then GETOPTION NONE else LOOKUP d k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOKUP; LOOKUPOPT_REMOVE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let LOOKUPDEFAULT_REMOVE = prove
 (`!d k0  k. LOOKUPDEFAULT (REMOVE (d:(A,B)dict) k0) a k =
             if k = k0 then a else LOOKUPDEFAULT d a k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOKUPDEFAULT; LOOKUPOPT_REMOVE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DEFAULT]);;

(* ------------------------------------------------------------------------- *)
(* Dictionary with a single association.                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("=>",(12,"right"));;

let PAIRDICT = new_definition
  `(k:A => v:B) = Dict(\l. if l = k then SOME v else NONE)`;;

let LOOKUPOPT_PAIRDICT = prove
 (`!k:A v:B l. LOOKUPOPT (k => v) l = if l = k then SOME v else NONE`,
  REWRITE_TAC[PAIRDICT; LOOKUPOPT]);;

let KEYS_PAIRDICT = prove
 (`!k:A v:B. KEYS (k => v) = {k}`,
  REWRITE_TAC[EXTENSION; IN_KEYS; LOOKUPOPT_PAIRDICT;
              IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT GEN_TAC THEN  COND_CASES_TAC THEN ASM_REWRITE_TAC[ISSOME]);;

let LOOKUP_PAIRDICT = prove
 (`!k:A v:B l. LOOKUP (k => v) l = if l = k then v else GETOPTION NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOKUP; LOOKUPOPT_PAIRDICT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GETOPTION]);;

let LOOKUPDEFAULT_PAIRDICT = prove
 (`!k:A v:B a l. LOOKUPDEFAULT (k => v) a l = if l = k then v else a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOKUPDEFAULT; LOOKUPOPT_PAIRDICT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DEFAULT]);;

let UPDATE_EMPTYDICT = prove
 (`!k:A v:B. UPDATE EMPTYDICT k v = (k => v)`,
  REWRITE_TAC[DICT_LOOKUPOPT_EXTENSION; KEYS_UPDATE;
              KEYS_PAIRDICT; KEYS_EMPTYDICT] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; LOOKUPOPT_UPDATE;
              LOOKUPOPT_PAIRDICT; LOOKUPOPT_EMPTYDICT]);;
