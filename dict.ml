(* ========================================================================= *)
(* Dictionaries (partial functions).                                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Miscellanea.                                                              *)
(* ------------------------------------------------------------------------- *)

let IMAGE_EQ = prove
 (`!f g:A->B s. (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN METIS_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Options.                                                                  *)
(* ------------------------------------------------------------------------- *)

let GETOPTION = define
  `!x:A. GETOPTION (SOME x) = x`;;

let DEFAULT = define
  `(!a x:A. DEFAULT a (SOME x) = x) /\
   (!a:A. DEFAULT a NONE = a)`;;

let OPTION_MAP = define
  `(!f:A->B. OPTION_MAP f NONE = NONE) /\
   (!f:A->B x. OPTION_MAP f (SOME x) = SOME (f x))`;;

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
  REWRITE_TAC[FORALL_OPTION_THM; ISSOME; ISNONE]);;

let NOT_ISNONE = prove
 (`!x:A option. ~ISNONE x <=> ISSOME x`,
  REWRITE_TAC[FORALL_OPTION_THM; ISSOME; ISNONE]);;

let OPTION_EXTENSION = prove
 (`!x y:A option. x = y <=> (ISSOME x <=> ISSOME y) /\
                            GETOPTION x = GETOPTION y`,
  REWRITE_TAC[FORALL_OPTION_THM; ISSOME; GETOPTION; option_DISTINCT; option_INJ]);;

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

let LOOKUPOPT_EQ_SOME = prove
 (`!d:(K,V)dict k. k IN KEYS d ==> LOOKUPOPT d k = SOME (LOOKUP d k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOKUP; IN_KEYS] THEN
  STRUCT_CASES_TAC (ISPEC `LOOKUPOPT (d:(K,V)dict) k` (cases "option")) THEN
  REWRITE_TAC[ISSOME; GETOPTION]);;

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

(* ------------------------------------------------------------------------- *)
(* Combine two dictionaries.                                                 *)
(* ------------------------------------------------------------------------- *)

let DICT_COMBINE = new_definition
  `DICT_COMBINE (op:A->A->A) d1 d2 =
   Dict (\k:K. lifted op (LOOKUPOPT d1 k) (LOOKUPOPT d2 k))`;;

let LOOKUPOPT_DICT_COMBINE = prove
 (`!op d1 d2 k. LOOKUPOPT (DICT_COMBINE (op:V->V->V) d1 d2) (k:K) =
                lifted op (LOOKUPOPT d1 k) (LOOKUPOPT d2 k)`,
  REWRITE_TAC[DICT_COMBINE; LOOKUPOPT]);;

let ISSOME_LIFTED = prove
 (`!op:A->A->A x y. ISSOME (lifted op x y) <=> ISSOME x /\ ISSOME y`,
  REWRITE_TAC[FORALL_OPTION_THM; lifted; ISSOME]);;

let KEYS_DICT_COMBINE = prove
 (`!op d1 d2:(K,V)dict.
     KEYS (DICT_COMBINE op d1 d2) = KEYS d1 INTER KEYS d2`,
  REWRITE_TAC[EXTENSION; IN_KEYS; LOOKUPOPT_DICT_COMBINE;
              IN_INTER; ISSOME_LIFTED]);;

let LOOKUP_DICT_COMBINE = prove
 (`!op d1 d2 k.
     k IN KEYS d1 /\ k IN KEYS d2
     ==> LOOKUP (DICT_COMBINE (op:V->V->V) d1 d2) (k:K) =
         op (LOOKUP d1 k) (LOOKUP d2 k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LOOKUP; LOOKUPOPT_DICT_COMBINE] THEN
  SIMP_TAC[LOOKUPOPT_EQ_SOME] THEN REWRITE_TAC[GETOPTION; lifted]);;

(* ------------------------------------------------------------------------- *)
(* From multivalued dictionaries to set of dictionaries.                     *)
(* ------------------------------------------------------------------------- *)

let DICT_COLLECT = new_definition
  `DICT_COLLECT (d:(K,V->bool)dict) : (K,V)dict->bool =
   {e | KEYS e = KEYS d /\ !k. k IN KEYS e ==> LOOKUP e k IN LOOKUP d k}`;;

(* ------------------------------------------------------------------------- *)
(* Dictionary associated to a function.                                      *)
(* ------------------------------------------------------------------------- *)

let DICTFUN = new_definition
  `DICTFUN K (f:A->B) = Dict(\k. if k IN K then SOME (f k) else NONE)`;;

let LOOKUPOPT_DICTFUN = prove
 (`!K f:A->B k. LOOKUPOPT (DICTFUN K f) k =
                if k IN K then SOME (f k) else NONE`,
  REWRITE_TAC[DICTFUN; LOOKUPOPT]);;

let KEYS_DICTFUN = prove
 (`!K f:A->B. KEYS (DICTFUN K f) = K`,
  REWRITE_TAC[EXTENSION; IN_KEYS; LOOKUPOPT_DICTFUN] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[ISSOME]);;

let LOOKUP_DICTFUN = prove
 (`!K f:A->B k. LOOKUP (DICTFUN K f) k =
                if k IN K then f k else GETOPTION NONE`,
  REWRITE_TAC[LOOKUP; LOOKUPOPT_DICTFUN] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[ISSOME; GETOPTION]);;

(* ------------------------------------------------------------------------- *)
(* Mapping on dictionary values                                              *)
(* ------------------------------------------------------------------------- *)

let DICT_MAP = new_definition
  `DICT_MAP (f:A->B) (d:(K,A)dict) : (K,B)dict =
   DICTFUN (KEYS d) (\k. f (LOOKUP d k))`;;

let KEYS_DICT_MAP = prove
 (`!f:A->B d:(K,A)dict. KEYS (DICT_MAP f d) = KEYS d`,
   REWRITE_TAC[DICT_MAP; KEYS_DICTFUN]);;

let LOOKUP_DICT_MAP = prove
 (`!f:A->B d:(K,A)dict k.
     LOOKUP (DICT_MAP f d) k =
     if k IN KEYS d then f (LOOKUP d k) else GETOPTION NONE`,
   REPEAT GEN_TAC THEN REWRITE_TAC[DICT_MAP; LOOKUP_DICTFUN] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let DICT_MAP_EMPTYDICT = prove
 (`!f:U->V. DICT_MAP f EMPTYDICT : (K,V)dict = EMPTYDICT`,
  REWRITE_TAC[DICT_LOOKUP_EXTENSION; KEYS_DICT_MAP;
              KEYS_EMPTYDICT; NOT_IN_EMPTY]);;

let DICT_IMAP = new_definition
  `DICT_IMAP (f:K->A->B) (d:(K,A)dict) : (K,B)dict =
   DICTFUN (KEYS d) (\k. f k (LOOKUP d k))`;;

let KEYS_DICT_IMAP = prove
 (`!f:K->A->B d:(K,A)dict. KEYS (DICT_IMAP f d) = KEYS d`,
   REWRITE_TAC[DICT_IMAP; KEYS_DICTFUN]);;

let LOOKUP_DICT_IMAP = prove
 (`!f:K->A->B d:(K,A)dict k.
     LOOKUP (DICT_IMAP f d) k =
     if k IN KEYS d then f k (LOOKUP d k) else GETOPTION NONE`,
   REPEAT GEN_TAC THEN REWRITE_TAC[DICT_IMAP; LOOKUP_DICTFUN] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Values of a dictionary.                                                   *)
(* ------------------------------------------------------------------------- *)

let DICT_VALS = new_definition
  `DICT_VALS (d:(K,V)dict) : V->bool = IMAGE (LOOKUP d) (KEYS d)`;;

let IN_DICT_VALS = prove
 (`!v d:(K,V)dict. v IN DICT_VALS d <=> ?k. k IN KEYS d /\ LOOKUP d k = v`,
  REWRITE_TAC[DICT_VALS; IN_IMAGE] THEN MESON_TAC[]);;

let DICT_VALS_EMPTYDICT = prove
 (`DICT_VALS (EMPTYDICT:(K,V)dict) = {}`,
  REWRITE_TAC[EXTENSION; IN_DICT_VALS; KEYS_EMPTYDICT; NOT_IN_EMPTY]);;

let DICT_VALS_PAIRDICT = prove
 (`!k:K v:V. DICT_VALS (k => v) = {v}`,
  REWRITE_TAC[EXTENSION; DICT_VALS; IN_SING; KEYS_PAIRDICT;
              IMAGE_CLAUSES; LOOKUP_PAIRDICT]);;

let DICT_VALS_DICTFUN = prove
 (`!K f:A->B. DICT_VALS (DICTFUN K f) = IMAGE f K`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DICT_VALS; KEYS_DICTFUN; LOOKUP_DICTFUN] THEN
  MATCH_MP_TAC IMAGE_EQ THEN SIMP_TAC[LOOKUP_DICTFUN]);;

(* ------------------------------------------------------------------------- *)
(* Transposed dictionary.                                                    *)
(* ------------------------------------------------------------------------- *)

let DICT_TRANSPOSE = new_definition
  `DICT_TRANSPOSE (d:(K,V)dict) : (V,K->bool)dict =
   DICTFUN (DICT_VALS d) (\v. {k | k IN KEYS d /\ LOOKUP d k = v})`;;

let KEYS_DICT_TRANSPOSE = prove
 (`!d:(K,V)dict. KEYS (DICT_TRANSPOSE d) = DICT_VALS d`,
  REWRITE_TAC[DICT_TRANSPOSE; KEYS_DICTFUN]);;

let LOOKUP_DICT_TRANSPOSE = prove
 (`!d:(K,V)dict v.
     v IN DICT_VALS d
     ==> LOOKUP (DICT_TRANSPOSE d) v = {k | k IN KEYS d /\ LOOKUP d k = v}`,
  SIMP_TAC[DICT_TRANSPOSE; LOOKUP_DICTFUN]);;
