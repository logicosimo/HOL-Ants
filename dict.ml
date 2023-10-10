(* ========================================================================= *)
(* Dictionaries (partial functions).                                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Miscellanea.                                                              *)
(* ------------------------------------------------------------------------- *)

let IMAGE_EQ = prove
 (`!f g:A->B s. (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN MESON_TAC[]);;

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
  REWRITE_TAC[FORALL_OPTION_THM; ISSOME; GETOPTION;
              option_DISTINCT; option_INJ]);;

let OPTION_MERGE = define
  `(!x y:A. OPTION_MERGE op (SOME x) (SOME y) = SOME (op x y)) /\
   (!x. OPTION_MERGE op (SOME x) NONE = SOME x) /\
   (!x. OPTION_MERGE op NONE (SOME x) = SOME x) /\
   OPTION_MERGE op NONE NONE = NONE`;;

let ISSOME_OPTION_MERGE = prove
 (`!x y:A option. ISSOME (OPTION_MERGE op x y) <=> ISSOME x \/ ISSOME y`,
  REWRITE_TAC[FORALL_OPTION_THM; OPTION_MERGE; ISSOME]);;

let ISNONE_OPTION_MERGE = prove
 (`!x y:A option. ISNONE (OPTION_MERGE op x y) <=> ISNONE x /\ ISNONE y`,
  REWRITE_TAC[FORALL_OPTION_THM; OPTION_MERGE; ISNONE]);;

(* ------------------------------------------------------------------------- *)
(* Dictionaries.                                                             *)
(* ------------------------------------------------------------------------- *)

let dict_INDUCT,dict_RECUR = define_type
  "dict = Dict (A -> B option)";;

let LOOKUP = define
  `LOOKUP (Dict d:(A,B)dict) k = d k`;;

let LOOKUP_INJ = prove
 (`!d1 d2:(A,B)dict. LOOKUP d1 = LOOKUP d2 ==> d1 = d2`,
  MATCH_MP_TAC dict_INDUCT THEN INTRO_TAC "![d1]" THEN
  MATCH_MP_TAC dict_INDUCT THEN INTRO_TAC "![d2]" THEN
  REWRITE_TAC[FUN_EQ_THM; LOOKUP; injectivity "dict"]);;

let LOOKUP_EQ = prove
 (`!d1 d2:(A,B)dict. LOOKUP d1 = LOOKUP d2 <=> d1 = d2`,
  MESON_TAC[LOOKUP_INJ]);;

let KEYS = define
  `KEYS (d:(A,B)dict) = {k | ISSOME (LOOKUP d k)}`;;

let IN_KEYS = prove
 (`!k d:(A,B)dict. k IN KEYS d <=> ISSOME (LOOKUP d k)`,
  REWRITE_TAC[KEYS; IN_ELIM_THM]);;

let LOOKUP_EQ_NONE_EQ = prove
 (`!d:(A,B)dict k. LOOKUP d k = NONE <=> ~(k IN KEYS d)`,
  REWRITE_TAC[IN_KEYS] THEN MESON_TAC[ISSOME; cases "option"]);;

let LOOKUP_EQ_NONE = prove
 (`!d:(A,B)dict k. ~(k IN KEYS d) ==> LOOKUP d k = NONE`,
  MESON_TAC[LOOKUP_EQ_NONE_EQ]);;

let DICT_LOOKUP_EXTENSION = prove
 (`!d1 d2:(A,B)dict.
     d1 = d2 <=> (!k. LOOKUP d1 k = LOOKUP d2 k)`,
  REWRITE_TAC[GSYM LOOKUP_EQ; FUN_EQ_THM]);;

let GET = new_definition
  `GET (d:(A,B)dict) k = GETOPTION (LOOKUP d k)`;;

let LOOKUP_EQ_SOME = prove
 (`!d:(K,V)dict k. k IN KEYS d ==> LOOKUP d k = SOME (GET d k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GET; IN_KEYS] THEN
  STRUCT_CASES_TAC (ISPEC `LOOKUP (d:(K,V)dict) k` (cases "option")) THEN
  REWRITE_TAC[ISSOME; GETOPTION]);;

let GETDEFAULT = new_definition
  `GETDEFAULT (d:(A,B)dict) a k = DEFAULT a (LOOKUP d k)`;;

let LOOKUP_EQ_GET = prove
 (`!d:(K,V)dict k.
     LOOKUP d k = if k IN KEYS d then SOME (GET d k) else NONE`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[LOOKUP_EQ_SOME; LOOKUP_EQ_NONE]);;

let DICT_GET_EXTENSION = prove
 (`!d1 d2:(A,B)dict.
     d1 = d2 <=> KEYS d1 = KEYS d2 /\
                 (!k. k IN KEYS d1 ==> GET d1 k = GET d2 k)`,
  SUBGOAL_THEN
    `!d1 d2:(A,B)dict.
       KEYS d1 = KEYS d2 /\
       (!k. k IN KEYS d1 ==> GET d1 k = GET d2 k)
       ==> LOOKUP d1 = LOOKUP d2`
    (fun th -> ASM_MESON_TAC[th; LOOKUP_INJ]) THEN
  REWRITE_TAC[EXTENSION; IN_KEYS; GET; LOOKUP] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  INTRO_TAC "![k]" THEN REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC `k:A`)) THEN
  STRUCT_CASES_TAC (ISPEC `LOOKUP (d1:(A,B)dict) k` (cases "option")) THEN
  STRUCT_CASES_TAC (ISPEC `LOOKUP (d2:(A,B)dict) k` (cases "option")) THEN
  REWRITE_TAC[ISSOME; GETOPTION; option_INJ]);;

(* ------------------------------------------------------------------------- *)
(* Dictionary associated to a function.                                      *)
(* ------------------------------------------------------------------------- *)

let FUNDICT = new_definition
  `FUNDICT K (f:A->B) = Dict(\k. if k IN K then SOME (f k) else NONE)`;;

let LOOKUP_FUNDICT = prove
 (`!K f:A->B k. LOOKUP (FUNDICT K f) k =
                if k IN K then SOME (f k) else NONE`,
  REWRITE_TAC[FUNDICT; LOOKUP]);;

let KEYS_FUNDICT = prove
 (`!K f:A->B. KEYS (FUNDICT K f) = K`,
  REWRITE_TAC[EXTENSION; IN_KEYS; LOOKUP_FUNDICT] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[ISSOME]);;

let GET_FUNDICT = prove
 (`!K f:A->B k. GET (FUNDICT K f) k =
                if k IN K then f k else GETOPTION NONE`,
  REWRITE_TAC[GET; LOOKUP_FUNDICT] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[ISSOME; GETOPTION]);;

(* ------------------------------------------------------------------------- *)
(* Empty dictionary.                                                         *)
(* ------------------------------------------------------------------------- *)

let EMPTYDICT = new_definition
  `EMPTYDICT : (A,B)dict = FUNDICT {} ARB`;;

let KEYS_EMPTYDICT = prove
 (`KEYS (EMPTYDICT:(A,B)dict) = {}`,
  REWRITE_TAC[EMPTYDICT; KEYS_FUNDICT]);;

let GET_EMPTYDICT = prove
 (`!k. GET (EMPTYDICT:(A,B)dict) k = GETOPTION NONE`,
  REWRITE_TAC[EMPTYDICT; GET_FUNDICT; NOT_IN_EMPTY]);;

let LOOKUP_EMPTYDICT = prove
 (`!k. LOOKUP (EMPTYDICT:(A,B)dict) k = NONE`,
  REWRITE_TAC[LOOKUP_EQ_GET; KEYS_EMPTYDICT; NOT_IN_EMPTY]);;

let GETDEFAULT_EMPTYDICT = prove
 (`!a k. GETDEFAULT (EMPTYDICT:(A,B)dict) a k = a`,
  REWRITE_TAC[GETDEFAULT; LOOKUP_EMPTYDICT; DEFAULT]);;

let DICT_EQ_EMPTY = prove
 (`!d:(K,V)dict. d = EMPTYDICT <=> KEYS d = {}`,
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_EMPTYDICT] THEN
  MESON_TAC[NOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Updating a dictionary.                                                    *)
(* ------------------------------------------------------------------------- *)

let UPDATE = new_definition
  `UPDATE (d:(A,B)dict) k0 v0 =
   Dict(\k. if k = k0 then SOME v0 else LOOKUP d k)`;;

let LOOKUP_UPDATE = prove
 (`!d k0 v0 k. LOOKUP (UPDATE (d:(A,B)dict) k0 v0) k =
               if k = k0 then SOME v0 else LOOKUP d k`,
  REWRITE_TAC[LOOKUP; UPDATE]);;

let KEYS_UPDATE = prove
 (`!d k0:A v0:B. KEYS (UPDATE d k0 v0) = k0 INSERT KEYS d`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_KEYS; LOOKUP_UPDATE; IN_INSERT] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[ISSOME_RULES]);;

let GET_UPDATE = prove
 (`!d k0 v0 k. GET (UPDATE (d:(A,B)dict) k0 v0) k =
               if k = k0 then v0 else GET d k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GET; LOOKUP_UPDATE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GETOPTION]);;

let GETDEFAULT_UPDATE = prove
 (`!d k0 v0 a k. GETDEFAULT (UPDATE (d:(A,B)dict) k0 v0) a k =
                 if k = k0 then v0 else GETDEFAULT d a k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GETDEFAULT; LOOKUP_UPDATE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DEFAULT]);;

let UPDATE_IDEMPOT = prove
 (`!d:(K,V)dict k u v. UPDATE (UPDATE d k u) k v = UPDATE d k v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_UPDATE; INSERT_INSERT;
              FORALL_IN_INSERT; GET_UPDATE] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Dictionary with a single association.                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("=>",(12,"right"));;

let PAIRDICT = new_definition
  `(k:A => v:B) = FUNDICT {k} (\k. v)`;;

let KEYS_PAIRDICT = prove
 (`!k:A v:B. KEYS (k => v) = {k}`,
  REWRITE_TAC[PAIRDICT; KEYS_FUNDICT]);;

let GET_PAIRDICT = prove
 (`!k:A v:B l. GET (k => v) l = if l = k then v else GETOPTION NONE`,
  REWRITE_TAC[PAIRDICT; GET_FUNDICT; IN_SING]);;

let LOOKUP_PAIRDICT = prove
 (`!k:A v:B l. LOOKUP (k => v) l = if l = k then SOME v else NONE`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LOOKUP_EQ_GET; KEYS_PAIRDICT; IN_SING;
              GET_PAIRDICT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let GETDEFAULT_PAIRDICT = prove
 (`!k:A v:B a l. GETDEFAULT (k => v) a l = if l = k then v else a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GETDEFAULT; LOOKUP_PAIRDICT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DEFAULT]);;

let UPDATE_EMPTYDICT = prove
 (`!k:A v:B. UPDATE EMPTYDICT k v = (k => v)`,
  REWRITE_TAC[DICT_LOOKUP_EXTENSION; KEYS_UPDATE;
              KEYS_PAIRDICT; KEYS_EMPTYDICT] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; LOOKUP_UPDATE;
              LOOKUP_PAIRDICT; LOOKUP_EMPTYDICT]);;

(* ------------------------------------------------------------------------- *)
(* Removing an association from a dictionary.                                *)
(* ------------------------------------------------------------------------- *)

let REMOVE = new_definition
  `REMOVE (d:(A,B)dict) k0 =
   Dict(\k. if k = k0 then NONE else LOOKUP d k)`;;

let LOOKUP_REMOVE = prove
 (`!d k0 k. LOOKUP (REMOVE (d:(A,B)dict) k0) k =
               if k = k0 then NONE else LOOKUP d k`,
  REWRITE_TAC[LOOKUP; REMOVE]);;

let KEYS_REMOVE = prove
 (`!d:(A,B)dict k. KEYS (REMOVE d k) = KEYS d DELETE k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_KEYS; LOOKUP_REMOVE; IN_DELETE] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ISSOME]);;

let GET_REMOVE = prove
 (`!d k0 k. GET (REMOVE (d:(A,B)dict) k0) k =
            if k = k0 then GETOPTION NONE else GET d k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GET; LOOKUP_REMOVE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let GETDEFAULT_REMOVE = prove
 (`!d k0  k. GETDEFAULT (REMOVE (d:(A,B)dict) k0) a k =
             if k = k0 then a else GETDEFAULT d a k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GETDEFAULT; LOOKUP_REMOVE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DEFAULT]);;

let REMOVE_EMPTYDICT = prove
 (`!k. REMOVE EMPTYDICT k = EMPTYDICT:(K,V)dict`,
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_REMOVE; KEYS_EMPTYDICT;
              EMPTY_DELETE; NOT_IN_EMPTY]);;

let REMOVE_UPDATE = prove
 (`!d:(K,V)dict k v l.
     REMOVE (UPDATE d k v) l =
     if k = l then REMOVE d l else UPDATE (REMOVE d l) k v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DICT_GET_EXTENSION] THEN COND_CASES_TAC THENL
  [POP_ASSUM SUBST1_TAC THEN
   REWRITE_TAC[KEYS_REMOVE; KEYS_UPDATE] THEN
   CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[IN_DELETE; IN_INSERT; GET_REMOVE; GET_UPDATE] THEN MESON_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[KEYS_REMOVE; KEYS_UPDATE] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_DELETE; IMP_CONJ; FORALL_IN_INSERT;
              GET_REMOVE; GET_UPDATE] THEN
  MESON_TAC[]);;

let REMOVE_PAIRDICT = prove
 (`!k:K v:V l. REMOVE (k => v) l = if k = l then EMPTYDICT else (k => v)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_REMOVE; KEYS_PAIRDICT] THEN
  COND_CASES_TAC THENL
  [POP_ASSUM SUBST1_TAC THEN
   REWRITE_TAC[KEYS_EMPTYDICT; IN_DELETE; IMP_CONJ; FORALL_IN_INSERT;
               GET_REMOVE; GET_EMPTYDICT; GET_PAIRDICT; NOT_IN_EMPTY] THEN
   SET_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_DELETE; IMP_CONJ; FORALL_IN_INSERT; NOT_IN_EMPTY;
                  KEYS_PAIRDICT; GET_REMOVE; GET_PAIRDICT] THEN
  ASM SET_TAC []);;

(* ------------------------------------------------------------------------- *)
(* Restriction of a dictionary.                                              *)
(* ------------------------------------------------------------------------- *)

let DICT_RESTRICT = new_definition
  `DICT_RESTRICT K (d:(K,V)dict) = FUNDICT K (GET d)`;;

let KEYS_DICT_RESTRICT = prove
 (`!K d:(K,V)dict. KEYS (DICT_RESTRICT K d) = K`,
  REWRITE_TAC[DICT_RESTRICT; KEYS_FUNDICT]);;

let GET_DICT_RESTRICT = prove
 (`!K d:(K,V)dict k. GET (DICT_RESTRICT K d) k =
                     if k IN K then GET d k else GETOPTION NONE`,
  REWRITE_TAC[DICT_RESTRICT; GET_FUNDICT]);;

let DICT_RESTRICT_EMPTY = prove
 (`!d:(K,V)dict. DICT_RESTRICT {} d = EMPTYDICT`,
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_RESTRICT;
              KEYS_EMPTYDICT; NOT_IN_EMPTY]);;

let DICT_RESTRICT_INSERT = prove
 (`!k K d:(K,V)dict.
     DICT_RESTRICT (k INSERT K) d =
     UPDATE (DICT_RESTRICT K d) k (GET d k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_RESTRICT; KEYS_UPDATE] THEN
  REWRITE_TAC[FORALL_IN_INSERT; GET_DICT_RESTRICT; GET_UPDATE] THEN
  REWRITE_TAC[IN_INSERT] THEN SIMP_TAC[] THEN MESON_TAC[]);;

let DICT_UPDATE_RESTRICT = prove
 (`!d:(K,V)dict k v.
     UPDATE d k v = UPDATE (DICT_RESTRICT (KEYS d DELETE k) d) k v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DICT_GET_EXTENSION] THEN CONJ_TAC THENL
  [REWRITE_TAC[KEYS_UPDATE; KEYS_DICT_RESTRICT] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[KEYS_UPDATE; FORALL_IN_INSERT; GET_UPDATE;
              GET_DICT_RESTRICT; IN_DELETE] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Combine two dictionaries.                                                 *)
(* ------------------------------------------------------------------------- *)

let DICT_COMBINE = new_definition
  `DICT_COMBINE (op:A->A->A) d1 d2 =
   Dict (\k:K. lifted op (LOOKUP d1 k) (LOOKUP d2 k))`;;

let LOOKUP_DICT_COMBINE = prove
 (`!op d1 d2 k. LOOKUP (DICT_COMBINE (op:V->V->V) d1 d2) (k:K) =
                lifted op (LOOKUP d1 k) (LOOKUP d2 k)`,
  REWRITE_TAC[DICT_COMBINE; LOOKUP]);;

let ISSOME_LIFTED = prove
 (`!op:A->A->A x y. ISSOME (lifted op x y) <=> ISSOME x /\ ISSOME y`,
  REWRITE_TAC[FORALL_OPTION_THM; lifted; ISSOME]);;

let KEYS_DICT_COMBINE = prove
 (`!op d1 d2:(K,V)dict.
     KEYS (DICT_COMBINE op d1 d2) = KEYS d1 INTER KEYS d2`,
  REWRITE_TAC[EXTENSION; IN_KEYS; LOOKUP_DICT_COMBINE;
              IN_INTER; ISSOME_LIFTED]);;

let GET_DICT_COMBINE = prove
 (`!op d1 d2 k.
     k IN KEYS d1 /\ k IN KEYS d2
     ==> GET (DICT_COMBINE (op:V->V->V) d1 d2) (k:K) =
         op (GET d1 k) (GET d2 k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GET; LOOKUP_DICT_COMBINE] THEN
  SIMP_TAC[LOOKUP_EQ_SOME] THEN REWRITE_TAC[GETOPTION; lifted]);;

(* ------------------------------------------------------------------------- *)
(* Mapping on dictionary values                                              *)
(* ------------------------------------------------------------------------- *)

let DICT_MAP = new_definition
  `DICT_MAP (f:A->B) (d:(K,A)dict) : (K,B)dict =
   FUNDICT (KEYS d) (\k. f (GET d k))`;;

let KEYS_DICT_MAP = prove
 (`!f:A->B d:(K,A)dict. KEYS (DICT_MAP f d) = KEYS d`,
   REWRITE_TAC[DICT_MAP; KEYS_FUNDICT]);;

let GET_DICT_MAP = prove
 (`!f:A->B d:(K,A)dict k.
     GET (DICT_MAP f d) k =
     if k IN KEYS d then f (GET d k) else GETOPTION NONE`,
   REPEAT GEN_TAC THEN REWRITE_TAC[DICT_MAP; GET_FUNDICT] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let DICT_MAP_EMPTYDICT = prove
 (`!f:U->V. DICT_MAP f EMPTYDICT : (K,V)dict = EMPTYDICT`,
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_MAP;
              KEYS_EMPTYDICT; NOT_IN_EMPTY]);;

let DICT_IMAP = new_definition
  `DICT_IMAP (f:K->A->B) (d:(K,A)dict) : (K,B)dict =
   FUNDICT (KEYS d) (\k. f k (GET d k))`;;

let KEYS_DICT_IMAP = prove
 (`!f:K->A->B d:(K,A)dict. KEYS (DICT_IMAP f d) = KEYS d`,
   REWRITE_TAC[DICT_IMAP; KEYS_FUNDICT]);;

let GET_DICT_IMAP = prove
 (`!f:K->A->B d:(K,A)dict k.
     GET (DICT_IMAP f d) k =
     if k IN KEYS d then f k (GET d k) else GETOPTION NONE`,
   REPEAT GEN_TAC THEN REWRITE_TAC[DICT_IMAP; GET_FUNDICT] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let DICT_MAP_UPDATE = prove
 (`!f:V->W d:(K,V)dict k v.
     DICT_MAP f (UPDATE d k v) = UPDATE (DICT_MAP f d) k (f v)`,
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_MAP; KEYS_UPDATE;
              FORALL_IN_INSERT; GET_DICT_MAP; GET_UPDATE] THEN
  REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]);;

let DICT_MAP_PAIRDICT = prove
 (`!f:A->B k:K v. DICT_MAP f (k => v) = (k => f v)`,
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_MAP; KEYS_PAIRDICT;
              FORALL_IN_INSERT] THEN
  REWRITE_TAC[NOT_IN_EMPTY; GET_DICT_MAP; IN_SING; KEYS_PAIRDICT;
              GET_PAIRDICT]);;

(* ------------------------------------------------------------------------- *)
(* Values of a dictionary.                                                   *)
(* ------------------------------------------------------------------------- *)

let DICT_VALS = new_definition
  `DICT_VALS (d:(K,V)dict) : V->bool = IMAGE (GET d) (KEYS d)`;;

let IN_DICT_VALS = prove
 (`!v d:(K,V)dict. v IN DICT_VALS d <=> ?k. k IN KEYS d /\ GET d k = v`,
  REWRITE_TAC[DICT_VALS; IN_IMAGE] THEN MESON_TAC[]);;

let DICT_VALS_EMPTYDICT = prove
 (`DICT_VALS (EMPTYDICT:(K,V)dict) = {}`,
  REWRITE_TAC[EXTENSION; IN_DICT_VALS; KEYS_EMPTYDICT; NOT_IN_EMPTY]);;

let DICT_VALS_PAIRDICT = prove
 (`!k:K v:V. DICT_VALS (k => v) = {v}`,
  REWRITE_TAC[EXTENSION; DICT_VALS; IN_SING; KEYS_PAIRDICT;
              IMAGE_CLAUSES; GET_PAIRDICT]);;

let DICT_VALS_FUNDICT = prove
 (`!K f:A->B. DICT_VALS (FUNDICT K f) = IMAGE f K`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DICT_VALS; KEYS_FUNDICT; GET_FUNDICT] THEN
  MATCH_MP_TAC IMAGE_EQ THEN SIMP_TAC[GET_FUNDICT]);;

let DICT_VALS_UPDATE = prove
 (`!d:(K,V)dict k v.
     DICT_VALS (UPDATE d k v) = v INSERT DICT_VALS (REMOVE d k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; DICT_VALS; KEYS_UPDATE;
    FORALL_IN_IMAGE; FORALL_IN_INSERT; KEYS_REMOVE] THEN CONJ_TAC THENL
  [REWRITE_TAC[GET_UPDATE; IN_INSERT] THEN
   REWRITE_TAC[IN_IMAGE; IN_DELETE; GET_REMOVE] THEN MESON_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES; GET_UPDATE; IN_INSERT] THEN
  SIMP_TAC[IN_DELETE; GET_REMOVE; IN_IMAGE; GET_UPDATE] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Monoidal combination of two dictionaries.                                 *)
(* (Sensible definition when op is monoidal)                                 *)
(* ------------------------------------------------------------------------- *)

let DICT_MERGE = new_definition
  `DICT_MERGE op d1 d2 : (K,V)dict =
   Dict(\k. OPTION_MERGE op (LOOKUP d1 k) (LOOKUP d2 k))`;;

let LOOKUP_DICT_MERGE = prove
 (`!op d1 d2:(K,V)dict. LOOKUP (DICT_MERGE op d1 d2) k =
                        OPTION_MERGE op (LOOKUP d1 k) (LOOKUP d2 k)`,
  REWRITE_TAC[DICT_MERGE; LOOKUP]);;

let KEYS_DICT_MERGE = prove
 (`!op d1 d2:(K,V)dict. KEYS (DICT_MERGE op d1 d2) =
                        KEYS d1 UNION KEYS d2`,
  REWRITE_TAC[KEYS; LOOKUP_DICT_MERGE; ISSOME_OPTION_MERGE] THEN SET_TAC[]);;

let GET_DICT_MERGE = prove
 (`!op d1 d2:(K,V)dict k.
     GET (DICT_MERGE op d1 d2) k =
     if k IN KEYS d1
     then if k IN KEYS d2
          then op (GET d1 k) (GET d2 k)
          else GET d1 k
     else if k IN KEYS d2
          then GET d2 k
          else GETOPTION NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GET; LOOKUP_DICT_MERGE] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[LOOKUP_EQ_SOME; LOOKUP_EQ_NONE; OPTION_MERGE; GETOPTION]);;

let GET_DICT_MERGE_DISJOINT_KEYS = prove
 (`!op d1 d2:(K,V)dict.
     DISJOINT (KEYS d1) (KEYS d2)
     ==> GET (DICT_MERGE op d1 d2) k =
         if k IN KEYS d1 then GET d1 k else
         if k IN KEYS d2 then GET d2 k else
         GETOPTION NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GET_DICT_MERGE] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM SET_TAC[]);;

let DICT_MERGE_EMPTYDICT = prove
 (`!op d:(K,V)dict. DICT_MERGE op EMPTYDICT d = d`,
  SIMP_TAC[DICT_GET_EXTENSION; KEYS_DICT_MERGE; KEYS_EMPTYDICT;
           UNION_EMPTY; GET_DICT_MERGE; NOT_IN_EMPTY]);;

let DICT_MERGE_UPDATE = prove
 (`!op d e k:K v:V.
     DICT_MERGE op (UPDATE d k v) e =
     UPDATE (DICT_MERGE op d e) k (if k IN KEYS e then op v (GET e k) else v)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_MERGE; KEYS_UPDATE] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_UNION;
              GET_DICT_MERGE; GET_UPDATE; KEYS_UPDATE] THEN
  REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]);;

let DICT_MERGE_PAIRDICT = prove
 (`!op k v d:(K,V)dict.
     DICT_MERGE op (k => v) d =
     UPDATE d k (if k IN KEYS d then op v (GET d k) else v)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_MERGE;
              KEYS_PAIRDICT; KEYS_UPDATE] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_INSERT; NOT_IN_EMPTY; KEYS_PAIRDICT;
              GET_DICT_MERGE; GET_UPDATE; GET_PAIRDICT] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
  [POP_ASSUM SUBST_VAR_TAC THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Union of two dictionaries.                                                *)
(* ------------------------------------------------------------------------- *)

let DICT_UNION = new_definition
  `DICT_UNION d1 d2 : (K,V)dict = DICT_MERGE (CURRY FST) d1 d2`;;

let GET_DICT_UNION = prove
 (`!d1 d2:(K,V)dict k.
     GET (DICT_UNION d1 d2) k =
     if k IN KEYS d1 then GET d1 k else
     if k IN KEYS d2 then GET d2 k else
     GETOPTION NONE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DICT_UNION; GET_DICT_MERGE] THEN
  REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[CURRY_DEF]));;

let KEYS_DICT_UNION = prove
 (`!d1 d2:(K,V)dict. KEYS (DICT_UNION d1 d2) = KEYS d1 UNION KEYS d2`,
  REWRITE_TAC[DICT_UNION; KEYS_DICT_MERGE]);;

let GET_DICT_UNION_DISJOINT_KEYS = prove
 (`!d1 d2:(K,V)dict.
     DISJOINT (KEYS d1) (KEYS d2)
     ==> GET (DICT_UNION d1 d2) k =
         if k IN KEYS d1 then GET d1 k else
         if k IN KEYS d2 then GET d2 k else
         GETOPTION NONE`,
  SIMP_TAC[DICT_UNION; GET_DICT_MERGE_DISJOINT_KEYS]);;

let DICT_UNION_PAIRDICT = prove
 (`!k:K v:V d. DICT_UNION (k => v) d = UPDATE d k v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DICT_GET_EXTENSION] THEN
  REWRITE_TAC[KEYS_DICT_UNION; KEYS_UPDATE; KEYS_PAIRDICT] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GET_DICT_UNION; GET_UPDATE; KEYS_PAIRDICT;
              GET_PAIRDICT; IN_SING] THEN
  MESON_TAC[]);;

let DICT_UNION_RESTRICT = prove
 (`!d1 d2:(K,V)dict. DICT_UNION d1 d2 =
                     DICT_UNION d1 (DICT_RESTRICT (KEYS d2 DIFF KEYS d1) d2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_UNION; KEYS_DICT_RESTRICT] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[FORALL_IN_UNION; GET_DICT_UNION] THEN
  GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[KEYS_DICT_RESTRICT; IN_DIFF; GET_DICT_RESTRICT]);;

let DICT_MAP_DICT_UNION = prove
 (`!f:U->V d1 d2:(K,U)dict. DICT_MAP f (DICT_UNION d1 d2) =
                            DICT_UNION (DICT_MAP f d1) (DICT_MAP f d2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_MAP; KEYS_DICT_UNION;
              IN_UNION; GET_DICT_MAP; GET_DICT_UNION] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transposed dictionary.                                                    *)
(* ------------------------------------------------------------------------- *)

let DICT_TRANSPOSE = new_definition
  `DICT_TRANSPOSE (d:(K,V)dict) : (V,K->bool)dict =
   FUNDICT (DICT_VALS d) (\v. {k | k IN KEYS d /\ GET d k = v})`;;

let KEYS_DICT_TRANSPOSE = prove
 (`!d:(K,V)dict. KEYS (DICT_TRANSPOSE d) = DICT_VALS d`,
  REWRITE_TAC[DICT_TRANSPOSE; KEYS_FUNDICT]);;

let GET_DICT_TRANSPOSE = prove
 (`!d:(K,V)dict v.
     v IN DICT_VALS d
     ==> GET (DICT_TRANSPOSE d) v = {k | k IN KEYS d /\ GET d k = v}`,
  SIMP_TAC[DICT_TRANSPOSE; GET_FUNDICT]);;

let GET_DICT_TRANSPOSE_GEN = prove
 (`!d:(K,V)dict v.
     GET (DICT_TRANSPOSE d) v = if v IN DICT_VALS d
                                then {k | k IN KEYS d /\ GET d k = v}
                                else GETOPTION NONE`,
  REWRITE_TAC[DICT_TRANSPOSE; GET_FUNDICT]);;

let DICT_TRANSPOSE_EMPTYDICT = prove
 (`DICT_TRANSPOSE (EMPTYDICT:(K,V)dict) = EMPTYDICT`,
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_TRANSPOSE;
              KEYS_EMPTYDICT; DICT_VALS_EMPTYDICT; NOT_IN_EMPTY]);;

let DICT_TRANSPOSE_UPDATE = prove
 (`!d:(K,V)dict k v.
     DICT_TRANSPOSE (UPDATE d k v) =
     DICT_MERGE (UNION) (v => {k}) (DICT_TRANSPOSE (REMOVE d k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DICT_GET_EXTENSION] THEN CONJ_TAC THENL
  [REWRITE_TAC[KEYS_DICT_TRANSPOSE; KEYS_DICT_MERGE; KEYS_PAIRDICT;
     KEYS_UPDATE; GET_UPDATE; KEYS_REMOVE; GET_REMOVE; EXTENSION;
     IN_DICT_VALS; IN_UNION; EXISTS_IN_INSERT; IN_DELETE] THEN
   REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[KEYS_DICT_TRANSPOSE; GET_DICT_TRANSPOSE_GEN; GET_DICT_MERGE;
    IN_DICT_VALS; KEYS_UPDATE; GET_UPDATE; KEYS_PAIRDICT; KEYS_REMOVE;
    GET_REMOVE; GET_PAIRDICT; EXISTS_IN_INSERT; IN_DELETE] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THENL
  [ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [POP_ASSUM STRIP_ASSUME_TAC THEN POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
   ASM SET_TAC[];
   ALL_TAC] THEN
  ASM_CASES_TAC `k'':K = k` THENL
  [POP_ASSUM SUBST_VAR_TAC THEN REWRITE_TAC[] THEN
   COND_CASES_TAC THENL
   [POP_ASSUM STRIP_ASSUME_TAC THEN POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
   ASM SET_TAC[];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `GET (d:(K,V)dict) k'' = v` THEN ASM_REWRITE_TAC[] THENL
  [COND_CASES_TAC THENL
   [POP_ASSUM STRIP_ASSUME_TAC THEN POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC [];
    ALL_TAC] THEN
   ASM SET_TAC[];
   ALL_TAC] THEN
   COND_CASES_TAC THENL
   [POP_ASSUM STRIP_ASSUME_TAC THEN POP_ASSUM MP_TAC THEN COND_CASES_TAC THENL
    [POP_ASSUM SUBST_VAR_TAC THEN COND_CASES_TAC THENL
     [POP_ASSUM STRIP_ASSUME_TAC THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
     ALL_TAC] THEN
    COND_CASES_TAC THENL
    [POP_ASSUM STRIP_ASSUME_TAC THEN POP_ASSUM MP_TAC THEN
     ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
     ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
  [POP_ASSUM STRIP_ASSUME_TAC THEN POP_ASSUM MP_TAC THEN
   ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
   ALL_TAC] THEN
  REFL_TAC);;

let DICT_TRANSPOSE_PAIRDICT = prove
 (`!k:K v:V. DICT_TRANSPOSE (k => v) = (v => {k})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_TRANSPOSE; KEYS_PAIRDICT;
              EXTENSION; IN_DICT_VALS; EXISTS_IN_INSERT; NOT_IN_EMPTY;
              GET_DICT_TRANSPOSE_GEN; GET_PAIRDICT] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* From multivalued dictionaries to set of dictionaries.                     *)
(* ------------------------------------------------------------------------- *)

let DICT_COLLECT = new_definition
  `DICT_COLLECT (d:(K,V->bool)dict) : (K,V)dict->bool =
   {FUNDICT (KEYS d) f | f | !k. k IN KEYS d ==> f k IN GET d k}`;;

let IN_DICT_COLLECT = prove
 (`!e d:(K,V->bool)dict.
     e IN DICT_COLLECT d <=> KEYS e = KEYS d /\
                             (!k. k IN KEYS d ==> GET e k IN GET d k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DICT_COLLECT; IN_ELIM_THM] THEN EQ_TAC THENL
  [STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
   ASM_SIMP_TAC[KEYS_FUNDICT; GET_FUNDICT];
   ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `GET (e:(K,V)dict)` THEN
  ASM_SIMP_TAC[DICT_GET_EXTENSION; KEYS_FUNDICT; GET_FUNDICT]);;

let DICT_COLLECT_EMPTYDICT = prove
 (`DICT_COLLECT (EMPTYDICT:(K,V->bool)dict) = {EMPTYDICT}`,
  GEN_REWRITE_TAC I [GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[SUBSET; IN_DICT_COLLECT; KEYS_EMPTYDICT; NOT_IN_EMPTY;
              FORALL_IN_INSERT; IN_SING; DICT_EQ_EMPTY]);;

let DICT_COLLECT_UPDATE_FRESH = prove
 (`!d:(K,V->bool)dict k v.
     ~(k IN KEYS d)
     ==> DICT_COLLECT (UPDATE d k v) =
         SETBIND (\e. IMAGE (UPDATE e k) v) (DICT_COLLECT d)`,
  REPEAT GEN_TAC THEN INTRO_TAC "k" THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET] THEN CONJ_TAC THENL
  [FIX_TAC "[e]" THEN REWRITE_TAC[IN_DICT_COLLECT] THEN
   INTRO_TAC "keys get" THEN REWRITE_TAC[IN_SETBIND; IN_DICT_COLLECT] THEN
   EXISTS_TAC `DICT_RESTRICT (KEYS (d:(K,V->bool)dict)) (e:(K,V)dict)` THEN
   REWRITE_TAC[KEYS_DICT_RESTRICT] THEN CONJ_TAC THENL
   [INTRO_TAC "![l]; l" THEN REMOVE_THEN "get" (MP_TAC o SPEC `l:K`) THEN
    ASM_SIMP_TAC[KEYS_UPDATE; IN_INSERT; GET_DICT_RESTRICT; GET_UPDATE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `GET (e:(K,V)dict) k` THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[DICT_GET_EXTENSION; KEYS_UPDATE; KEYS_DICT_RESTRICT;
                    FORALL_IN_INSERT; GET_UPDATE] THEN
    INTRO_TAC "![l]; l" THEN
    SUBGOAL_THEN `~(l:K = k)` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GET_DICT_RESTRICT];
    ALL_TAC] THEN
    REMOVE_THEN "get" (MP_TAC o SPEC `k:K`) THEN
    REWRITE_TAC[KEYS_UPDATE; IN_INSERT; GET_UPDATE];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_SETBIND; IN_DICT_COLLECT; IMP_CONJ;
              RIGHT_FORALL_IMP_THM] THEN
  INTRO_TAC "![e]; ekeys; eget" THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; KEYS_UPDATE; FORALL_IN_INSERT] THEN
  INTRO_TAC "![u]; u" THEN ASM_REWRITE_TAC[GET_UPDATE] THEN ASM_MESON_TAC[]);;

let DICT_COLLECT_UPDATE = prove
 (`!d:(K,V->bool)dict k v.
     DICT_COLLECT (UPDATE d k v) =
     SETBIND (\e. IMAGE (UPDATE e k) v)
             (DICT_COLLECT (DICT_RESTRICT (KEYS d DELETE k) d))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [DICT_UPDATE_RESTRICT] THEN
  SIMP_TAC[DICT_COLLECT_UPDATE_FRESH; KEYS_DICT_RESTRICT; IN_DELETE]);;

let DICT_COLLECT_PAIRDICT = prove
 (`!k:K s:V->bool. DICT_COLLECT (k => s) = IMAGE ((=>) k) s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DICT_COLLECT; GSYM SUBSET_ANTISYM_EQ; SUBSET;
              FORALL_IN_GSPEC; FORALL_IN_IMAGE; KEYS_PAIRDICT; GET_PAIRDICT;
              FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
  [EXISTS_TAC `f (k:K):V` THEN
   ASM_REWRITE_TAC[DICT_GET_EXTENSION; KEYS_FUNDICT; KEYS_PAIRDICT;
                   FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
   REWRITE_TAC[GET_FUNDICT; GET_PAIRDICT; IN_SING];
   EXISTS_TAC `\k:K. x:V` THEN
   ASM_REWRITE_TAC[DICT_GET_EXTENSION; KEYS_FUNDICT; KEYS_PAIRDICT;
                   FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
   REWRITE_TAC[GET_FUNDICT; GET_PAIRDICT; IN_SING]]);;

let DICT_COLLECT_DICT_UNION_DISJOINT_KEYS = prove
 (`!d1 d2:(K,V->bool)dict.
     DISJOINT (KEYS d1) (KEYS d2)
     ==> DICT_COLLECT (DICT_UNION d1 d2) =
         SETBIND (\d1. IMAGE (DICT_UNION d1) (DICT_COLLECT d2))
                 (DICT_COLLECT d1)`,
  REPEAT GEN_TAC THEN INTRO_TAC "disj" THEN
  CLAIM_TAC "rmk" `!k. k IN KEYS (d2:(K,V->bool)dict)
                       ==> ~(k IN KEYS (d1:(K,V->bool)dict))` THENL
  [HYP SET_TAC "disj" []; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC I [SUBSET] THENL
  [REWRITE_TAC[IN_DICT_COLLECT; KEYS_DICT_UNION; FORALL_IN_UNION] THEN
   INTRO_TAC "![d]; keys d1 d2" THEN
   HYP_TAC "d1" (SIMP_RULE[GET_DICT_UNION]) THEN REMOVE_THEN "d2" MP_TAC THEN
   ASM_SIMP_TAC[GET_DICT_UNION_DISJOINT_KEYS] THEN
   INTRO_TAC "d2" THEN REWRITE_TAC[IN_SETBIND; IN_DICT_COLLECT] THEN
   EXISTS_TAC `DICT_RESTRICT (KEYS (d1:(K,V->bool)dict)) (d:(K,V)dict)` THEN
   CONJ_TAC THENL
   [ASM_SIMP_TAC[KEYS_DICT_RESTRICT; GET_DICT_RESTRICT]; ALL_TAC] THEN
   REWRITE_TAC[IN_IMAGE] THEN
   EXISTS_TAC `DICT_RESTRICT (KEYS (d2:(K,V->bool)dict)) (d:(K,V)dict)` THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC[DICT_GET_EXTENSION; KEYS_DICT_UNION;
                    KEYS_DICT_RESTRICT] THEN
    ASM_SIMP_TAC[FORALL_IN_UNION; GET_DICT_UNION_DISJOINT_KEYS;
                 KEYS_DICT_RESTRICT; GET_DICT_RESTRICT] THEN
    HYP SET_TAC "disj" [];
    ALL_TAC] THEN
   SIMP_TAC[IN_DICT_COLLECT; KEYS_DICT_RESTRICT; GET_DICT_RESTRICT] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_SETBIND; IN_DICT_COLLECT; IMP_CONJ;
              RIGHT_FORALL_IMP_THM] THEN
  INTRO_TAC "![d]; keys_d; d" THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_DICT_COLLECT] THEN
  INTRO_TAC "![d']; keys_d' d'" THEN
  ASM_REWRITE_TAC[KEYS_DICT_UNION; FORALL_IN_UNION] THEN
  ASM_SIMP_TAC[GET_DICT_UNION_DISJOINT_KEYS]);;

let DICT_COLLECT_DICT_UNION = prove
 (`!d1 d2:(K,V->bool)dict.
     DICT_COLLECT (DICT_UNION d1 d2) =
     SETBIND (\d. IMAGE (DICT_UNION d)
                        (DICT_COLLECT (DICT_RESTRICT (KEYS d2 DIFF KEYS d1)
                                                     d2)))
             (DICT_COLLECT d1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [DICT_UNION_RESTRICT] THEN
  SIMP_TAC[DICT_COLLECT_DICT_UNION_DISJOINT_KEYS; KEYS_DICT_RESTRICT;
           SET_RULE `DISJOINT (s:A->bool) (t DIFF s)`]);;
