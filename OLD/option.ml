(* ========================================================================= *)
(* Options.                                                                  *)
(* ========================================================================= *)

needs "code/HOL-Ants/misc.ml";;

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
   (!u. OPTION_MERGE op u NONE = u) /\
   (!u. OPTION_MERGE op NONE u = u)`;;

let ISSOME_OPTION_MERGE = prove
 (`!x y:A option. ISSOME (OPTION_MERGE op x y) <=> ISSOME x \/ ISSOME y`,
  REWRITE_TAC[FORALL_OPTION_THM; OPTION_MERGE; ISSOME]);;

let ISNONE_OPTION_MERGE = prove
 (`!x y:A option. ISNONE (OPTION_MERGE op x y) <=> ISNONE x /\ ISNONE y`,
  REWRITE_TAC[FORALL_OPTION_THM; OPTION_MERGE; ISNONE]);;
