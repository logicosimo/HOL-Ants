prioritize_num();;

(* needs "code/HOL-Ants/misc.ml";; *)
needs "code/HOL-Ants/option.ml";;

(* ------------------------------------------------------------------------- *)
(* Constructions.                                                            *)
(* ------------------------------------------------------------------------- *)

let DICTTRIE = new_definition
  `DICTTRIE f : num->A = f`;;

let DICTEMPTY = new_definition
  `DICTEMPTY (n : num) : A option = NONE`;;

let DICTNODE = new_definition
  `DICTNODE x a b n : A option =
   if n = 0 then x else (if EVEN n then a else b) (n DIV 2)`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the binary representations of numerals.                      *)
(* ------------------------------------------------------------------------- *)

let ARITH_2 = prove
 (`(_0 = 0 <=> T) /\
   (!n. BIT0 n = 0 <=> n = _0) /\
   (!n. ~(BIT1 n = 0)) /\
   (_0 DIV 2 = _0) /\
   (!n. BIT0 n DIV 2 = n) /\
   (!n. BIT1 n DIV 2 = n)`,
  REWRITE_TAC[NUMERAL; BIT0; BIT1] THEN
  ONCE_REWRITE_TAC[GSYM (REWRITE_CONV[NUMERAL] `0`)] THEN ARITH_TAC);;

let NUM_BIT_CASES = prove
 (`!n. (n = _0) \/
       (?m. ~(m = _0) /\ n = BIT0 m) \/
       (?m. n = BIT1 m)`,
  GEN_REWRITE_TAC I [NUM_CASES_BINARY] THEN
  REWRITE_TAC[NUMERAL; BIT0; BIT1] THEN
  ONCE_REWRITE_TAC[GSYM (REWRITE_CONV[NUMERAL] `0`)] THEN
  NUM_REDUCE_TAC THEN
  SUBGOAL_THEN `!n m. ~(2 * n = SUC (m + m))` (fun th -> REWRITE_TAC[th]) THENL
  [REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o AP_TERM `EVEN`) THEN
   REWRITE_TAC[EVEN_DOUBLE; EVEN; EVEN_ADD];
   ALL_TAC] THEN
  SUBGOAL_THEN `!n m. ~(2 * n + 1 = m + m)` (fun th -> REWRITE_TAC[th]) THENL
  [REPEAT GEN_TAC THEN DISCH_THEN (MP_TAC o AP_TERM `EVEN`) THEN
   REWRITE_TAC[EVEN_DOUBLE; EVEN; EVEN_ADD; ONE];
   ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE
    `(2 * n = 0 <=> n = 0) /\
     (2 * n = m + m <=> n = m) /\
     ~(2 * n + 1 = 0) /\
     (2 * n + 1 = SUC (m + m) <=> n = m)`] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)
  
let DICTTRIE_ARITH = prove
 (`DICTTRIE f (NUMERAL n) : A option = f n /\
   DICTEMPTY n : A option = NONE /\
   DICTNODE x a b _0 : A option = x /\
   DICTNODE x a b (BIT0 n) = (if n = _0 then x else a n) /\
   DICTNODE x a b (BIT1 n) = b n`,
  CONJ_TAC THENL [REWRITE_TAC[DICTTRIE; NUMERAL]; REWRITE_TAC[DICTEMPTY]] THEN
  REWRITE_TAC[DICTNODE; ARITH_2; ARITH_EVEN]);;

let DICTMERGE = new_definition
  `DICTMERGE op a b (n : num) : A option = OPTION_MERGE op (a n) (b n)`;;

let OPTION_MERGE_ID = prove
 (`(!op a:A option. OPTION_MERGE op NONE a = a) /\
   (!op a:A option. OPTION_MERGE op a NONE = a)`,
  REPEAT STRIP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `a:A option` (cases "option")) THEN
  REWRITE_TAC[OPTION_MERGE]);;

let DICTMERGE_ARITH = prove
 (`DICTMERGE op (DICTTRIE a) (DICTTRIE b)= DICTTRIE (DICTMERGE op a b) /\
   DICTMERGE op DICTEMPTY a = a : num -> A option /\
   DICTMERGE op a DICTEMPTY = a /\
   DICTMERGE op (DICTNODE x1 a1 b1) (DICTNODE x2 a2 b2) : num -> A option =
   DICTNODE (OPTION_MERGE op x1 x2) (DICTMERGE op a1 a2) (DICTMERGE op b1 b2)`,
  REWRITE_TAC[DICTTRIE] THEN
  REWRITE_TAC[FUN_EQ_THM; DICTMERGE; DICTEMPTY; OPTION_MERGE_ID] THEN
  INTRO_TAC "![n]" THEN STRUCT_CASES_TAC (SPEC `n:num` NUM_BIT_CASES) THEN
  ASM_REWRITE_TAC[DICTTRIE_ARITH; DICTMERGE]);;

let DICT_SING = new_definition
  `!k v:A n:num. DICT_SING k v n = if n = k then SOME v else NONE`;;

let DICT_SING_ARITH = prove
 (`(!k v:A. DICT_SING (NUMERAL k) v = DICT_SING k v) /\
   (!v:A. DICT_SING _0 v = DICTNODE (SOME v) DICTEMPTY DICTEMPTY) /\
   (!k v:A. DICT_SING (BIT0 k) v =
            if k = _0
            then DICTNODE (SOME v) DICTEMPTY DICTEMPTY
            else DICTNODE NONE (DICT_SING k v) DICTEMPTY) /\
   (!k v:A. DICT_SING (BIT1 k) v = DICTNODE NONE DICTEMPTY (DICT_SING k v))`,
  REWRITE_TAC[FUN_EQ_THM; DICT_SING; NUMERAL; DICTNODE] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN ASM_CASES_TAC `x = _0` THEN
   ASM_REWRITE_TAC[NUMERAL] THEN
   COND_CASES_TAC THEN REWRITE_TAC[DICTEMPTY];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   ASM_CASES_TAC `x = _0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `k = _0` THEN
    ASM_REWRITE_TAC[ARITH_ZERO; DICTNODE; NUMERAL; ARITH_EQ];
    ALL_TAC] THEN
   ASM_CASES_TAC `k = _0` THEN ASM_REWRITE_TAC[ARITH_EQ; ARITH_ZERO] THENL
   [REWRITE_TAC[DICTNODE] THEN
    SUBGOAL_THEN `~(x = 0)` (fun th -> REWRITE_TAC[th]) THENL
    [DISCH_THEN SUBST_VAR_TAC THEN ASM_MESON_TAC[NUMERAL]; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[DICTEMPTY];
    ALL_TAC] THEN
   COND_CASES_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC[DICTNODE; NUMERAL; ARITH_EVEN] THEN
    SUBGOAL_THEN `BIT0 k DIV BIT0 (BIT1 _0) = k`
      (fun th -> REWRITE_TAC[th; DICT_SING]) THEN
    MATCH_MP_TAC (REWRITE_RULE[NUMERAL](ARITH_RULE `b * 2 = a ==> a DIV 2 = b`)) THEN
    REWRITE_TAC[BIT0; BIT1] THEN
    ONCE_REWRITE_TAC[GSYM (REWRITE_CONV[NUMERAL] `0`)] THEN
    ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC[DICTNODE] THEN
   SUBGOAL_THEN `~(x = 0)` (fun th -> ASM_REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[NUMERAL]; ALL_TAC] THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC[DICT_SING] THEN
    SUBGOAL_THEN `~(x DIV 2 = k)` (fun th -> REWRITE_TAC[th]) THEN
    POP_ASSUM (MP_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
    POP_ASSUM (LABEL_TAC "x" o REWRITE_RULE[BIT0]) THEN
    INTRO_TAC "@m. m" THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    DISCH_THEN SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[ARITH_RULE `(2 * m) DIV 2 = m`] THEN
    ARITH_TAC;
    REWRITE_TAC[DICTEMPTY]];
   ALL_TAC] THEN

  REPEAT GEN_TAC THEN ASM_CASES_TAC `x = _0` THEN
  ASM_REWRITE_TAC[ARITH_EQ; ARITH_EVEN] THEN
  ASM_CASES_TAC `EVEN x` THEN ASM_REWRITE_TAC[] THENL
  [
   COND_CASES_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[ARITH_EVEN];
    REWRITE_TAC[DICTEMPTY]]
  ;
   COND_CASES_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC[REWRITE_RULE[GSYM BIT1; NUMERAL]
                  (ARITH_RULE `SUC (k + k) DIV 2 = k`); DICT_SING];
    ALL_TAC] THEN
   REWRITE_TAC[DICT_SING] THEN
   SUBGOAL_THEN `~(x DIV BIT0 (BIT1 _0) = k)` (fun th -> REWRITE_TAC[th]) THEN
   FIRST_X_ASSUM (MP_TAC o GEN_REWRITE_RULE I [NOT_EVEN]) THEN
   REWRITE_TAC[ODD_EXISTS] THEN
   INTRO_TAC "@m. m" THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   SUBGOAL_THEN `~(SUC (2 * m) DIV 2 = k)`
     (fun th -> MP_TAC th THEN REWRITE_TAC[NUMERAL]) THEN
   REWRITE_TAC[ARITH_RULE `SUC (2 * m) DIV 2 = m`] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   SUBGOAL_THEN `BIT1 k = SUC (k + k)` SUBST1_TAC THENL
   [REWRITE_TAC[BIT1]; ARITH_TAC]
  ]);;

let DICT_UPDATE = new_definition
  `DICT_UPDATE d k v n = if n = k then SOME v else d n`;;

let DICT_UPDATE_ARITH = prove
 (`(!d k v. DICT_UPDATE (DICTTRIE d) (NUMERAL k) v = DICT_UPDATE d k v) /\
   (!d k v. DICT_UPDATE DICTEMPTY k v = DICT_SING k v) /\
   (!d v. DICT_UPDATE (DICTNODE x a b) _0 v = DICTNODE (SOME v) a b) /\
   (!d k v. DICT_UPDATE (DICTNODE x a b) (BIT0 k) v =
            if k = _0 then DICTNODE (SOME v) a b else
            DICTNODE x (DICT_UPDATE a k v) b) /\
   (!d k v. DICT_UPDATE (DICTNODE x a b) (BIT1 k) v =
            DICTNODE x a (DICT_UPDATE b k v))`,
  CHEAT_TAC);;
