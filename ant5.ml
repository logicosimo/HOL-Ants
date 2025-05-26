(* ========================================================================= *)
(* Example with 5 ants which uses bintreevects.                              *)
(* ========================================================================= *)

let FORALL_LE_BIN = prove
 (`(!n. (!i. i < NUMERAL n ==> P i) <=> (!i. i < n ==> P (NUMERAL i))) /\
   ((!i. i <= _0 ==> P i) <=> P _0) /\
   ((!i. i <= BIT0 n ==> P i) <=>
    (!i. i <= n ==> P (BIT0 i)) /\ (!i. i < n ==> P (BIT1 i))) /\
   ((!i. i <= BIT1 n ==> P i) <=>
    (!i. i <= n ==> P (BIT0 i)) /\ (!i. i <= n ==> P (BIT1 i)))`,
  CONJ_TAC THENL [REWRITE_TAC[NUMERAL]; ALL_TAC] THEN
  CONV_TAC (ONCE_DEPTH_CONV BITS_ELIM_CONV) THEN
  REWRITE_TAC[FORALL_LE_BINARY]);;

let FORALL_LT_BIN = prove
 (`(!n. (!i. i < NUMERAL n ==> P i) <=> (!i. i < n ==> P (NUMERAL i))) /\
   (!i. i < _0 ==> P i) /\
   (!n. (!i. i < BIT0 n ==> P i) <=>
        (!i. i < n ==> P (BIT0 i)) /\ (!i. i < n ==> P (BIT1 i))) /\
   (!n. (!i. i < BIT1 n ==> P i) <=>
        (!i. i <= n ==> P (BIT0 i)) /\ (!i. i < n ==> P (BIT1 i)))`,
  CONJ_TAC THENL [REWRITE_TAC[NUMERAL]; ALL_TAC] THEN
  CONV_TAC (ONCE_DEPTH_CONV BITS_ELIM_CONV) THEN
  REWRITE_TAC[FORALL_LT_BINARY]);;

let FORALL_N_THM = prove
 (`!P. (!i. 1 <= i /\ i <= n ==> P i) <=> (!i. i < n ==> P (SUC i))`,
  GEN_TAC THEN EQ_TAC THENL
  [MESON_TAC[ARITH_RULE `!n i. 1 <= SUC i /\ SUC i <= n <=> i < n`];
   MESON_TAC[ARITH_RULE `1 <= i /\ i <= n
                         ==> SUC (PRE i) = i /\ PRE i < n`]]);;

(* ------------------------------------------------------------------------- *)

let ONCE_NSUM_NUMSEG_CONV : conv =
  (LAND_CONV (RAND_CONV (TRY_CONV num_CONV))) THENC
  GEN_REWRITE_CONV I [NSUM_CLAUSES_NUMSEG] THENC
  NUM_REDUCE_CONV;;

let NSUM_NUMSEG_CONV : conv =
  TOP_SWEEP_CONV ONCE_NSUM_NUMSEG_CONV THENC
  REWRITE_CONV[ADD; GSYM ADD_ASSOC];;

let NSUM_5 = NSUM_NUMSEG_CONV `nsum (1..5) f`;;

let NSUM_10 = NSUM_NUMSEG_CONV `nsum (1..10) f`;;

(*
let NSUM_NUMSEG_BINARY = prove
 (`(!m n f. nsum (NUMERAL m..NUMERAL n) f = nsum (m..n) (\i. f (NUMERAL i))) /\
   (!f. nsum (_0.. _0) f = f _0) /\
   (!f n. nsum (_0..BIT0 n) f = nsum (_0..n) (\i. f (BIT0 i)) +
                                if n = 0 then _0 else
                                nsum (_0..PRE n) (\i. f (BIT0 i)))`,

  CONJ_TAC THENL [REWRITE_TAC[NUMERAL; NTRIE]; ALL_TAC]
*)

(* ------------------------------------------------------------------------- *)

let DELTA_STI_2 =
  let th = INST_TYPE [`:2`,`:N`] DELTA_STI_COMPONENT_ALT in
  let th = REWRITE_RULE[FORALL_VECTOR_THM; FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN;
                        DIMINDEX_CONV `dimindex(:2)`; NSUM_2; PP] th in
  let th = CONV_RULE (ONCE_DEPTH_CONV VECTOR_REDUCE_CONV) th in
  th;;

let DELTA_STI_5 =
  let th = INST_TYPE [`:5`,`:N`] DELTA_STI_COMPONENT_ALT in
  let th = REWRITE_RULE[FORALL_VECTOR_THM; FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN;
                        DIMINDEX_CONV `dimindex(:5)`; NSUM_5; PP] th in
  let th = CONV_RULE (ONCE_DEPTH_CONV VECTOR_REDUCE_CONV) th in
  th;;

let DELTA_STI_10 =
  let th = INST_TYPE [`:10`,`:N`] DELTA_STI_COMPONENT_ALT in
  let th = REWRITE_RULE[FORALL_VECTOR_THM; FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN;
                        DIMINDEX_CONV `dimindex(:10)`; NSUM_10; PP] th in
  let th = CONV_RULE (ONCE_DEPTH_CONV VECTOR_REDUCE_CONV) th in
  th;;

let IN_NEW_SYSTEM_5 =
  let th = INST_TYPE [`:5`,`:N`] IN_NEW_SYSTEM_ALT in
  let th = REWRITE_RULE[FORALL_SYSTEM_THM; FORALL_PAIR_THM; FORALL_VECTOR_THM;
                        ANT; STI; NEW_ANT_ALT; NEW_STI_ALT; DELTA_STI_5;
                        DIMINDEX_CONV `dimindex(:5)`;
                        FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN;
                        CART_EQ; DIMINDEX_3;
                        ARITH_ZERO; VECTOR_ADD_NUM_COMPONENT] th in
  let th = CONV_RULE (ONCE_DEPTH_CONV NUM_SUC_CONV) th in
  let th = CONV_RULE (ONCE_DEPTH_CONV VECTOR_REDUCE_CONV) th in
  let th = REWRITE_RULE[DELTA_STI_5] th in
  REWRITE_RULE[] th;;

let IN_NEW_SYSTEM_10 =
  let th = INST_TYPE [`:10`,`:N`] IN_NEW_SYSTEM_ALT in
  let th = REWRITE_RULE[FORALL_SYSTEM_THM; FORALL_PAIR_THM; FORALL_VECTOR_THM;
                        ANT; STI; NEW_ANT_ALT; NEW_STI_ALT; DELTA_STI_10;
                        DIMINDEX_CONV `dimindex(:10)`;
                        FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN;
                        CART_EQ; DIMINDEX_3;
                        ARITH_ZERO; VECTOR_ADD_NUM_COMPONENT] th in
  let th = CONV_RULE (ONCE_DEPTH_CONV NUM_SUC_CONV) th in
  let th = CONV_RULE (ONCE_DEPTH_CONV VECTOR_REDUCE_CONV) th in
  let th = REWRITE_RULE[DELTA_STI_10] th in
  REWRITE_RULE[] th;;

(* ------------------------------------------------------------------------- *)
(* Invariant.                                                                *)
(* ------------------------------------------------------------------------- *)

(* Per 2 formiche. *)
g `!sys sys' sys'' sys''':2 system.
      sys' IN NEW_SYSTEM sys /\
      sys'' IN NEW_SYSTEM sys' /\
      sys''' IN NEW_SYSTEM sys'' /\
      INVARIANT_STI (STI sys) /\
      INVARIANT_STI (STI sys') /\
      INVARIANT_STI (STI sys'')
      ==> INVARIANT_STI (STI sys''')`;;
e (REWRITE_TAC[INVARIANT_STI]);;
e (GEN_REWRITE_TAC I [FORALL_SYSTEM_THM]);;
e (REWRITE_TAC[FORALL_PAIR_THM; FORALL_VECTOR_THM; ANT; STI; FORALL_POSITION_NUM_THM]);;
e (INTRO_TAC "![a0]; a0; ![d0] [a1]; a1; ![d1] [s1] [s2] [s3]");;
e (GEN_REWRITE_TAC I [FORALL_SYSTEM_THM]);;
e (REWRITE_TAC[FORALL_PAIR_THM; FORALL_VECTOR_THM; ANT; STI; FORALL_POSITION_NUM_THM]);;
e (INTRO_TAC "![a0']; a0'; ![d0'] [a1']; a1'; ![d1'] [s1'] [s2'] [s3']");;
e (GEN_REWRITE_TAC I [FORALL_SYSTEM_THM]);;
e (REWRITE_TAC[FORALL_PAIR_THM; FORALL_VECTOR_THM; ANT; STI; FORALL_POSITION_NUM_THM]);;
e (INTRO_TAC "![a0'']; a0''; ![d0''] [a1'']; a1''; ![d1''] [s1''] [s2''] [s3'']");;
e (GEN_REWRITE_TAC I [FORALL_SYSTEM_THM]);;
e (REWRITE_TAC[FORALL_PAIR_THM; FORALL_VECTOR_THM; ANT; STI; FORALL_POSITION_NUM_THM]);;
e (INTRO_TAC "![a0''']; a'''; ![d0'''] [a1''']; a1'''; ![d1'''] [s1'''] [s2'''] [s3''']");;
e VECTOR_REDUCE_TAC;;
e (REWRITE_TAC[IN_NEW_SYSTEM_2; MAX; GSYM PP;
    MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`]);;
e (POP_ASSUM_LIST (MP_TAC o end_itlist CONJ));;
let _,ptm = top_goal();;

(* Per 5 formiche. *)
g `!sys sys' sys'' sys''':5 system.
      sys' IN NEW_SYSTEM sys /\
      sys'' IN NEW_SYSTEM sys' /\
      sys''' IN NEW_SYSTEM sys'' /\
      INVARIANT_STI (STI sys) /\
      INVARIANT_STI (STI sys') /\
      INVARIANT_STI (STI sys'')
      ==> INVARIANT_STI (STI sys''')`;;
e (REWRITE_TAC[INVARIANT_STI]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_PAIR_THM; FORALL_VECTOR_THM; ANT; STI; FORALL_POSITION_NUM_THM]);;
e (REPEAT (GEN_TAC ORELSE DISCH_TAC));;
e (POP_ASSUM MP_TAC);;
e VECTOR_REDUCE_TAC;;
e (REWRITE_TAC[IN_NEW_SYSTEM_5; MAX; GSYM PP;
    MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`]);;
e (POP_ASSUM_LIST (MP_TAC o end_itlist CONJ));;
let _,ptm = top_goal();;


(* Per 10 formiche. *)
g `!sys sys' sys'' sys''':10 system.
      sys' IN NEW_SYSTEM sys /\
      sys'' IN NEW_SYSTEM sys' /\
      sys''' IN NEW_SYSTEM sys'' /\
      INVARIANT_STI (STI sys) /\
      INVARIANT_STI (STI sys') /\
      INVARIANT_STI (STI sys'')
      ==> INVARIANT_STI (STI sys''')`;;
e (REWRITE_TAC[INVARIANT_STI]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_PAIR_THM; FORALL_VECTOR_THM; ANT; STI; FORALL_POSITION_NUM_THM]);;
e (REPEAT (GEN_TAC ORELSE DISCH_TAC));;
e (POP_ASSUM MP_TAC);;
e VECTOR_REDUCE_TAC;;
e (REWRITE_TAC[IN_NEW_SYSTEM_10; MAX; GSYM PP;
    MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`]);;
e (POP_ASSUM_LIST (MP_TAC o end_itlist CONJ));;
let _,ptm = top_goal();;

(* ------------------------------------------------------------------------- *)
(* Contresempio.                                                             *)
(* ------------------------------------------------------------------------- *)

g `!sys sys' sys'':2 system.
      sys' IN NEW_SYSTEM sys /\
      sys'' IN NEW_SYSTEM sys' /\
      INVARIANT_STI (STI sys) /\
      INVARIANT_STI (STI sys')
      ==> INVARIANT_STI (STI sys'')`;;
e (REWRITE_TAC[INVARIANT_STI]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_PAIR_THM; FORALL_VECTOR_THM; ANT; STI; FORALL_POSITION_NUM_THM]);;
e (REPEAT (GEN_TAC ORELSE DISCH_TAC));;
e (POP_ASSUM MP_TAC);;
e VECTOR_REDUCE_TAC;;
e (REWRITE_TAC[IN_NEW_SYSTEM_2; MAX; GSYM PP;
    MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`]);;
e (POP_ASSUM_LIST (MP_TAC o end_itlist CONJ));;
let _,ptm = top_goal();;

(* ------------------------------------------------------------------------- *)
(* Simulazione.                                                              *)
(* ------------------------------------------------------------------------- *)

let ptm =
`System (Vx[(PP a1,d1); (PP a2,d2)])
        (Vx[s1; s2; s3]) : 2 system
 IN ITER 10 (SETBIND NEW_SYSTEM)
              {System (Vx[(P0,T); (P1,F)])
                      (Vx[0; 0; 0]) : 2 system}`
|> TOP_SWEEP_CONV num_CONV THENC
   REWRITE_CONV[ITER; IN_SETBIND; IN_INSERT; NOT_IN_EMPTY] THENC
   TOP_DEPTH_CONV UNWIND_CONV THENC
   REWRITE_CONV[EXISTS_SYSTEM_THM; EXISTS_VECTOR_THM; LEFT_AND_EXISTS_THM];;

let ptm =
`System (Vx[(PP a1,d1); (PP a2,d2)])
        (Vx[s1; s2; s3]) : 2 system
 IN ITER 10 (SETBIND NEW_SYSTEM)
              {System (Vx[(P0,T); (P1,F)])
                      (Vx[0; 0; 0]) : 2 system}`
|> TOP_SWEEP_CONV num_CONV THENC
   REWRITE_CONV[ITER; IN_SETBIND; IN_INSERT; NOT_IN_EMPTY] THENC
   TOP_DEPTH_CONV UNWIND_CONV THENC
   REWRITE_CONV[EXISTS_SYSTEM_THM; EXISTS_VECTOR_THM;
                EXISTS_POSITION_NUM_THM;
                EXISTS_PAIR_THM; IN_NEW_SYSTEM_2; GSYM PP;
                GSYM RIGHT_EXISTS_AND_THM; LEFT_AND_EXISTS_THM;
    MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`]
|> concl |> rand;;

;;

let ptm =
`System (Vx[(PP a0,d0); (PP a1,d1); (PP a2,d2); (PP a3,d3); (PP a4,d4);
            (PP a5,d5); (PP a6,d6); (PP a7,d7); (PP a8,d8); (PP a9,d9)])
        (Vx[s1; s2; s3]) : 10 system
 IN ITER 5 (SETBIND NEW_SYSTEM)
              {System (Vx[(P0,T); (P0,T); (P0,T); (P0,T); (P0,T);
                          (P0,T); (P0,T); (P0,T); (P0,T); (P0,T)])
                      (Vx[0; 0; 0]) : 10 system}`
|> TOP_SWEEP_CONV num_CONV THENC
   REWRITE_CONV[ITER; IN_SETBIND; IN_INSERT; NOT_IN_EMPTY] THENC
   TOP_DEPTH_CONV UNWIND_CONV THENC
   REWRITE_CONV[LEFT_AND_EXISTS_THM] THENC
   REWRITE_CONV[EXISTS_SYSTEM_THM; EXISTS_VECTOR_THM;
                EXISTS_POSITION_NUM_THM;
                EXISTS_PAIR_THM; IN_NEW_SYSTEM_10; GSYM PP;
    MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`]
  (* GEN_REWRITE_CONV TOP_SWEEP_CONV [GSYM RIGHT_EXISTS_AND_THM] *)
|> concl |> rand;;

let ptm5 = ptm |>
TOP_SWEEP_CONV (GEN_REWRITE_CONV I [GSYM RIGHT_EXISTS_AND_THM] THENC
                ONCE_REWRITE_CONV[CONJ_ASSOC])
|> concl |> rand;;

let ptm = ptm |> strip_exists |> snd;;

(* ------------------------------------------------------------------------- *)
(* Reachability.                                                             *)
(* ------------------------------------------------------------------------- *)

let ptm =
`(System (Vx[(PP a0,d0); (PP a1,d1); (PP a2,d2); (PP a3,d3); (PP a4,d4)])
        (Vx[s1; s2; s3]) : 5 system
 IN ITER 5 (SETBIND NEW_SYSTEM)
              {System (Vx[(P0,T); (P0,T); (P0,T); (P0,T); (P0,T)])
                      (Vx[0; 0; 0]) : 5 system}) /\
 2 <= s1 /\
 s2 + 3 <= s3`
|> TOP_SWEEP_CONV num_CONV THENC
   REWRITE_CONV[ITER; IN_SETBIND; IN_INSERT; NOT_IN_EMPTY] THENC
   TOP_DEPTH_CONV UNWIND_CONV THENC
   REWRITE_CONV[LEFT_AND_EXISTS_THM] THENC
   REWRITE_CONV[EXISTS_SYSTEM_THM; EXISTS_VECTOR_THM;
                EXISTS_POSITION_NUM_THM;
                EXISTS_PAIR_THM; IN_NEW_SYSTEM_5; GSYM PP;
    MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`] THENC
    NUM_REDUCE_CONV
  (* GEN_REWRITE_CONV TOP_SWEEP_CONV [GSYM RIGHT_EXISTS_AND_THM] *)
|> concl |> rand;;

let ptm = ptm |>
TOP_SWEEP_CONV (GEN_REWRITE_CONV I [GSYM RIGHT_EXISTS_AND_THM] THENC
                ONCE_REWRITE_CONV[CONJ_ASSOC])
|> concl |> rand;;

let ptm = ptm |> strip_exists |> snd;;

(* ------------------------------------------------------------------------- *)
(* Serializzazione.                                                          *)
(* ------------------------------------------------------------------------- *)

let ptm = mk_neg ptm;;

frees ptm |> map dest_var;;

let () =
  let vars = sort (<) (frees ptm) in
  let decl_sexps = map sexp_mk_declare_const vars in
  let bound_sexps = mapfilter sexp_mk_assert_nonneg vars in
  let assert_sexp = sexp_mk_fn "assert" [sexp_of_term ptm] in
  let check_sexp = sexp_mk_fn "check-sat" [] in
  let get_sexps = sexp_mk_get_value (map name_of vars) in
  let sexps = decl_sexps @
              bound_sexps @
              [assert_sexp; check_sexp] @ get_sexps in
  let path = "/workspaces/hol-light-devcontainer/code/HOL-Ants" in
  let fname = "sim1.smt2" in
  let pathname = path^"/"^fname in
  write_sexps_to_file pathname sexps;;

(* ========================================================================= *)
(* ========================================================================= *)
(* ========================================================================= *)
(* ========================================================================= *)
(* ========================================================================= *)
(* ========================================================================= *)











g `!sys sys':2 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (GEN_REWRITE_TAC I [FORALL_SYSTEM_THM]);;
e (REWRITE_TAC[FORALL_PAIR_THM; FORALL_VECTOR_THM; ANT; STI]);;
e (INTRO_TAC "![a0] [d0] [a1] [d1] [s1] [s2] [s3]");;
e (GEN_REWRITE_TAC I [FORALL_SYSTEM_THM]);;
e (REWRITE_TAC[FORALL_PAIR_THM; FORALL_VECTOR_THM; ANT; STI]);;
e (INTRO_TAC "![a0'] [d0'] [a1'] [d1'] [s1'] [s2'] [s3']");;
e VECTOR_REDUCE_TAC;;
e DISCH_TAC;;

e (REWRITE_TAC[LEFT_AND_FORALL_THM; LEFT_IMP_FORALL_THM]);;


e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_PAIR_THM; FORALL_VECTOR_THM; ANT; STI]);;
e (REPEAT GEN_TAC);;
e (REWRITE_TAC[IN_NEW_SYSTEM_2; MAX]);;
e VECTOR_REDUCE_TAC;;
e (REWRITE_TAC[LEFT_IMP_FORALL_THM]);;
let _,tm = top_goal();;

let tm = mk_neg tm in
let th = REWRITE_CONV[NOT_FORALL_THM; NOT_EXISTS_THM;
                      NOT_IMP; DE_MORGAN_THM;
                      LEFT_IMP_FORALL_THM] tm in
rhs(concl th);;

e (REWRITE_TAC[LEFT_IMP_FORALL_THM]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_PAIR_THM; FORALL_VECTOR_THM; ANT; STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_2]);;
e VECTOR_REDUCE_TAC;;


g `!sys sys':5 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI;
               FORALL_SYSTEM_THM; FORALL_VECTOR_THM;
               IN_NEW_SYSTEM_ALT; STI; ANT;
               NEW_ANT_ALT; NEW_STI_ALT; ANT; STI; DELTA_STI_COMPONENT_ALT;
               DIMINDEX_CONV `dimindex(:5)`; DIMINDEX_CONV `dimindex(:3)`;
               CART_EQ; FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN; ARITH_ZERO;
               VECTOR_ADD_NUM_COMPONENT;
               FORALL_PAIR_THM; PAIR_EQ]);;
e (NUM_REDUCE_TAC THEN VECTOR_REDUCE_TAC);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; PP]);;
e (REWRITE_TAC[DIMINDEX_CONV `dimindex(:5)`; NSUM_5]);;
e VECTOR_REDUCE_TAC;;
e (REWRITE_TAC[MAX]);;
e (REWRITE_TAC[FORALL_POSITION_NUM_THM; EXISTS_POSITION_NUM_THM; GSYM PP;
               MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`;
               RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC;
               LEFT_AND_FORALL_THM; RIGHT_AND_FORALL_THM]);;
(* e (CONV_TAC (NNFC_CONV THENC PRENEX_CONV));; *)
(* e (REWRITE_TAC[RIGHT_AND_FORALL_THM]);; *)
(* e (REFUTE_THEN MP_TAC);;
e (PURE_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; DE_MORGAN_THM]);;
e (REWRITE_TAC[]);; *)
let _,ptm = top_goal();;

let ptm = mk_neg (snd (strip_forall ptm));;

g `!sys sys':2 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI;
               FORALL_SYSTEM_THM; FORALL_VECTOR_THM;
               IN_NEW_SYSTEM_ALT; STI; ANT;
               NEW_ANT_ALT; NEW_STI_ALT; ANT; STI; DELTA_STI_COMPONENT_ALT;
               DIMINDEX_CONV `dimindex(:2)`; DIMINDEX_CONV `dimindex(:3)`;
               CART_EQ; FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN; ARITH_ZERO;
               VECTOR_ADD_NUM_COMPONENT;
               FORALL_PAIR_THM; PAIR_EQ]);;
e (NUM_REDUCE_TAC THEN VECTOR_REDUCE_TAC);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; PP]);;
e (REWRITE_TAC[DIMINDEX_CONV `dimindex(:2)`; NSUM_2]);;
e VECTOR_REDUCE_TAC;;
e (REWRITE_TAC[MAX]);;
e (REWRITE_TAC[FORALL_POSITION_NUM_THM; EXISTS_POSITION_NUM_THM; GSYM PP;
               MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`;
               RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC;
               LEFT_AND_FORALL_THM; RIGHT_AND_FORALL_THM;
               NOT_EXISTS_THM; NOT_IMP]);;
e (REWRITE_TAC[MESON[] `((!x. P x) ==> Q) <=> (?x. ~P x \/ Q)`]);;
(*  e (CONV_TAC (NNF_CONV THENC DNF_CONV THENC PRENEX_CONV));;

search[`((!x. P x) ==> Q) <=> r`];;
e (CONV_TAC (NNFC_CONV THENC PRENEX_CONV));; *)
(* e (REWRITE_TAC[RIGHT_AND_FORALL_THM]);; *)
(* e (REFUTE_THEN MP_TAC);;
e (PURE_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; DE_MORGAN_THM]);;
e (REWRITE_TAC[]);; *)
let _,ptm = top_goal();;

let ptm = ptm |> (NNF_CONV THENC DNF_CONV THENC PRENEX_CONV) |> concl |> rhs;;


let ptm = mk_neg (snd (strip_forall ptm));;
let ptm =
  ptm |> REWRITE_CONV[NOT_FORALL_THM; NOT_EXISTS_THM; NOT_IMP; DE_MORGAN_THM]
      |> concl |> rhs;;
let ptm = ptm |> PRENEX_CONV |> concl |> rhs;;
let ptm = ptm |> strip_exists |> snd;;



`!p1 p2 p1' p2' a a' c p1'' p2'' p1''' p2''' a'' a''' c' p1'''' p2'''' p1''''' p2''''' a'''' a''''' c'' p1'''''' p2'''''' p1''''''' p2''''''' a'''''' a''''''' c'''.
     (FORALL)
     ==> a'' > (if a''' <= c' then c' else a''') /\
         a'''' > (if a''''' <= c'' then c'' else a''''') /\
         a'''''' > (if a''''''' <= c''' then c''' else a''''''')`