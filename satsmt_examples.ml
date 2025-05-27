(* ========================================================================= *)
(* Construction of examples and problems designed to be solved using         *)
(* SAT/SMT-based methods.                                                    *)
(* ========================================================================= *)

loadt "BinTreeVec/make.ml";;

(* ------------------------------------------------------------------------- *)
(* Conversion for sums of nums and some frequently used instances.           *)
(* ------------------------------------------------------------------------- *)

let NSUM_NUMSEG_CONV : conv =
  let ONCE_NSUM_NUMSEG_CONV : conv =
    (LAND_CONV (RAND_CONV (TRY_CONV num_CONV))) THENC
    GEN_REWRITE_CONV I [NSUM_CLAUSES_NUMSEG] THENC
    NUM_REDUCE_CONV in
  TOP_SWEEP_CONV ONCE_NSUM_NUMSEG_CONV THENC
  REWRITE_CONV[ADD; GSYM ADD_ASSOC];;

let NSUM_5 = NSUM_NUMSEG_CONV `nsum (1..5) f`;;
let NSUM_6 = NSUM_NUMSEG_CONV `nsum (1..6) f`;;
let NSUM_7 = NSUM_NUMSEG_CONV `nsum (1..7) f`;;
let NSUM_8 = NSUM_NUMSEG_CONV `nsum (1..8) f`;;
let NSUM_9 = NSUM_NUMSEG_CONV `nsum (1..9) f`;;
let NSUM_10 = NSUM_NUMSEG_CONV `nsum (1..10) f`;;

(* ------------------------------------------------------------------------- *)
(* Heterogeneous tools.                                                      *)
(* ------------------------------------------------------------------------- *)

let mk_forall_position =
  let position_ty = `:position` in
  fun tm -> let fvars = frees tm in
            let vars = filter ((=) position_ty o type_of) fvars in
            list_mk_forall(vars,tm);;

let CONJ_LIST (thl : thm list) : thm =
  try end_itlist CONJ thl with Failure _ -> failwith "CONJ_LIST";;

let LIST_MP_TAC (thl : thm list) : tactic =
  try MP_TAC (CONJ_LIST thl) with Failure _ -> ALL_TAC;;

let UNDISCH_ALL_TAC : tactic =
  POP_ASSUM_LIST (LIST_MP_TAC o rev);;

let FORALL_ANT_THM = prove
 (`!P. (!x. P x) <=> (!pos:position dir:bool. P (pos,dir))`,
  MATCH_ACCEPT_TAC FORALL_PAIR_THM);;

let EXISTS_ANT_THM = prove
 (`!P. (?x. P x) <=> (?pos:position dir:bool. P (pos,dir))`,
  MATCH_ACCEPT_TAC EXISTS_PAIR_THM);;

(* ------------------------------------------------------------------------- *)
(* System of 2 ants.                                                         *)
(* ------------------------------------------------------------------------- *)

let DELTA_STI_2 =
  let th = INST_TYPE [`:2`,`:N`] DELTA_STI_COMPONENT_ALT in
  let th = REWRITE_RULE[FORALL_VECTOR_THM; FORALL_N_THM;
                        FORALL_LT_BIN; FORALL_LE_BIN;
                        DIMINDEX_CONV `dimindex(:2)`; NSUM_2; PP] th in
  CONV_RULE (ONCE_DEPTH_CONV VECTOR_REDUCE_CONV) th;;

let IN_NEW_SYSTEM_2 =
  let th = INST_TYPE [`:2`,`:N`] IN_NEW_SYSTEM_ALT in
  let th = REWRITE_RULE[FORALL_SYSTEM_THM; FORALL_PAIR_THM; FORALL_VECTOR_THM;
                        ANT; STI; NEW_ANT_ALT; NEW_STI_ALT; DELTA_STI_2;
                        DIMINDEX_CONV `dimindex(:2)`;
                        FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN;
                        CART_EQ; DIMINDEX_3;
                        ARITH_ZERO; VECTOR_ADD_NUM_COMPONENT] th in
  let th = CONV_RULE (ONCE_DEPTH_CONV NUM_SUC_CONV) th in
  let th = CONV_RULE (ONCE_DEPTH_CONV VECTOR_REDUCE_CONV) th in
  let th = REWRITE_RULE[DELTA_STI_2] th in
  REWRITE_RULE[] th;;

(* ------------------------------------------------------------------------- *)
(* System of 3 ants.                                                         *)
(* ------------------------------------------------------------------------- *)

let DELTA_STI_3 =
  let th = INST_TYPE [`:3`,`:N`] DELTA_STI_COMPONENT_ALT in
  let th = REWRITE_RULE[FORALL_VECTOR_THM; FORALL_N_THM;
                        FORALL_LT_BIN; FORALL_LE_BIN;
                        DIMINDEX_CONV `dimindex(:3)`; NSUM_3; PP] th in
  CONV_RULE (ONCE_DEPTH_CONV VECTOR_REDUCE_CONV) th;;

let IN_NEW_SYSTEM_3 =
  let th = INST_TYPE [`:3`,`:N`] IN_NEW_SYSTEM_ALT in
  let th = REWRITE_RULE[FORALL_SYSTEM_THM; FORALL_PAIR_THM; FORALL_VECTOR_THM;
                        ANT; STI; NEW_ANT_ALT; NEW_STI_ALT; DELTA_STI_3;
                        DIMINDEX_CONV `dimindex(:3)`;
                        FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN;
                        CART_EQ; DIMINDEX_3;
                        ARITH_ZERO; VECTOR_ADD_NUM_COMPONENT] th in
  let th = CONV_RULE (ONCE_DEPTH_CONV NUM_SUC_CONV) th in
  let th = CONV_RULE (ONCE_DEPTH_CONV VECTOR_REDUCE_CONV) th in
  let th = REWRITE_RULE[DELTA_STI_3] th in
  REWRITE_RULE[] th;;

(* ------------------------------------------------------------------------- *)
(* System of 5 ants.                                                         *)
(* ------------------------------------------------------------------------- *)

let DELTA_STI_5 =
  let th = INST_TYPE [`:5`,`:N`] DELTA_STI_COMPONENT_ALT in
  let th = REWRITE_RULE[FORALL_VECTOR_THM; FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN;
                        DIMINDEX_CONV `dimindex(:5)`; NSUM_5; PP] th in
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

(* ------------------------------------------------------------------------- *)
(* System of 10 ants.                                                        *)
(* ------------------------------------------------------------------------- *)

let DELTA_STI_10 =
  let th = INST_TYPE [`:10`,`:N`] DELTA_STI_COMPONENT_ALT in
  let th = REWRITE_RULE[FORALL_VECTOR_THM; FORALL_N_THM; FORALL_LT_BIN; FORALL_LE_BIN;
                        DIMINDEX_CONV `dimindex(:10)`; NSUM_10; PP] th in
  let th = CONV_RULE (ONCE_DEPTH_CONV VECTOR_REDUCE_CONV) th in
  th;;

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
(* Proof of the permanence of the invariant of the stigmergy.                *)
(* ------------------------------------------------------------------------- *)

(* Statement for 2 ants (uses the position datatype). *)
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
e (REWRITE_TAC[FORALL_ANT_THM; FORALL_VECTOR_THM; ANT; STI]);;
e (INTRO_TAC "![a0] [d0] [a1] [d1] [s1] [s2] [s3]");;
e (GEN_REWRITE_TAC I [FORALL_SYSTEM_THM]);;
e (REWRITE_TAC[FORALL_ANT_THM; FORALL_VECTOR_THM; ANT; STI]);;
e (INTRO_TAC "![a0'] [d0'] [a1'] [d1'] [s1'] [s2'] [s3']");;
e (GEN_REWRITE_TAC I [FORALL_SYSTEM_THM]);;
e (REWRITE_TAC[FORALL_ANT_THM; FORALL_VECTOR_THM; ANT; STI]);;
e (INTRO_TAC "![a0''] [d0''] [a1''] [d1''] [s1''] [s2''] [s3'']");;
e (GEN_REWRITE_TAC I [FORALL_SYSTEM_THM]);;
e (REWRITE_TAC[FORALL_ANT_THM; FORALL_VECTOR_THM; ANT; STI]);;
e (INTRO_TAC "![a0'''] [d0'''] [a1'''] [d1'''] [s1'''] [s2'''] [s3''']");;
e VECTOR_REDUCE_TAC;;
e UNDISCH_ALL_TAC;;
e (REWRITE_TAC[IN_NEW_SYSTEM_2; MAX; PP]);;
let _,invariant_tm_2 = top_goal();;

(* Statement for 2 ants (do not uses the position datatype). *)
g (mk_forall_position invariant_tm_2);;
e (REWRITE_TAC[FORALL_POSITION_NUM_THM; GSYM PP]);;
e (REWRITE_TAC[MESON []
     `(if a then PP b else PP c) = PP (if a then b else c)`]);;
e (REPEAT STRIP_TAC THEN UNDISCH_ALL_TAC);;
let _,invariant_nopos_tm_2 = top_goal();;

(* Statement for 5 ants (uses the position datatype). *)
g `!sys sys' sys'' sys''':5 system.
      sys' IN NEW_SYSTEM sys /\
      sys'' IN NEW_SYSTEM sys' /\
      sys''' IN NEW_SYSTEM sys'' /\
      INVARIANT_STI (STI sys) /\
      INVARIANT_STI (STI sys') /\
      INVARIANT_STI (STI sys'')
      ==> INVARIANT_STI (STI sys''')`;;
e (REWRITE_TAC[INVARIANT_STI]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; ANT; STI;
               FORALL_ANT_THM; FORALL_VECTOR_THM]);;
e (REPEAT GEN_TAC);;
e VECTOR_REDUCE_TAC;;
e (REWRITE_TAC[IN_NEW_SYSTEM_5; MAX; PP]);;
e (REPEAT STRIP_TAC THEN UNDISCH_ALL_TAC);;
let _,invariant_tm_5 = top_goal();;

(* Statement for 5 ants (do not uses the position datatype). *)
g (mk_forall_position invariant_tm_5);;
e (REWRITE_TAC[FORALL_POSITION_NUM_THM; GSYM PP]);;
e (REWRITE_TAC[MESON []
     `(if a then PP b else PP c) = PP (if a then b else c)`]);;
e (REPEAT STRIP_TAC THEN UNDISCH_ALL_TAC);;
let _,invariant_nopos_tm_5 = top_goal();;

(* Statement for 10 ants (uses the position datatype). *)
g `!sys sys' sys'' sys''':10 system.
      sys' IN NEW_SYSTEM sys /\
      sys'' IN NEW_SYSTEM sys' /\
      sys''' IN NEW_SYSTEM sys'' /\
      INVARIANT_STI (STI sys) /\
      INVARIANT_STI (STI sys') /\
      INVARIANT_STI (STI sys'')
      ==> INVARIANT_STI (STI sys''')`;;
e (REWRITE_TAC[INVARIANT_STI]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; ANT; STI;
               FORALL_ANT_THM; FORALL_VECTOR_THM]);;
e (REPEAT GEN_TAC);;
e VECTOR_REDUCE_TAC;;
e (REWRITE_TAC[IN_NEW_SYSTEM_10; MAX; PP]);;
e (REPEAT STRIP_TAC THEN UNDISCH_ALL_TAC);;
let _,invariant_tm_10 = top_goal();;

(* Statement for 10 ants (do not uses the position datatype). *)
g (mk_forall_position invariant_tm_10);;
e (REWRITE_TAC[FORALL_POSITION_NUM_THM; GSYM PP]);;
e (REWRITE_TAC[MESON []
     `(if a then PP b else PP c) = PP (if a then b else c)`]);;
e (REPEAT STRIP_TAC THEN UNDISCH_ALL_TAC);;
let _,invariant_nopos_tm_10 = top_goal();;

(* ------------------------------------------------------------------------- *)
(* Conterexample to the permanence of the invariant of the stigmergy.        *)
(* ------------------------------------------------------------------------- *)

g `!sys sys' sys'':2 system.
      sys' IN NEW_SYSTEM sys /\
      sys'' IN NEW_SYSTEM sys' /\
      INVARIANT_STI (STI sys) /\
      INVARIANT_STI (STI sys')
      ==> INVARIANT_STI (STI sys'')`;;
e (REWRITE_TAC[INVARIANT_STI]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; ANT; STI;
               FORALL_ANT_THM; FORALL_VECTOR_THM]);;
e (REPEAT GEN_TAC);;
e VECTOR_REDUCE_TAC;;
e (REWRITE_TAC[IN_NEW_SYSTEM_2; MAX; PP]);;
e (REPEAT STRIP_TAC THEN UNDISCH_ALL_TAC);;
let _,counterex_tm_2 = top_goal();;

(* ------------------------------------------------------------------------- *)
(* Examples of simulation of the eveolution of the system.                   *)
(* ------------------------------------------------------------------------- *)

(* let run_conv (conv:conv) (tm:term) : term =
  rhs (concl (conv tm));; *)

let ptm =
  `System (Vx[(a1,d1); (a2,d2)])
          (Vx[s1; s2; s3]) : 2 system
   IN ITER 10 (SETBIND NEW_SYSTEM)
                {System (Vx[(P0,T); (P1,F)])
                        (Vx[0; 0; 0]) : 2 system}` in
let vars = frees ptm in
let goal = list_mk_exists(vars,ptm) in
g goal;;
e (CONV_TAC (TOP_SWEEP_CONV num_CONV));;
e (REWRITE_TAC[ITER; IN_SETBIND; IN_INSERT; NOT_IN_EMPTY]);;
e (CONV_TAC (TOP_DEPTH_CONV UNWIND_CONV));;
e (REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC]);;
e (REWRITE_TAC[EXISTS_SYSTEM_THM; EXISTS_VECTOR_THM; EXISTS_ANT_THM]);;
e (REPEAT META_EXISTS_TAC);;
e (REWRITE_TAC[IN_NEW_SYSTEM_2; PP; GSYM CONJ_ASSOC]);;
let (_,simul_tm_2) = top_goal();;
(* let tml = striplist dest_conj simul_tm_2;;
filter (not o can sexp_of_term) tml;;

sexp_of_term simul_tm_2;; *)

let ptm =
  `System (Vx[(a0,d0); (a1,d1); (a2,d2); (a3,d3); (a4,d4)])
          (Vx[s1; s2; s3]) : 5 system
   IN ITER 5 (SETBIND NEW_SYSTEM)
                {System (Vx[(P0,T); (P0,T); (P0,T); (P0,T); (P0,T)])
                        (Vx[0; 0; 0]) : 5 system}` in
let vars = frees ptm in
let goal = list_mk_exists(vars,ptm) in
g goal;;
e (CONV_TAC (TOP_SWEEP_CONV num_CONV));;
e (REWRITE_TAC[ITER; IN_SETBIND; IN_INSERT; NOT_IN_EMPTY]);;
e (CONV_TAC (TOP_DEPTH_CONV UNWIND_CONV));;
e (REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC]);;
e (REWRITE_TAC[EXISTS_SYSTEM_THM; EXISTS_VECTOR_THM; EXISTS_ANT_THM]);;
e (REPEAT META_EXISTS_TAC);;
e (REWRITE_TAC[IN_NEW_SYSTEM_5; PP; GSYM CONJ_ASSOC]);;
let (_,simul_tm_5) = top_goal();;

let ptm =
  `System (Vx[(a0,d0); (a1,d1); (a2,d2); (a3,d3); (a4,d4);
              (a5,d5); (a6,d6); (a7,d7); (a8,d8); (a9,d9)])
          (Vx[s1; s2; s3]) : 10 system
   IN ITER 5 (SETBIND NEW_SYSTEM)
                {System (Vx[(P0,T); (P0,T); (P0,T); (P0,T); (P0,T);
                            (P0,T); (P0,T); (P0,T); (P0,T); (P0,T)])
                        (Vx[0; 0; 0]) : 10 system}` in
let vars = frees ptm in
let goal = list_mk_exists(vars,ptm) in
g goal;;
e (CONV_TAC (TOP_SWEEP_CONV num_CONV));;
e (REWRITE_TAC[ITER; IN_SETBIND; IN_INSERT; NOT_IN_EMPTY]);;
e (CONV_TAC (TOP_DEPTH_CONV UNWIND_CONV));;
e (REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC]);;
e (REWRITE_TAC[EXISTS_SYSTEM_THM; EXISTS_VECTOR_THM; EXISTS_ANT_THM]);;
e (REPEAT META_EXISTS_TAC);;
e (REWRITE_TAC[IN_NEW_SYSTEM_10; PP; GSYM CONJ_ASSOC]);;
let (_,simul_tm_10) = top_goal();;

(* ------------------------------------------------------------------------- *)
(* Reachability.                                                             *)
(* ------------------------------------------------------------------------- *)

let ptm =
  `System (Vx[(PP a0,d0); (PP a1,d1); (PP a2,d2); (PP a3,d3); (PP a4,d4)])
          (Vx[s1; s2; s3]) : 5 system
   IN ITER 5 (SETBIND NEW_SYSTEM)
                {System (Vx[(P0,T); (P0,T); (P0,T); (P0,T); (P0,T)])
                        (Vx[0; 0; 0]) : 5 system} /\
   2 <= s1 /\
   s2 + 3 <= s3` in
let vars = frees ptm in
let goal = list_mk_exists(vars,ptm) in
g goal;;
e (CONV_TAC (TOP_SWEEP_CONV num_CONV));;
e (REWRITE_TAC[ITER; IN_SETBIND; IN_INSERT; NOT_IN_EMPTY]);;
e (CONV_TAC (TOP_DEPTH_CONV UNWIND_CONV));;
e (REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC]);;
e (REWRITE_TAC[EXISTS_SYSTEM_THM; EXISTS_VECTOR_THM; EXISTS_ANT_THM]);;
e (REPEAT META_EXISTS_TAC);;
e (REWRITE_TAC[IN_NEW_SYSTEM_10; PP; GSYM CONJ_ASSOC]);;
let (_,reach_5) = top_goal();;
