(* ========================================================================= *)
(* COMPUTE_CONV, a conversion for call-by-value evaluation.                  *)
(* Copyright (c) 2014-2016 Marco Maggesi                                     *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The core of this file is the conversional COMPUTE_DEPTH_CONV, similar     *)
(* to the one given in the Tutorial but with some improvements:              *)
(*  - Does not compute inside an abstraction.                                *)
(*  - Handles match-with (however does not handle "function".                *)
(*  - Handles let-in.                                                        *)
(*  - Uses a failure-propagating style to avoid rebuilding of terms (i.e.,   *)
(*    unnecessary application of TRANS).                                     *)
(* ------------------------------------------------------------------------- *)

(* needs "Snippets/conv.hl";; *)

(* let debug_conv (conv:conv) : conv = fun tm ->
  pp_print_string std_formatter "DEBUG: ";
  pp_print_term std_formatter tm;
  conv tm;;

let debug_conv (conv:conv) : conv = fun tm -> conv tm;; *)

let COMPUTE_DEPTH_CONV (conv:conv) : conv =
  let is_match = function
      Comb(Comb(Const("_MATCH",_),_),_) -> true
    | _ -> false in
  let COMB_QCONV (conv:conv) : conv =
    fun tm ->
      match tm with
        Comb(l,r) ->
          (try let th1 = conv l in
               try let th2 = conv r in MK_COMB(th1,th2)
               with Failure _ -> AP_THM th1 r
           with Failure _ -> AP_TERM l (conv r))
      | _ -> failwith "COMB_QCONV: Not a combination" in
  let THENQC conv1 conv2 tm =
    try let th1 = conv1 tm in
        try let th2 = conv2(rand(concl th1)) in TRANS th1 th2
        with Failure _ -> th1
    with Failure _ -> conv2 tm in
  let THENCQC (conv1:conv) (conv2:conv) : conv =
    fun tm -> let th1 = conv1 tm in
              try let th2 = conv2(rand(concl th1)) in TRANS th1 th2
              with Failure _ -> th1 in
  let rec RUNC tm =
    if is_gabs tm then
      fail ()
    else if is_cond tm then
      THENQC (RATOR_CONV (LAND_CONV RUNC)) (THENCQC COND_CONV RUNC) tm
    else if is_conj tm then
      THENQC (LAND_CONV RUNC) (THENCQC CONJ_CONV RUNC) tm
    else if is_disj tm then
      THENQC (LAND_CONV RUNC) (THENCQC DISJ_CONV RUNC) tm
    else if is_let tm then
      THENQC (debug_conv (SUBLET_CONV RUNC)) (THENCQC let_CONV RUNC) tm
    else if is_match tm then
      THENQC (LAND_CONV RUNC) (THENCQC MATCH_CONV RUNC) tm
    else if is_comb tm then
      THENQC (COMB_QCONV RUNC) (THENCQC (GEN_BETA_CONV ORELSEC conv) RUNC) tm
    else
      THENCQC conv RUNC tm in
  TRY_CONV RUNC;;

(* ------------------------------------------------------------------------- *)
(* Store of rewrites and conversions for COMPUTE_CONV.                       *)
(* ------------------------------------------------------------------------- *)

let set_compute_rewrites,extend_compute_rewrites,compute_rewrites,
    set_compute_convs,extend_compute_convs,compute_convs,compute_net =
  let rewrites = ref ([]:thm list)
  and conversions = ref ([]:(string*(term*conv))list)
  and conv_net = ref (empty_net: gconv net) in
  let rehash_convnet() =
    conv_net := itlist (net_of_thm true) (!rewrites)
        (itlist (fun (_,(pat,cnv)) -> net_of_conv pat cnv) (!conversions)
                empty_net) in
  let set_compute_rewrites thl =
    let canon_thl = itlist (mk_rewrites false) thl [] in
    (rewrites := canon_thl; rehash_convnet())
  and extend_compute_rewrites thl =
    let canon_thl = itlist (mk_rewrites false) thl [] in
    (rewrites := canon_thl @ !rewrites; rehash_convnet())
  and compute_rewrites() = !rewrites
  and set_compute_convs cnvs =
    (conversions := cnvs; rehash_convnet())
  and extend_compute_convs (name,patcong) =
    (conversions :=
      (name,patcong)::filter(fun (name',_) -> name <> name') (!conversions);
     rehash_convnet())
  and compute_convs() = !conversions
  and compute_net() = !conv_net in
  set_compute_rewrites,extend_compute_rewrites,compute_rewrites,
  set_compute_convs,extend_compute_convs,compute_convs,compute_net;;

let COMPUTE_CONV : thm list -> conv =
  let COMPUTE_REWRITE_CONV thl =
    GENERAL_REWRITE_CONV false I (compute_net()) thl in
  fun thl -> COMPUTE_DEPTH_CONV (COMPUTE_REWRITE_CONV thl);;

(* ------------------------------------------------------------------------- *)
(* Default net for COMPUTE_CONV.                                             *)
(* ------------------------------------------------------------------------- *)

set_compute_convs
  ["NUM_SUC_CONV",(`SUC(NUMERAL n)`,NUM_SUC_CONV);
   "NUM_PRE_CONV",(`PRE(NUMERAL n)`,NUM_PRE_CONV);
   "NUM_FACT_CONV",(`FACT(NUMERAL n)`,NUM_FACT_CONV);
   "NUM_LT_CONV",(`NUMERAL m < NUMERAL n`,NUM_LT_CONV);
   "NUM_LE_CONV",(`NUMERAL m <= NUMERAL n`,NUM_LE_CONV);
   "NUM_GT_CONV",(`NUMERAL m > NUMERAL n`,NUM_GT_CONV);
   "NUM_GE_CONV",(`NUMERAL m >= NUMERAL n`,NUM_GE_CONV);
   "NUM_EQ_CONV",(`NUMERAL m = NUMERAL n`,NUM_EQ_CONV);
   "NUM_EVEN_CONV",(`EVEN(NUMERAL n)`,NUM_EVEN_CONV);
   "NUM_ODD_CONV",(`ODD(NUMERAL n)`,NUM_ODD_CONV);
   "NUM_ADD_CONV",(`NUMERAL m + NUMERAL n`,NUM_ADD_CONV);
   "NUM_SUB_CONV",(`NUMERAL m - NUMERAL n`,NUM_SUB_CONV);
   "NUM_MULT_CONV",(`NUMERAL m * NUMERAL n`,NUM_MULT_CONV);
   "NUM_EXP_CONV",(`(NUMERAL m) EXP (NUMERAL n)`,NUM_EXP_CONV);
   "NUM_DIV_CONV",(`(NUMERAL m) DIV (NUMERAL n)`,NUM_DIV_CONV);
   "NUM_MOD_CONV",(`(NUMERAL m) MOD (NUMERAL n)`,NUM_MOD_CONV);
   "NUM_MAX_CONV",(`MAX (NUMERAL m) (NUMERAL n)`,NUM_MAX_CONV);
   "NUM_MIN_CONV",(`MIN (NUMERAL m) (NUMERAL n)`,NUM_MIN_CONV)];;

set_compute_rewrites
  (map (fun tm -> prove (tm,REWRITE_TAC[]))
       [`FST (x:A,y:B) = x`; `SND (x:A,y:B) = y`; `x:A = x <=> T`;
        `~T <=> F`; `~F <=> T`] @
   [o_THM; I_THM]);;

(* Tests *)
(*
COMPUTE_CONV [] `(\n. FACT n) (let x = 2 in if x < 3 then 3 * 4 else x + 1)`;;
COMPUTE_CONV [] `let x = 1 in x + 2`;;
COMPUTE_CONV [] `let x,y = SND(3,(1,2)) in x + y`;;
COMPUTE_CONV [] `let x = FST(3,(1,2)) in x + 2`;;
*)
