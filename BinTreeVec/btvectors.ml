(* ========================================================================= *)
(* Binary tree vectors.                                                      *)
(*                                                                           *)
(* (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018                  *)
(* (c) Copyright, Marco Maggesi 2025                                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Concrete representation of vectors.                                       *)
(* ------------------------------------------------------------------------- *)

let VECX_DEF = new_definition
  `vecx a:A^1 = lambda0 i. a`;;

let VEC0_DEF = new_definition
  `vec0 (x:A^N) (y:A^N) : A^N tybit0 =
   lambda0 i. (if EVEN i then x else y)$.(i DIV 2)`;;

let VEC1_DEF = new_definition
  `vec1 (x:A^N) (y:A^N) (a:A) : A^N tybit1 =
   lambda0 i. if i = 2 * dimindex(:N) then a else
              (if EVEN i then x else y)$.(i DIV 2)`;;

let VECX_COMPONENT0 = prove
 (`!a:A i. vecx a$.i = a`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[VECTOR0_1_GEN] THEN
  SIMP_TAC[VECX_DEF; LAMBDA0_BETA; DIMINDEX_1; ARITH_RULE`0 < 1`]);;

let VEC0_COMPONENT0 = prove
 (`!x y:A^N i.
     i < 2 * dimindex(:N)
     ==> vec0 x y$.i = (if EVEN i then x else y)$.(i DIV 2)`,
  SIMP_TAC[VEC0_DEF; LAMBDA0_BETA; DIMINDEX_TYBIT0]);;

let VEC1_COMPONENT0 = prove
 (`!x y:A^N a i.
     i < 2 * dimindex(:N) + 1
     ==> vec1 x y a$.i = if i = 2 * dimindex(:N) then a else
                         (if EVEN i then x else y)$.(i DIV 2)`,
  SIMP_TAC[VEC1_DEF; LAMBDA0_BETA; DIMINDEX_TYBIT1]);;

(* ------------------------------------------------------------------------- *)
(* Computing components of a binary-indexd vector.                           *)
(* ------------------------------------------------------------------------- *)

let VEC0_COMPONENT0_BINARY = prove
 (`(!x y:A^N. vec0 x y$.0 = x$.0) /\
   (!x y:A^N i. i < dimindex(:N) ==> vec0 x y$.(2 * i) = x$.i) /\
   (!x y:A^N i. i < dimindex(:N) ==> vec0 x y$.(2 * i + 1) = y$.i)`,
  SIMP_TAC[VEC0_COMPONENT0; DIMINDEX_GT_0; DIMINDEX_TYBIT0; NUM_LT_BINARY;
           NUM_EVEN_BINARY; NUM_DIV2_BINARY]);;

let VEC1_COMPONENT0_BINARY = prove
 (`(!x y:A^N a. vec1 x y a $. 0 = x$.0) /\
   (!x y:A^N a i. i <= dimindex(:N)
                  ==> vec1 x y a$.(2 * i) =
                      if i = dimindex(:N) then a else x$.i) /\
   (!x y:A^N a i. i < dimindex(:N) ==> vec1 x y a$.(2 * i + 1) = y$.i)`,
  SIMP_TAC[VEC1_COMPONENT0; DIMINDEX_GT_0; DIMINDEX_TYBIT1; NUM_LT_BINARY;
           NUM_EVEN_BINARY; NUM_EQ_BINARY; NUM_DIV2_BINARY] THEN
  SUBGOAL_THEN `~(dimindex(:N) = 0)` (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `1 <= dimindex(:N)` MP_TAC THENL
  [REWRITE_TAC[DIMINDEX_GE_1]; ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Extensionality for finite vectors.                                        *)
(* ------------------------------------------------------------------------- *)

let VECTOR_EQ_ARITH = prove
 (`(!a b:A. vecx a = vecx b <=> a = b) /\
   (!x x' y y':A^N. vec0 x y = vec0 x' y' <=> x = x' /\ y = y') /\
   (!x x' y y':A^N c1 c2. vec1 x y c1 = vec1 x' y' c2 <=>
                          x = x' /\ y = y' /\ c1 = c2)`,
  CONJ_TAC THENL
  [REWRITE_TAC[CART_EQ0; VECX_COMPONENT0; DIMINDEX_1]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_LT_BINARY] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ0; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1;
              FORALL_LT_BINARY] THEN
  SIMP_TAC[VEC0_COMPONENT0_BINARY; VEC1_COMPONENT0_BINARY] THEN
  MESON_TAC[LE_LT; LE_REFL; ARITH_RULE `!i n:num. i < n ==> ~(i = n)`]);;

(* ------------------------------------------------------------------------- *)
(* Case analysis for binary indexed vectors.                                 *)
(* ------------------------------------------------------------------------- *)

let VECTOR_CASES_THM = prove
 (`(!v. ?x:A. v = vecx x) /\
   (!v. ?x y:A^N. v = vec0 x y) /\
   (!v. ?x y:A^N a. v = vec1 x y a)`,
  REPEAT CONJ_TAC THEN GEN_TAC THENL
  [EXISTS_TAC `v:A^1 $. 0` THEN
   REWRITE_TAC[CART_EQ0; VECX_COMPONENT0; DIMINDEX_1; FORALL_LT_BINARY]
   ;
   EXISTS_TAC `(lambda0 i. (v:A^N tybit0) $. (2 * i)) : A^N` THEN
   EXISTS_TAC `(lambda0 i. (v:A^N tybit0) $. (2 * i + 1)) : A^N` THEN
   REWRITE_TAC[CART_EQ0; DIMINDEX_TYBIT0; FORALL_LT_BINARY] THEN
   SIMP_TAC[VEC0_COMPONENT0_BINARY; LAMBDA0_BETA]
   ;
   EXISTS_TAC `(lambda0 i. (v:A^N tybit1) $. (2 * i)) : A^N` THEN
   EXISTS_TAC `(lambda0 i. (v:A^N tybit1) $. (2 * i + 1)) : A^N` THEN
   EXISTS_TAC `(v:A^N tybit1) $. (2 * dimindex(:N))` THEN
   REWRITE_TAC[CART_EQ0; DIMINDEX_TYBIT1; FORALL_LT_BINARY] THEN
   SIMP_TAC[VEC1_COMPONENT0_BINARY; LAMBDA0_BETA] THEN
   GEN_TAC THEN REWRITE_TAC[LE_LT] THEN STRIP_TAC THEN
   ASM_SIMP_TAC[LAMBDA0_BETA; ARITH_RULE `i < n:num ==> ~(i = n)`]]);;

let FORALL_VECTOR_THM = prove
 (`(!P. (!x. P x) <=> (!a:A. P (vecx a))) /\
   (!P. (!x. P x) <=> (!y z:A^N. P (vec0 y z))) /\
   (!P. (!x. P x) <=> (!y z:A^N c. P (vec1 y z c)))`,
  MESON_TAC[VECTOR_CASES_THM]);;

let EXISTS_VECTOR_THM = prove
 (`(!P. (?x. P x) <=> (?a:A. P (vecx a))) /\
   (!P. (?x. P x) <=> (?y z:A^N. P (vec0 y z))) /\
   (!P. (?x. P x) <=> (?y z:A^N c. P (vec1 y z c)))`,
  MESON_TAC[VECTOR_CASES_THM]);;

(* ------------------------------------------------------------------------- *)
(* Unfolding lambda0.                                                        *)
(* ------------------------------------------------------------------------- *)

let LAMBDA0_BINARY = prove
 (`(!f:num->A. (lambda0) f : A^1 = vecx (f 0)) /\
   (!f:num->A. (lambda0) f : A^N tybit0 = vec0 (lambda0 j. f (2 * j))
                                               (lambda0 j. f (2 * j + 1))) /\
   (!f:num->A. (lambda0) f : A^N tybit1 = vec1 (lambda0 j. f (2 * j))
                                               (lambda0 j. f (2 * j + 1))
                                               (f (2 * dimindex(:N))))`,
  REWRITE_TAC[CART_EQ0] THEN SIMP_TAC[LAMBDA0_BETA] THEN
  REWRITE_TAC[DIMINDEX_1; VECX_COMPONENT0; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1;
              FORALL_LT_BINARY] THEN
  SIMP_TAC[VEC0_COMPONENT0_BINARY; VEC1_COMPONENT0_BINARY; LAMBDA0_BETA] THEN
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[LE_LT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA0_BETA; ARITH_RULE `i:num < n ==> ~(i = n)`]);;

let LAMBDA0_ARITH = prove
 (`(!f:num->A. (lambda0) f : A^N = lambda0 i. f (NUMERAL i)) /\
   (!f:num->A. (lambda0) f : A^1 = vecx (f _0)) /\
   (!f:num->A. (lambda0) f : A^N tybit0 = vec0 (lambda0 j. f (BIT0 j))
                                               (lambda0 j. f (BIT1 j))) /\
   (!f:num->A. (lambda0) f : A^N tybit1 = vec1 (lambda0 j. f (BIT0 j))
                                               (lambda0 j. f (BIT1 j))
                                               (f (BIT0 (dimindex(:N)))))`,
  CONJ_TAC THENL [REWRITE_TAC[NUMERAL; ETA_AX]; ALL_TAC] THEN
  CONV_TAC BITS_ELIM_CONV THEN CONJ_TAC THEN
  REWRITE_TAC[CART_EQ0] THEN SIMP_TAC[LAMBDA0_BETA] THEN
  REWRITE_TAC[DIMINDEX_1; VECX_COMPONENT0; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1;
              FORALL_LT_BINARY] THEN
  SIMP_TAC[VEC0_COMPONENT0_BINARY; VEC1_COMPONENT0_BINARY; LAMBDA0_BETA] THEN
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[LE_LT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAMBDA0_BETA; ARITH_RULE `i:num < n ==> ~(i = n)`]);;

(*---------------------------------------------------------------------------*)
(* Functions for constructing and destructing a vector.                      *)
(*---------------------------------------------------------------------------*)

let rec get_vector_component (d:int) (n:int) : term -> term =
  function
    Comb(Const("vecx",_),x) -> x
  | Comb(Comb(Const("vec0",_),xtm),ytm) ->
      let d' = d / 2
      and n' = n / 2 in
      let tm = if n mod 2 = 0 then xtm else ytm in
      get_vector_component d' n' tm
  | Comb(Comb(Comb(Const("vec1",_),xtm),ytm),atm) ->
      if n = d - 1 then atm else
      let d' = d / 2
      and n' = n / 2 in
      let tm = if n mod 2 = 0 then xtm else ytm in
      get_vector_component d' n' tm
  | _ -> failwith "get_vector_component";;

let dest_vector =
  fun vtm ->
    let ety,dty =
      match type_of vtm with
        Tyapp ("cart",[ety;dty]) -> ety,dty
      | _ -> fail() in
  let dim = Num.int_of_num(dest_finty dty) in
  let rec loop i acc =
    if i < 0 then acc else
    loop (i-1) (get_vector_component dim i vtm :: acc) in
  loop (dim - 1) [];;

let (mk_vector : term list -> term),
    (pmk_vector : preterm list -> preterm) =
  let rec pos_even_list =
    function
      [] -> []
    | h :: t -> h :: pos_odd_list t
  and pos_odd_list =
    function
      [] -> []
    | _ :: t -> pos_even_list t in
  let mk_vector =
    let ntvar = `:N` in
    let mk_vecx ty tm =
      mk_comb(mk_const("vecx",[ty,aty]),tm)
    and mk_vec0 ty nty tm0 tm1 =
      mk_comb(mk_comb(mk_const("vec0",[ty,aty;nty,ntvar]),tm0),tm1)
    and mk_vec1 ty nty tm0 tm1 tm2 =
      let pconst = mk_const("vec1",[ty,aty;nty,ntvar]) in
      mk_comb(mk_comb(mk_comb(pconst,tm0),tm1),tm2) in
    fun l ->
      if l = [] then failwith "mk_vector: empty list" else
      let ty = type_of(hd l) in
      let mk_vecx = mk_vecx ty
      and mk_vec0 = mk_vec0 ty
      and mk_vec1 = mk_vec1 ty in
      let rec mk_vector d l =
        if d = 1 then `:1`,mk_vecx (hd l) else
        let d' = d / 2 in
        if d mod 2 = 0 then
          let nty,l0 = mk_vector d' (pos_even_list l) in
          let _,l1 = mk_vector d' (pos_odd_list l) in
          let nty' = mk_type("tybit0",[nty]) in
          nty',mk_vec0 nty l0 l1
        else
          let l' = pos_even_list l in
          let nty,vtm0 = mk_vector d' (butlast l') in
          let   _,vtm1 = mk_vector d' (pos_odd_list l) in
          let nty' = mk_type("tybit1",[nty]) in
          nty',mk_vec1 nty vtm0 vtm1 (last l')
          in
      snd(mk_vector (length l) l) in
  let pmk_vector =
    let vecx_ptm = Varp("vecx",dpty)
    and vec0_ptm = Varp("vec0",dpty)
    and vec1_ptm = Varp("vec1",dpty) in
    let pmk_vecx ptm = Combp(vecx_ptm,ptm)
    and pmk_vec0 ptm1 ptm2 = Combp(Combp(vec0_ptm,ptm1),ptm2)
    and pmk_vec1 ptm1 ptm2 ptm3 = Combp(Combp(Combp(vec1_ptm,ptm1),ptm2),ptm3) in
    let rec pmk_vector d l =
      if d = 0 then failwith "pmk_vector: anomaly" else
      if d = 1 then pmk_vecx (hd l) else
      let d' = d / 2 in
      if d mod 2 = 0 then
        let l0 = pos_even_list l
        and l1 = pos_odd_list l in
        pmk_vec0 (pmk_vector d' l0) (pmk_vector d' l1)
      else
        let l0 = pos_even_list l
        and l1 = pos_odd_list l in
        let a = last l0 in
        let l0 = butlast l0 in
        pmk_vec1 (pmk_vector d' l0) (pmk_vector d' l1) a in
    function
      [] -> failwith "pmk_vector: empty list"
    | l -> pmk_vector (length l) l in
  mk_vector,pmk_vector;;

(* ------------------------------------------------------------------------- *)
(* Custom parser for vectors.                                                *)
(* ------------------------------------------------------------------------- *)

let parse_finvec =
  let parse_seq = elistof parse_preterm (a (Resword ";")) "term" in
  ((a (Ident "Vx") ++ a (Resword "[")) ++ parse_seq >> snd) ++ a (Resword "]")
  >> (pmk_vector o fst);;

install_parser("finvec",parse_finvec);;

(* ------------------------------------------------------------------------- *)
(* Custom printer for vectors.                                               *)
(* ------------------------------------------------------------------------- *)

let rec pp_print_term_sequence fmt break sep =
  function
    [] -> ()
  | htm :: ttms ->
      pp_print_term fmt htm;
      if ttms = [] then () else
      (pp_print_string fmt sep;
       (if break then pp_print_space fmt ());
       pp_print_term_sequence fmt break sep ttms);;

let pp_finvec_printer fmt tm =
  let tml = dest_vector tm in
  pp_open_box fmt 0; pp_print_string fmt "Vx["; pp_open_box fmt 0;
  pp_print_term_sequence fmt true ";" tml;
  pp_close_box fmt (); pp_print_string fmt "]";
  pp_close_box fmt ();;

install_user_printer("finvec",pp_finvec_printer);;

(* ------------------------------------------------------------------------- *)
(* Relation for accessing a vector component.                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_vector_component0",(12,"right"));;

let has_vector_component0 = new_definition
  `(v:A^N has_vector_component0 x) i <=> i < dimindex(:N) /\ v$.i = x`;;

let HAS_VECTOR_COMPONENT0_BINARY = prove
 (`(!a b i. (vecx a:A^1 has_vector_component0 b) i <=> i = 0 /\ a = b) /\
   (!x y:A^N b.
      (vec0 x y has_vector_component0 b) 0 <=>
      (x has_vector_component0 b) 0) /\
   (!x y:A^N b i.
      (vec0 x y has_vector_component0 b) (2 * i) <=>
      (x has_vector_component0 b) i) /\
   (!x y:A^N b i.
      (vec0 x y has_vector_component0 b) (2 * i + 1) <=>
      (y has_vector_component0 b) i) /\
   (!x y:A^N a b.
      (vec1 x y a has_vector_component0 b) 0 <=>
      (x has_vector_component0 b) 0) /\
   (!x y:A^N a b i.
      (vec1 x y a has_vector_component0 b) (2 * i) <=>
      if i = dimindex(:N) then a = b else
      (x has_vector_component0 b) i) /\
   (!x y:A^N a b i.
      (vec1 x y a has_vector_component0 b) (2 * i + 1) <=>
      (y has_vector_component0 b) i)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[has_vector_component0; DIMINDEX_1; DIMINDEX_TYBIT0;
              DIMINDEX_TYBIT1; NUM_LT_BINARY;
              MESON[] `(p /\ q <=> p /\ r) <=> (p ==> (q <=> r))`] THEN
  SIMP_TAC[VECX_COMPONENT0; VEC0_COMPONENT0_BINARY;
           VEC1_COMPONENT0_BINARY] THEN
  REWRITE_TAC[DIMINDEX_GT_0] THENL
  [MESON_TAC[ARITH_RULE `i < 1 <=> i = 0`]; ALL_TAC] THEN
  ASM_CASES_TAC `i <= dimindex(:N)` THEN
  ASM_SIMP_TAC[VEC1_COMPONENT0_BINARY] THEN
  ASM_MESON_TAC[LT_LE; NOT_LE]);;

let HAS_VECTOR_COMPONENT0_ARITH = prove
 (`(!v:A^N b i.
      (v has_vector_component0 b) (NUMERAL i) <=>
      (v has_vector_component0 b) i) /\
   (!a b i. (vecx a:A^1 has_vector_component0 b) i <=> i = _0 /\ a = b) /\
   (!x y:A^N b.
      (vec0 x y has_vector_component0 b) _0 <=>
      (x has_vector_component0 b) _0) /\
   (!x y:A^N b i.
      (vec0 x y has_vector_component0 b) (BIT0 i) <=>
      (x has_vector_component0 b) i) /\
   (!x y:A^N b i.
      (vec0 x y has_vector_component0 b) (BIT1 i) <=>
      (y has_vector_component0 b) i) /\
   (!x y:A^N a b.
      (vec1 x y a has_vector_component0 b) _0 <=>
      (x has_vector_component0 b) _0) /\
   (!x y:A^N a b i.
      (vec1 x y a has_vector_component0 b) (BIT0 i) <=>
      if i = dimindex(:N) then a = b else
      (x has_vector_component0 b) i) /\
   (!x y:A^N a b i.
      (vec1 x y a has_vector_component0 b) (BIT1 i) <=>
      (y has_vector_component0 b) i)`,
  CONJ_TAC THENL [REWRITE_TAC[NUMERAL]; ALL_TAC] THEN
  CONV_TAC BITS_ELIM_CONV THEN
  REWRITE_TAC[HAS_VECTOR_COMPONENT0_BINARY]);;

(* ------------------------------------------------------------------------- *)
(* Conversion for computing the component of a binary-indexed vector.        *)
(* ------------------------------------------------------------------------- *)

let VECTOR_COMPONENT0_CONV : conv =
  let MK_HAS_VECTOR_COMPONENT0 : term -> thm =
    let dest_cart_ty =
      function
        Tyapp("cart",[ety;dty]) -> ety,dty
      | _ -> failwith "dest_cart_ty" in
    let denumeral =
      function
        Comb(Const("NUMERAL",_),tm) -> tm
      | _ -> failwith "denumeral: Not a numeral" in
    let dest_component0 = dest_binary "$." in
    let pth_cond = MESON[]
      `(if T then a:A else b) = a /\ (if F then a:A else b) = b` in
    let VECX_HAS_VECTOR_COMPONENT0_ARITH = prove
     (`!a b. (vecx a:A^1 has_vector_component0 b) _0 <=> a = b`,
      REWRITE_TAC[HAS_VECTOR_COMPONENT0_ARITH]) in
    let HAS_VECTOR_COMPONENT0_ARITH' =
      let pth1 = CONJUNCT1 HAS_VECTOR_COMPONENT0_ARITH
      and pth2 = CONJUNCT2 (CONJUNCT2 HAS_VECTOR_COMPONENT0_ARITH) in
      CONJ pth1 (CONJ VECX_HAS_VECTOR_COMPONENT0_ARITH pth2) in
    let pconv : conv =
      REPEATC
        (GEN_REWRITE_CONV I [HAS_VECTOR_COMPONENT0_ARITH'] THENC
         TRY_CONV
           (RATOR_CONV (LAND_CONV
             (RAND_CONV (DIMINDEX_CONV THENC REWR_CONV NUMERAL) THENC
              GEN_REWRITE_CONV REPEATC [ARITH_EQ])) THENC
            GEN_REWRITE_CONV I [pth_cond]))  in
    let prule = CONV_RULE (REWR_CONV (MESON[] `(p <=> x:A = x) <=> p`)) in
    fun tm ->
      let vtm,itm = dest_component0 tm in
      let vty = type_of vtm in
      let xty,nty = dest_cart_ty vty in
      let xvar = genvar xty in
      let rtm =
        let fty = mk_fun_ty vty (mk_fun_ty xty `:num->bool`) in
        let ftm = mk_mconst("has_vector_component0",fty) in
        mk_comb(mk_binop ftm vtm xvar,denumeral itm) in
      let pth = pconv rtm in
      let xtm = lhs(rand(concl pth)) in
    prule (INST [xtm,xvar] pth) in
  let pth = prove
   (`!v:A^N x i. (v has_vector_component0 x) i ==> v $. NUMERAL i = x`,
    SIMP_TAC[NUMERAL; has_vector_component0]) in
  let prule = MATCH_MP pth in
  fun tm -> prule (MK_HAS_VECTOR_COMPONENT0 tm);;

let VECTOR_COMPONENT_CONV : conv =
  let pth = prove
   (`!x:A^N i j. i = SUC j ==> x$i = x$.j`,
    REWRITE_TAC[component0; ADD1] THEN MESON_TAC[]) in
  let dest_component = dest_binary "$" in
  fun tm ->
    let jth = num_CONV(snd(dest_component tm)) in
    (REWR_CONV (MATCH_MP pth jth) THENC VECTOR_COMPONENT0_CONV) tm;;

(* ------------------------------------------------------------------------- *)
(* Conversions for computing with vectors.                                   *)
(* ------------------------------------------------------------------------- *)

let core_vector_net =
  let thl = [VECTOR_EQ_ARITH] in
  let thl_canon = itlist (mk_rewrites false) thl [] in
  let rewr_net = itlist (net_of_thm false) thl_canon empty_net in
  let final_net =
    net_of_conv `u:A^N $. NUMERAL n` VECTOR_COMPONENT0_CONV
      (net_of_conv `u:A^N $ NUMERAL n` VECTOR_COMPONENT_CONV rewr_net) in
  final_net;;

let vector_net = ref core_vector_net;;

let basic_vector_net() = !vector_net;;

let VECTOR_RED_CONV : conv =
  fun tm ->
    let RW_CONV = REWRITES_CONV (basic_vector_net()) in
    (RW_CONV THENC TOP_DEPTH_CONV RW_CONV THENC REAL_RAT_REDUCE_CONV) tm;;

let VECTOR_REDUCE_CONV : conv =
  DEPTH_CONV VECTOR_RED_CONV;;

let VECTOR_REDUCE_TAC : tactic =
  CONV_TAC VECTOR_REDUCE_CONV;;
