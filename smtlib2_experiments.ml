(* ------------------------------------------------------------------------- *)
(* Teorema dell'invariante                                                   *)
(* ------------------------------------------------------------------------- *)

let sexp_of_pp_eq =
  let pp_tm = `PP` in
  fun tm -> let ltm,rtm = dest_eq tm in
            let lpp,i = dest_comb ltm in
            if lpp <> pp_tm then failwith "sexp_of_pp_eq" else
            let rpp,j = dest_comb rtm in
            if rpp <> pp_tm then failwith "sexp_of_pp_eq" else
            sexp_of_term (mk_eq(i,j));;

sexp_of_term_net :=
  enter [] (`PP i = PP j`,sexp_of_pp_eq) !sexp_of_term_net;;

(* Con una formica. *)
g `!sys sys':1 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
e (REWRITE_TAC[CART_EQ; DIMINDEX_1; FORALL_1; DIMINDEX_3; FORALL_3; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_VECTOR_1; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_3; VECTOR_1]);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_3; DIMINDEX_1; NSUM_1; VECTOR_3; VECTOR_1; PP]);;
e (REWRITE_TAC[MAX]);;
let _,ptm = top_goal();;

(* Con due formiche. *)
g `!sys sys':2 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
e (REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; DIMINDEX_3; FORALL_3; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_VECTOR_2; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_3; VECTOR_2]);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_3; DIMINDEX_2; NSUM_2; VECTOR_3; VECTOR_2; PP]);;
e (REWRITE_TAC[MAX]);;
e (REWRITE_TAC[FORALL_POSITION_NUM_THM; EXISTS_POSITION_NUM_THM; GSYM PP]);;
e (REWRITE_TAC[FORALL_POSITION_NUM_THM; EXISTS_POSITION_NUM_THM; GSYM PP;
               MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`;
               RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC]);;
let _,ptm = top_goal();;

(* Con 3 formiche. *)
g `!sys sys':3 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
e (REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; DIMINDEX_3; FORALL_3; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_VECTOR_3; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_3; VECTOR_3]);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_3; DIMINDEX_3; NSUM_3; VECTOR_3; VECTOR_3; PP]);;
e (REWRITE_TAC[MAX]);;
e (REWRITE_TAC[FORALL_POSITION_NUM_THM; EXISTS_POSITION_NUM_THM; GSYM PP;
               MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`;
               RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC]);;
let _,ptm = top_goal();;

(* Con 4 formiche. *)
g `!sys sys':4 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
e (REWRITE_TAC[CART_EQ; DIMINDEX_4; FORALL_4; DIMINDEX_3; FORALL_3; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_VECTOR_4; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_3; VECTOR_4]);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_3; DIMINDEX_4; NSUM_4; VECTOR_3; VECTOR_4; PP]);;
e (REWRITE_TAC[MAX]);;
e (REWRITE_TAC[FORALL_POSITION_NUM_THM; EXISTS_POSITION_NUM_THM; GSYM PP;
               MESON [] `(if a then PP b else PP c) = PP (if a then b else c)`;
               RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC]);;
let _,ptm = top_goal();;

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

let ptm =
  `((~(a > b) \/ ~(a > c)) \/ ~(a + 1 > b) \/ ~(a + 1 > c)) /\
   c <= a + 1
   ==> ?a b a_ b_.
           (((a = x /\ b = y /\ c = z) /\ y <= x) /\
            a_ = a + 1 /\
            b_ = b /\
            c_ = c)`;;

let ptm =
  `((~(x' > y') \/ ~(x' > z')) \/ ~(x' + 1 > y') \/ ~(x' + 1 > z')) /\
   z' <= x' + 1
   ==> ?x' y' x'' y''.
           (((x' = x /\ y' = y /\ z' = z) /\ y <= x) /\
            x'' = x' + 1 /\
            y'' = y' /\
            z'' = z')`;;

let xtm =
  let xtm = mk_neg(list_mk_forall(frees ptm,ptm)) in
  let xth = REWRITE_CONV[NOT_FORALL_THM; NOT_EXISTS_THM;
                         DE_MORGAN_THM; NOT_IMP] xtm in
  let xtm = rhs(concl xth) in
  let xtm = snd (strip_exists xtm) in
  xtm;;

let ptm = xtm;;

let ptm = mk_neg ptm;;

(* let () =
  let vars = sort (<) (frees ptm) in
  let decl_sexps = map sexp_mk_declare_const vars in
  let bound_sexps = mapfilter sexp_mk_assert_nonneg vars in
  let assert_sexp = sexp_mk_fn "assert" [sexp_of_term ptm] in
  let check_sexp = sexp_mk_fn "check-sat" [] in
  let get_sexps = sexp_mk_get_values (map name_of vars) in
  let sexps = decl_sexps @
              bound_sexps @
              [assert_sexp; check_sexp] @ get_sexps in
  let path = "/workspaces/hol-light-devcontainer/code/HOL-Ants" in
  let fname = "sim1.smt2" in
  let pathname = path^"/"^fname in
  write_sexps_to_file pathname sexps;; *)

(* let () =
  let datatype_sexp = sexp_mk_declare_datatype "Position"
                        ["P0"; "P1"; "P2"; "P3"; "P4"] in
  let vl = sort (<) (frees ptm) in
  let decl_sexps = map sexp_mk_declare_const vl in
  let bound_sexps = mapfilter sexp_mk_assert_nonneg vl in
  let assert_sexp = sexp_mk_fn "assert" [sexp_of_term ptm] in
  let check_sexp = sexp_mk_fn "check-sat" [] in
  let get_sexp = sexp_mk_fn "get-value"
                   [sexp_mk_list(map sexp_of_term vl)] in
  let sexps = [datatype_sexp] @
              decl_sexps @
              bound_sexps @
              [assert_sexp; check_sexp  (* ; get_sexp *)] in
  let path = "/workspaces/hol-light-devcontainer/code/HOL-Ants" in
  let fname = "sim1.smt2" in
  let pathname = path^"/"^fname in
  write_sexps_to_file pathname sexps;; *)

(*
(* ------------------------------------------------------------------------- *)
(* Examples of proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*  *)


(* let interize tm =
  if is_forall tm then
    let v,b = dest_forall tm in *)

let ptm =
  `((~(x' > y') \/ ~(x' > z')) \/ ~(x' + 1 > y') \/ ~(x' + 1 > z')) /\
   z' <= x' + 1
   ==> ?x' y' x'' y''.
           (((x' = x /\ y' = y /\ z' = z) /\ y <= x) /\
            x'' = x' + 1 /\
            y'' = y' /\
            z'' = z')`;;








(* let xtm = list_mk_forall (frees ptm,ptm) in
let xtm = mk_neg xtm in
let expr = sexp_mk_fn "assert" [sexp_of_term xtm] in
print_sexp expr;; *)

let () =
  let datatype_sexp = sexp_mk_declare_datatype "Position"
                        ["P0"; "P1"; "P2"; "P3"; "P4"] in
  let xtm = list_mk_forall (frees ptm,ptm) in
  let xtm = mk_neg xtm in
  let assert_sexp = sexp_mk_fn "assert" [sexp_of_term xtm] in
  let check_sexp = sexp_mk_fn "check-sat" [] in
  (* (get-info :reason-unknown) *)
  let get_info_sexp = sexp_mk_fn "get-info" [sexp_mk_atom ":reason-unknown"] in
  (* let get_model_sexp = sexp_mk_fn "get-model" [] in *)
  let path = "/workspaces/hol-light-devcontainer/code/HOL-Ants" in
  let fname = "thm.smt2" in
  let pathname = path^"/"^fname in
  write_sexps_to_file pathname [datatype_sexp; assert_sexp; check_sexp; get_info_sexp];;

(* ------------------------------------------------------------------------- *)
(* Examples of simulations.                                                  *)
(* ------------------------------------------------------------------------- *)

let sim4 =
  `System (vector[(a0,d0); (a1,d1); (a2,d2); (a3,d3)])
          (vector[s1; s2; s3]) : 4 system IN
   ITER 15 (SETBIND NEW_SYSTEM)
          {System (vector[(P0,T); (P1,F); (P2,F); (P4,F)])
                  (vector[0; 0; 0])}`;;

(* let CART_EQ_PTHM = prove
 (`dimindex(:N) = N <=>
   (!u v. u = v <=> (!i. i IN (1..N) ==> )
   `) *)

let ptm = sim4
  |> REWRITE_CONV
       [TOP_SWEEP_CONV num_CONV `15`; ITER; IN_SETBIND;
        IN_NEW_SYSTEM_ALT; DIMINDEX_4; FORALL_4;
        ANT; STI;
        NEW_ANT_ALT;
        NEW_STI_ALT;
        SYSTEM_INJECTIVITY;
        PAIR_EQ;
        DELTA_STI_COMPONENT_ALT;
        VECTOR_ADD_NUM_COMPONENT;
        EXISTS_SYSTEM_THM;
        EXISTS_PAIR_THM;
        EXISTS_VECTOR_4; VECTOR_4;
        EXISTS_VECTOR_3; VECTOR_3; FORALL_3;
        NSUM_4; PP;
        CART_EQ; DIMINDEX_3; VECTOR_3;
        IN_INSERT; NOT_IN_EMPTY]
  |> concl |> rhs;;

(* let EXISTS_STI_THM = prove
 (`(?v:num^3. P v) <=> (?s1 s2 s3. P (vector [s1; s2; s3]))`,
  MATCH_ACCEPT_TAC EXISTS_VECTOR_3);; *)

*)

(*
let () =
  report ";; Datatype for positions:";
  report "(declare-datatype Position ( (P0) (P1) (P2) (P3) (P4) ))";
  let vl = variables ptm in
  report "\n;; Constant declaration:";
  do_list (print_sexp o sexp_mk_declare_const) vl;
  report "\n;; Boundary assertions:";
  do_list print_sexp (mapfilter sexp_mk_assert_nonneg vl);
  report "\n;; Main assertion:";
  print_sexp (sexp_mk_fn "assert" [sexp_of_term ptm]);
  report "\n;; Check satifiability:";
  print_sexp (sexp_mk_fn "check-sat" []);
  report "\n;; Get values:";
  let sexp_vl = sexp_mk_list(map sexp_of_term (sort (<) vl)) in
  print_sexp (sexp_mk_fn "get-value" [sexp_vl]);;
*)
