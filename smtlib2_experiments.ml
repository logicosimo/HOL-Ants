(* ========================================================================= *)
(* Experiments using SAT-SMT through the smtlib2 interface.                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Extemsion of the sexp translator that eliminates atoms that are           *)
(* equalaities of the form `PP i = PP j`.                                    *)
(* ------------------------------------------------------------------------- *)

let sexp_of_pp_eq =
  let pp_tm = `PP` in
  fun tm -> let ltm,rtm = dest_eq tm in
            let lpp,i = dest_comb ltm in
            if lpp <> pp_tm then failwith "sexp_of_pp_eq" else
            let rpp,j = dest_comb rtm in
            if rpp <> pp_tm then failwith "sexp_of_pp_eq" else
            sexp_of_term (mk_eq (i,j));;

sexp_of_term_net :=
  enter [] (`PP i = PP j`,sexp_of_pp_eq) !sexp_of_term_net;;

(* ------------------------------------------------------------------------- *)
(* Genearate smtlib2 files.                                                  *)
(* ------------------------------------------------------------------------- *)

generate_smtlib2 (mk_neg invariant_tm_2) "smt2/invariant_2.smt2" false;;
generate_smtlib2 (mk_neg invariant_tm_5) "smt2/invariant_2.smt2" false;;
generate_smtlib2 (mk_neg invariant_tm_10) "smt2/invariant_10.smt2" false;;
generate_smtlib2 (mk_neg counterex_tm_2) "smt2/counterex_2.smt2" true;;
generate_smtlib2 simul_tm_2 "smt2/simul_2.smt2" true;;
generate_smtlib2 simul_tm_10 "smt2/simul_10.smt2" true;;
generate_smtlib2 simul_tm_10 "smt2/reach_5.smt2" true;;

(* ------------------------------------------------------------------------- *)
(* Minimal examples that fails (sometimes) with the OCaml Z3 interface.      *)
(* ------------------------------------------------------------------------- *)

(*
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
*)
