(* ========================================================================= *)
(* SAT-SMT examples via the SMT-LIB2 interface.                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Extension of the S-expression translator that eliminates atoms that are   *)
(* equalities of the form `PP i = PP j`.                                     *)
(*                                                                           *)
(* This custom translator handles position predicate equalities by           *)
(* converting `PP i = PP j` to just `i = j`, effectively removing the        *)
(* position predicate wrapper for cleaner SMT encoding.                      *)
(* ------------------------------------------------------------------------- *)

let sexp_of_pp_eq =
  let pp_tm = `PP` in
  fun tm ->
    let ltm, rtm = dest_eq tm in
    let lpp, i = dest_comb ltm in
    if lpp <> pp_tm then
      failwith "sexp_of_pp_eq: left term not a PP application"
    else let rpp, j = dest_comb rtm in
    if rpp <> pp_tm then
      failwith "sexp_of_pp_eq: right term not a PP application"
    else sexp_of_term (mk_eq (i, j));;

(* Register the custom PP equality handler in the translation network *)
sexp_of_term_net :=
  enter [] (`PP i = PP j`, sexp_of_pp_eq) !sexp_of_term_net;;

(* ------------------------------------------------------------------------- *)
(* Genearate smtlib2 files.                                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Generate SMT-LIB2 files with optional position datatype declarations.     *)
(*                                                                           *)
(* The position datatype represents discrete positions P0, P1, P2, P3, P4    *)
(* which can be toggled on/off via use_position_datatype flag.               *)
(* ------------------------------------------------------------------------- *)

(* Configuration flag: whether to include position datatype declarations *)
let use_position_datatype = ref true;;

let write_sexps : string -> Sexplib.Sexp.t list -> unit =
  let path = hol_ants_path^"/smt2" in
  let declare_position_sexp =
    sexp_mk_declare_datatype "Position" ["P0"; "P1"; "P2"; "P3"; "P4"] in
  fun fname sexps ->
    let pathname = Filename.concat path fname in
    let declare_pos_sexps =
      if !use_position_datatype then [declare_position_sexp] else [] in
    write_sexps_to_file pathname (declare_pos_sexps @ sexps);;

(* Convenience functions for generating different types of SMT-LIB2 files *)
let prove_smt2 fname tm =  write_sexps fname (sexp_mk_prove tm);;
let model_smt2 fname tm = write_sexps fname (sexp_mk_find_model tm);;

(* ------------------------------------------------------------------------- *)
(* Generate SMT-LIB2 files for invariant checking and model finding.         *)
(*                                                                           *)
(* First batch: with position datatype declarations                          *)
(* ------------------------------------------------------------------------- *)

use_position_datatype := true;;

(* Invariant checking: these generate (assert (not ...)) + (check-sat) *)
prove_smt2 "invariant_2.smt2" invariant_tm_2;;
prove_smt2 "invariant_5.smt2" invariant_tm_5;;
prove_smt2 "invariant_10.smt2" invariant_tm_10;;

(* Model finding: these generate (assert ...) + (check-sat) + (get-model) *)
model_smt2 "simul_2.smt2" simul_tm_2;;
model_smt2 "simul_10.smt2" simul_tm_10;;

model_smt2 "counterex_2.smt2" counterex_tm_2;;

model_smt2 "reach_5.smt2" reach_5;;

(* ------------------------------------------------------------------------- *)
(* Generate SMT-LIB2 files without position datatype declarations.           *)
(*                                                                           *)
(* Second batch: same terms but without position type, using raw integers.   *)
(* ------------------------------------------------------------------------- *)

use_position_datatype := false;;

prove_smt2 "invariant_nopos_2.smt2" invariant_nopos_tm_2;;
prove_smt2 "invariant_nopos_5.smt2" invariant_nopos_tm_5;;
prove_smt2 "invariant_nopos_10.smt2" invariant_nopos_tm_10;;

(* ------------------------------------------------------------------------- *)
(* Commented experimental code: Minimal examples for OCaml Z3 interface.     *)
(*                                                                           *)
(* These examples demonstrate terms that sometimes fail with the OCaml Z3    *)
(* interface, likely due to quantifier handling or arithmetic reasoning.     *)
(* Left commented for reference and debugging purposes.                      *)
(* ------------------------------------------------------------------------- *)

(*
(* Term with nested quantifiers and arithmetic *)
let ptm =
  `((~(a > b) \/ ~(a > c)) \/ ~(a + 1 > b) \/ ~(a + 1 > c)) /\
   c <= a + 1
   ==> ?a b a_ b_.
           (((a = x /\ b = y /\ c = z) /\ y <= x) /\
            a_ = a + 1 /\
            b_ = b /\
            c_ = c)`;;

(* Variant with primed variables to avoid name conflicts *)
let ptm =
  `((~(x' > y') \/ ~(x' > z')) \/ ~(x' + 1 > y') \/ ~(x' + 1 > z')) /\
   z' <= x' + 1
   ==> ?x' y' x'' y''.
           (((x' = x /\ y' = y /\ z' = z) /\ y <= x) /\
            x'' = x' + 1 /\
            y'' = y' /\
            z'' = z')`;;

(* Negation transformation for satisfiability checking *)
let xtm =
  let xtm = mk_neg(list_mk_forall(frees ptm, ptm)) in
  let xth = REWRITE_CONV[NOT_FORALL_THM; NOT_EXISTS_THM;
                         DE_MORGAN_THM; NOT_IMP] xtm in
  let xtm = rhs(concl xth) in
  let xtm = snd (strip_exists xtm) in
  xtm;;

let ptm = xtm;;
let ptm = mk_neg ptm;;
*)