(* ========================================================================= *)
(* Interface HOL Light with the Z3 solver.                                   *)
(* ========================================================================= *)

needs "z3base.ml";;

(* ------------------------------------------------------------------------- *)
(* Translation of variables.                                                 *)
(* ------------------------------------------------------------------------- *)

let basic_z3_of_var_translators = [`:bool`, Zzz.Boolean.mk_const_s;
                                   `:num`, Zzz.Arithmetic.Integer.mk_const_s];;

let z3_of_var_translators = ref basic_z3_of_var_translators;;

let z3_of_var ctx tm =
  let nm,ty = dest_var tm in
  let f = try Some assoc ty !z3_of_var_translators with Failure _ -> None in
  match f with
  | None -> failwith ("z3_of_var: Unsupported type: "^string_of_type ty)
  | Some f -> f ctx nm;;

(* ------------------------------------------------------------------------- *)
(* Translation of constants.                                                 *)
(* ------------------------------------------------------------------------- *)

let mk_z3_const ctm cstr ctx tm =
  if tm = ctm then cstr ctx else
  failwith ("mk_z3_const: "^name_of ctm);;

let z3_of_true = mk_z3_const `T` Zzz.Boolean.mk_true;;

let z3_of_false = mk_z3_const `F` Zzz.Boolean.mk_false;;

(* ------------------------------------------------------------------------- *)
(* Net-based translation infrastructure from HOL terms to Z3 expressions.    *)
(* ------------------------------------------------------------------------- *)

let z3_of_term_net : (Zzz.context -> term-> Zzz.Expr.expr) net ref =
  ref empty_net;;

let z3_of_term ctx tm =
  if is_var tm then z3_of_var ctx tm else
  let l = lookup tm !z3_of_term_net in
  try tryfind (fun f -> f ctx tm) l
  with Failure s -> failwith ("z3_of_term: "^string_of_term tm);;

(* ------------------------------------------------------------------------- *)
(* Identity.                                                                 *)
(* ------------------------------------------------------------------------- *)

let z3_of_eq ctx tm =
  let x,y = dest_eq tm in
  let e = z3_of_term ctx x
  and f = z3_of_term ctx y in
  if type_of x = bool_ty
  then Zzz.Boolean.mk_iff ctx e f
  else Zzz.Boolean.mk_eq ctx e f;;

(* ------------------------------------------------------------------------- *)
(* Translation of boolean expressions.                                       *)
(* ------------------------------------------------------------------------- *)

let z3_of_neg ctx tm =
  Zzz.Boolean.mk_not ctx (z3_of_term ctx (dest_neg tm));;

let z3_of_conj ctx tm =
  let p,q = dest_conj tm in
  Zzz.Boolean.mk_and ctx [z3_of_term ctx p; z3_of_term ctx q];;

let z3_of_disj ctx tm =
  let p,q = dest_disj tm in
  Zzz.Boolean.mk_or ctx [z3_of_term ctx p; z3_of_term ctx q];;

let z3_of_imp ctx tm =
  let p,q = dest_imp tm in
  Zzz.Boolean.mk_implies ctx (z3_of_term ctx p) (z3_of_term ctx q);;

(* ------------------------------------------------------------------------- *)
(* Translation of conditional constructions.                                 *)
(* ------------------------------------------------------------------------- *)

let z3_of_cond ctx tm =
  let b,(s,t) = dest_cond tm in
  Zzz.Boolean.mk_ite ctx (z3_of_term ctx b)
                         (z3_of_term ctx s)
                         (z3_of_term ctx t);;

(* ------------------------------------------------------------------------- *)
(* Translation of quantifiers.                                               *)
(* ------------------------------------------------------------------------- *)

let z3_of_quantifier =
  let num_ty = `:num` in
  fun ctx tm ->
    let zexpr = Zzz.Arithmetic.Integer.mk_numeral_i ctx 0 in
    let vtm,btm,universal = dest_quantifier tm in
    let vexpr = z3_of_term ctx vtm
    and bexpr = z3_of_term ctx btm in
    let bexpr = if type_of vtm = num_ty
                then let lexpr = Zzz.Arithmetic.mk_le ctx zexpr vexpr in
                     if universal
                     then Zzz.Boolean.mk_implies ctx lexpr bexpr
                     else Zzz.Boolean.mk_and ctx [lexpr; bexpr]
                else bexpr in
    if universal
    then z3_simple_mk_forall ctx [vexpr] bexpr
    else z3_simple_mk_exists ctx [vexpr] bexpr;;

(* ------------------------------------------------------------------------- *)
(* Translation of arithmetical expressions.                                  *)
(* ------------------------------------------------------------------------- *)

let z3_of_numeral ctx tm =
  Zzz.Arithmetic.Integer.mk_numeral_i ctx (dest_small_numeral tm);;

let z3_of_add ctx tm =
  let x,y = dest_binary "+" tm in
  Zzz.Arithmetic.mk_add ctx [z3_of_term ctx x; z3_of_term ctx y];;

let z3_of_le ctx tm =
  let x,y = dest_binary "<=" tm in
  Zzz.Arithmetic.mk_ge ctx (z3_of_term ctx y) (z3_of_term ctx x);;

let z3_of_gt ctx tm =
  let x,y = dest_binary ">" tm in
  Zzz.Arithmetic.mk_gt ctx (z3_of_term ctx x) (z3_of_term ctx y);;

(* ------------------------------------------------------------------------- *)
(* Default net for z3_of_term.                                               *)
(* ------------------------------------------------------------------------- *)

let basic_z3_of_term_net = itlist (enter [])
  [`p:A = q`, z3_of_eq;
   `~p`,z3_of_neg;
   `p /\ q`, z3_of_conj;
   `p \/ q`, z3_of_disj;
   `p ==> q`, z3_of_imp;
   `if p then q else r:A`, z3_of_cond;
   `!x:A. P`, z3_of_quantifier;
   `?x:A. P`, z3_of_quantifier;
   `NUMERAL n`, z3_of_numeral;
   `m + n:num`, z3_of_add;
   `m <= n:num`, z3_of_le;
   `m > n:num`, z3_of_gt;
   `T`, z3_of_true;
   `F`, z3_of_false]
  empty_net;;

z3_of_term_net := basic_z3_of_term_net;;

(* ------------------------------------------------------------------------- *)
(* Further procedures for the invocation of the Z3 checker.                  *)
(* ------------------------------------------------------------------------- *)

let z3_prove ctx tml tm =
  let ptm = itlist (curry mk_conj) tml (mk_neg tm) in
  let ptm = list_mk_forall (frees ptm,ptm) in
  let s = Zzz.Solver.mk_simple_solver ctx in
  let ret = Zzz.Solver.check s [z3_of_term ctx ptm] in
  if ret = Zzz.Solver.satisfiable then  false else
  if ret = Zzz.Solver.unsatisfiable then true else
  if ret = Zzz.Solver.unknown
  then failwith ("z3_prove: UNKNOWN: "^Zzz.Solver.get_reason_unknown s)
  else failwith "z3_prove: Anomaly";;

  (* let l = mk_neg tm :: tml in
  let exprs = map (z3_of_term ctx) l in
  let s = Zzz.Solver.mk_simple_solver ctx in
  let ret = Zzz.Solver.check s exprs in
  if ret = Zzz.Solver.satisfiable then  false else
  if ret = Zzz.Solver.unsatisfiable then true else
  if ret = Zzz.Solver.unknown
  then failwith ("z3_prove: UNKNOWN: "^Zzz.Solver.get_reason_unknown s)
  else failwith "z3_prove: Anomaly";; *)

let Z3_TAC ctx : tactic =
  fun (asl,w) as gl ->
    let ret = z3_prove ctx (map (concl o snd) asl) w in
    if ret then CHEAT_TAC gl else
    failwith "Z3_TAC: Satisfiable";;
