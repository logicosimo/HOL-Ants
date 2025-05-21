#use "topfind";;
#require "sexplib";;

let sexp_mk_list (l : Sexplib.Sexp.t list) : Sexplib.Sexp.t =
  Sexplib.Sexp.List l;;

let sexp_mk_atom (s : string) : Sexplib.Sexp.t =
  Sexplib.Sexp.Atom s;;

let sexp_pp = Sexplib.Sexp.pp_hum;;

let string_of_sexp = Sexplib.Sexp.to_string;;

let mysexp = sexp_mk_list[sexp_mk_atom "a"; sexp_mk_atom "b"];;

Format.fprintf Format.std_formatter "%a@." pp_sexp mysexp;;

(* ------------------------------------------------------------------------- *)
(* Net-based translation infrastructure from HOL terms to sexps.             *)
(* ------------------------------------------------------------------------- *)

let z3_of_term_net : (Zzz.context -> term-> Zzz.Expr.expr) net ref =
  ref empty_net;;

let z3_of_term ctx tm =
  if is_var tm then z3_of_var ctx tm else
  let l = lookup tm !z3_of_term_net in
  try tryfind (fun f -> f ctx tm) l
  with Failure s -> failwith ("z3_of_term: "^string_of_term tm);;



let sexp_of_conj tm =
  if not(is_conj tm) then failwith "sexp_of_conj" else
  let args = striplist dest_conj tm in
  sexp_mk_list (sexp_mk_atom "and" :: map sexp_of_term args);;

let sexp_of_disj tm =
  if not(is_disj tm) then failwith "sexp_of_disj" else
  let args = striplist dest_disj tm in
  sexp_mk_list (sexp_mk_atom "or" :: map sexp_of_term args);;

let sexp_of_term tm =
  if is_var tm || is_const tm then sexp_mk_atom (name_of tm) else
  if is_conj tm then sexp_of_conj tm else
  if is_disj tm then sexp_of_disj tm else
  failwith ("sexp_of_term: "^string_of_term tm);;

let strsexp_of_term = string_of_sexp o sexp_of_term;;

assert (strsexp_of_term `a` = "a");;
assert (strsexp_of_term `T` = "T");;
assert (strsexp_of_term `T /\ a /\ p` = "(and T a p)");;
assert (strsexp_of_term `T \/ a \/ p` = "(or T a p)");;
