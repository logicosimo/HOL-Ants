(* ========================================================================= *)
(* SMT-LIB2 Interface for HOL Light                                          *)
(* ========================================================================= *)
(* This module provides translation facilities from (some) HOL terms to      *)
(* SMT-LIB2 format, enabling the use of SMT solvers for automated theorem    *)
(* proving and model finding tasks.                                          *)
(* ========================================================================= *)


#use "topfind";;
#require "sexplib";;
#install_printer Sexplib.Sexp.pp_hum;;

(* ------------------------------------------------------------------------- *)
(* Basic S-expression manipulation functions                                 *)
(* These functions provide low-level operations for creating and handling    *)
(* S-expressions (symbolic expressions) used in SMT-LIB2 format              *)
(* ------------------------------------------------------------------------- *)

(* Pretty printer for S-expressions *)
let sexp_pp = Sexplib.Sexp.pp_hum;;

(* Convert S-expression to string representation *)
let string_of_sexp = Sexplib.Sexp.to_string;;

(* Create an S-expression list from a list of S-expressions *)
let sexp_mk_list (l : Sexplib.Sexp.t list) : Sexplib.Sexp.t =
  Sexplib.Sexp.List l;;

(* Strip trailing prime characters and replace with underscore + count
    This handles HOL's variable naming conventions where primes indicate
    different versions of variables (e.g., x''' becomes x_3) *)
let strip_prime s =
  let n = String.length s in
  let rec findidx i =
    if i >= 0 && String.get s i = '\''
    then findidx (i-1)
    else i in
  let i = findidx (n-1) + 1 in
  let m = n - i in
  if m = 0 then s else
  String.sub s 0 i^"_"^string_of_int m;;

(* Unit tests for strip_prime *)
assert (strip_prime "a" = "a");;
assert (strip_prime "x'''" = "x_3");;

(* Create an atomic S-expression (leaf node) from a string *)
let sexp_mk_atom (s : string) : Sexplib.Sexp.t =
  Sexplib.Sexp.Atom (strip_prime s);;

(* Create a function application S-expression: (function_nm arg1 arg2 ...) *)
let sexp_mk_fn (s : string) (l : Sexplib.Sexp.t list) : Sexplib.Sexp.t =
  sexp_mk_list (sexp_mk_atom s :: l);;

(* Print S-expression to a formatter with newline *)
let pp_sexp fmt sexp =
  Format.fprintf fmt "%a@." Sexplib.Sexp.pp_hum sexp;;

(* Print S-expression to standard output *)
let print_sexp sexp = pp_sexp Format.std_formatter;;

(** Write a list of S-expressions to a file *)
let write_sexps_to_file filename sexps =
  let oc = open_out filename in
  let fmt = Format.formatter_of_out_channel oc in
  List.iter (pp_sexp fmt) sexps;  (* List.iter instead of do_list *)
  close_out oc;;

(* ------------------------------------------------------------------------- *)
(* Example usage                                                             *)
(* ------------------------------------------------------------------------- *)

let mysexp = sexp_mk_list[sexp_mk_atom "a"; sexp_mk_atom "b"];;
Format.fprintf Format.std_formatter "%a@." sexp_pp mysexp;;


(* ------------------------------------------------------------------------- *)
(* Specialized S-expression constructors for common logical operations       *)
(* These functions handle the SMT-LIB2 syntax for boolean and arithmetic     *)
(* operations, including edge cases for empty and single-element lists       *)
(* ------------------------------------------------------------------------- *)

(* Create conjunction (AND): empty list as 'true', single element as itself *)
let sexp_mk_conj l =
  match l with
  | [] -> sexp_mk_atom "true"
  | [e] -> e
  | l -> sexp_mk_fn "and" l;;

(* Create disjunction (OR): empty list as 'false', single element as itself *)
let sexp_mk_disj l =
  match l with
  | [] -> sexp_mk_atom "false"
  | [e] -> e
  | l -> sexp_mk_fn "or" l;;

(* Create addition: empty list as '0', single element as itself *)
let sexp_mk_add l =
  match l with
  | [] -> sexp_mk_atom "0"
  | [e] -> e
  | l -> sexp_mk_fn "+" l;;

(* Create multiplication: empty list as '1', single element as itself *)
let sexp_mk_mul l =
  match l with
  | [] -> sexp_mk_atom "1"
  | [e] -> e
  | l -> sexp_mk_fn "*" l;;

(** Create subtraction (binary operation) *)
let sexp_mk_sub (a, b) =
  sexp_mk_fn "-" [a; b];;

(** Create small numeral from integer *)
let sexp_mk_small_numeral n =
  sexp_mk_atom (string_of_int n);;

(* ------------------------------------------------------------------------- *)
(* Net-based translation infrastructure from HOL terms to S-expressions      *)
(* This uses HOL Light's "net" data structure for efficient pattern matching *)
(* to determine how to translate different types of HOL terms                *)
(* ------------------------------------------------------------------------- *)

(* Global net storing translation functions for different term patterns *)
let sexp_of_term_net : (term -> Sexplib.Sexp.t) net ref =
  ref empty_net;;

(* Main term-to-S-expression translator
    Uses the net to find appropriate translation function for each term *)
let sexp_of_term tm =
  let l = lookup tm !sexp_of_term_net in
  try tryfind (fun f -> f tm) l with Failure s ->
  if is_var tm || is_const tm then sexp_mk_atom (name_of tm) else
  failwith ("sexp_of_term: "^string_of_term tm);;

(* Convert term to string via S-expression *)
let strsexp_of_term = string_of_sexp o sexp_of_term;;

(* ------------------------------------------------------------------------- *)
(* Translation of types.                                                     *)
(* ------------------------------------------------------------------------- *)

(** Translate HOL types to SMT-LIB2 sort names *)
let sexp_of_type ty =
  match fst(dest_type ty) with
  | "bool" -> sexp_mk_atom "Bool"
  | "num" -> sexp_mk_atom "Int"
  | "position" -> sexp_mk_atom "Position"
  | s -> failwith ("sexp_of_type: Unknown type: "^s);;


(* ------------------------------------------------------------------------- *)
(* Translation of identity expressions                                       *)
(* ------------------------------------------------------------------------- *)

(** Translate equality/equivalence depending on type *)
let sexp_of_eq tm =
  let x,y = dest_eq tm in
  let e = sexp_of_term x
  and f = sexp_of_term y in
  (* Use 'iff' for boolean equality, '=' for other types *)
  let fn = if type_of x = bool_ty then "iff" else "=" in
  sexp_mk_fn fn [e; f];;

(* ------------------------------------------------------------------------- *)
(* Translation of boolean expressions                                        *)
(* ------------------------------------------------------------------------- *)

(* Translate negation *)
let sexp_of_neg tm =
  sexp_mk_fn "not" [sexp_of_term (dest_neg tm)];;

(* Translate conjunction, handling nested conjunctions *)
let sexp_of_conj tm =
  if not(is_conj tm) then failwith "sexp_of_conj" else
  let args = striplist dest_conj tm in
  sexp_mk_conj (List.map sexp_of_term args);;

(* Translate disjunction, handling nested disjunctions *)
let sexp_of_disj tm =
  if not(is_disj tm) then failwith "sexp_of_disj" else
  let args = striplist dest_disj tm in
  sexp_mk_disj (List.map sexp_of_term args);;

(* Translate implication *)
let sexp_of_imp tm =
  let p,q = dest_imp tm in
  sexp_mk_fn "=>" [sexp_of_term p; sexp_of_term q];;


(* ------------------------------------------------------------------------- *)
(* Translation of conditional expressions                                    *)
(* ------------------------------------------------------------------------- *)

(** Translate if-then-else to SMT-LIB2 'ite' *)
let sexp_of_cond tm =
  let b,(s,t) = dest_cond tm in
  sexp_mk_fn "ite" [sexp_of_term b;
                    sexp_of_term s;
                    sexp_of_term t];;
          
(* ------------------------------------------------------------------------- *)
(* Translation of quantifiers                                                *)
(* ------------------------------------------------------------------------- *)

(* Create quantified variable declaration (variable name and type) *)
let mk_quant_var v =
  let nm,ty = dest_var v in
  sexp_mk_list[sexp_mk_atom nm;
               sexp_of_type ty];;

(* Create non-negativity constraint for numeric variables
   SMT-LIB2 integers are unbounded, but HOL 'num' type is non-negative *)
let sexp_mk_nonneg =
  let sexp_0 = sexp_mk_atom "0" in
  fun v ->
    let nm,ty = dest_var v in
    let nty,_ = dest_type ty in
    if nty <> "num" then failwith "sexp_mk_nonneg" else
    sexp_mk_fn ">=" [sexp_mk_atom nm; sexp_0];;

(* Translate universal quantification
   Adds non-negativity constraints for numeric variables *)
let sexp_of_forall tm =
  let vl,btm = strip_forall tm in
  if vl = [] then failwith "sexp_of_forall" else
  let vsexps = sexp_mk_list (map mk_quant_var vl) in
  let bounds = mapfilter sexp_mk_nonneg vl in
  let bdy = sexp_of_term btm in
  let bdy = if bounds = [] then bdy else
            sexp_mk_fn "=>" [sexp_mk_conj bounds; bdy] in
  sexp_mk_fn "forall" [vsexps; bdy];;

(* Translate existential quantification
   Adds non-negativity constraints for numeric variables *)
let sexp_of_exists tm =
  let vl,btm = strip_exists tm in
  if vl = [] then failwith "sexp_of_exists" else
  let vsexps = sexp_mk_list (map mk_quant_var vl) in
  let bounds = mapfilter sexp_mk_nonneg vl in
  let bdy = sexp_of_term btm in
  let bdy = if bounds = [] then bdy else
            sexp_mk_conj (bounds @ [bdy]) in
  sexp_mk_fn "exists" [vsexps; bdy];;

(* ------------------------------------------------------------------------- *)
(* Translation of arithmetic expressions                                     *)
(* ------------------------------------------------------------------------- *)

(* Translate HOL numerals to SMT-LIB2 integers *)
let sexp_of_numeral tm =
  sexp_mk_small_numeral (dest_small_numeral tm);;

(* Translate addition, handling nested additions *)
let sexp_of_add =
  let is_add = is_binary "+" in
  let dest_add = dest_binary "+" in
  fun tm ->
    if not(is_add tm) then failwith "sexp_of_add" else
    let args = striplist dest_add tm in
    sexp_mk_add (map sexp_of_term args);;

(* Translate less-than-or-equal *)
let sexp_of_le tm =
  let x,y = dest_binary "<=" tm in
  sexp_mk_fn "<=" [sexp_of_term x; sexp_of_term y];;

(* Translate greater-than *)
let sexp_of_gt tm =
  let x,y = dest_binary ">" tm in
  sexp_mk_fn ">" [sexp_of_term x; sexp_of_term y];;

(* ------------------------------------------------------------------------- *)
(* Default net for sexp_of_term.                                             *)
(* ------------------------------------------------------------------------- *)

let basic_sexp_of_term_net = itlist (enter [])
  [`p:A = q`, sexp_of_eq;
   `~p`,sexp_of_neg;
   `p /\ q`, sexp_of_conj;
   `p \/ q`, sexp_of_disj;
   `p ==> q`, sexp_of_imp;
   `if p then q else r:A`, sexp_of_cond;
   `!x:A. P`, sexp_of_forall;
   `?x:A. P`, sexp_of_exists;
   `NUMERAL n`, sexp_of_numeral;
   `m + n:num`, sexp_of_add;
   `m <= n:num`, sexp_of_le;
   `m > n:num`, sexp_of_gt;
   `T`, K (sexp_mk_atom "true");
   `F`, K (sexp_mk_atom "false")]
  empty_net;;

(* Initialize the global translation net *)
sexp_of_term_net := basic_sexp_of_term_net;;

(* ------------------------------------------------------------------------- *)
(* Unit tests for translation functions                                      *)
(* ------------------------------------------------------------------------- *)

assert (strsexp_of_term `a:A` = "a");;
assert (strsexp_of_term `T` = "true");;
assert (strsexp_of_term `F` = "false");;
assert (strsexp_of_term `T /\ a /\ p` = "(and true a p)");;
assert (strsexp_of_term `F \/ a \/ p` = "(or false a p)");;
assert (strsexp_of_term `T \/ a ==> p` = "(=>(or true a)p)");;
assert (strsexp_of_term `T \/ a ==> p /\ q` = "(=>(or true a)(and p q))");;
assert (strsexp_of_term `if a = b then x else a:A` = "(ite(= a b)x a)");;

assert (strsexp_of_term `!x:num y:bool z:num. y = F` =
  "(forall((x Int)(y Bool)(z Int))(=>(and(>= x 0)(>= z 0))(iff y false)))");;
assert (strsexp_of_term `!x:bool y:bool. x = F` =
  "(forall((x Bool)(y Bool))(iff x false))");;
assert (strsexp_of_term `!x:bool y:num. x = F` =
  "(forall((x Bool)(y Int))(=>(>= y 0)(iff x false)))");;

assert (strsexp_of_term `?x:num y:bool z:num. y = F` =
  "(exists((x Int)(y Bool)(z Int))(and(>= x 0)(>= z 0)(iff y false)))");;
assert (strsexp_of_term `?x:bool y:bool. x = F` =
  "(exists((x Bool)(y Bool))(iff x false))");;
assert (strsexp_of_term `?x:bool y:num. x = F` =
  "(exists((x Bool)(y Int))(and(>= y 0)(iff x false)))");;

assert (strsexp_of_term `10 + x <= y` = "(<=(+ 10 x)y)");;
assert (strsexp_of_term `5 > y+1` = "(> 5(+ y 1))");;

(* ------------------------------------------------------------------------- *)
(* SMT-LIB2 command generation helpers                                       *)
(* ------------------------------------------------------------------------- *)

(* Generate datatype declaration *)
let sexp_mk_declare_datatype sname cnames =
  let constrs = map (fun v -> sexp_mk_list [sexp_mk_atom v]) cnames in
  sexp_mk_fn "declare-datatype" [sexp_mk_atom sname; sexp_mk_list constrs];;

(* Generate constant declaration *)
let sexp_mk_declare_const v =
  let nm,ty = dest_var v in
  sexp_mk_fn "declare-const" [sexp_mk_atom nm; sexp_of_type ty];;

(* Test *)
assert (string_of_sexp(sexp_mk_declare_const `x:num`) =
        "(declare-const x Int)");;

(* Generate assertion for non-negativity constraint *)
let sexp_mk_assert_nonneg v =
  sexp_mk_fn "assert" [sexp_mk_nonneg v];;

(* Generate get-value command for specified variables *)
let sexp_mk_get_values (vars : string list) : Sexplib.Sexp.t list =
  if vars = [] then [] else
  [sexp_mk_fn "get-value" [sexp_mk_list (map sexp_mk_atom vars)]];;

(* ------------------------------------------------------------------------- *)
(* High-level SMT problem generation into smtlib2 file                       *)
(* ------------------------------------------------------------------------- *)

(* Generate complete SMT-LIB2 problem for satisfiability checking *)
let sexp_mk_check_formula (vars:term list) (ptm:term) : Sexplib.Sexp.t list =
  let decl_sexps = map sexp_mk_declare_const vars in
  let bound_sexps = mapfilter sexp_mk_assert_nonneg vars in
  let assert_sexp = sexp_mk_fn "assert" [sexp_of_term ptm] in
  let check_sexp = sexp_mk_fn "check-sat" [] in
  decl_sexps @ bound_sexps @ [assert_sexp; check_sexp];;

(* Generate SMT problem for theorem proving (checking unsatisfiability of negation) *)
let sexp_mk_prove (ptm:term) : Sexplib.Sexp.t list =
  let vars = sort (<) (frees ptm) in
  sexp_mk_check_formula vars (mk_neg ptm);;

(* Generate SMT problem for model finding (with variable value extraction) *)
let sexp_mk_find_model (ptm:term) : Sexplib.Sexp.t list =
  let vars = sort (<) (frees ptm) in
  let check_sexps = sexp_mk_check_formula vars ptm
  and getvals_sexps = sexp_mk_get_values (map name_of vars) in
  check_sexps @ getvals_sexps;;

(* ------------------------------------------------------------------------- *)
(* File generation utilities                                                 *)
(* ------------------------------------------------------------------------- *)
(*Commented out for future improvements 
(** Generate SMT-LIB2 file for theorem proving *)
let generate_prove_file ptm filename =
  let sexps = sexp_mk_prove ptm in
  write_sexps_to_file filename sexps;;

(** Generate SMT-LIB2 file for model finding *)
let generate_model_file ptm filename =
  let sexps = sexp_mk_find_model ptm in
  write_sexps_to_file filename sexps;;

(* Example usage:
   generate_prove_file `!x. x + 0 = x` "prove_identity.smt2";;
   generate_model_file `?x y. x + y = 10 /\ x > y` "find_solution.smt2";;
*)


(*
let generate_smtlib2 ptm fname getvals =
  let getvals_sexps = sexp_mk_get_values (map name_of vars) in
  let getvals_sexps = if getvals then getvals_sexps else [] in
  let path = "/workspaces/hol-light-devcontainer/code/HOL-Ants" in
  let pathname = path^"/"^fname in
  write_sexps_to_file pathname sexps;;

let generate_smtlib2 ptm fname getvals =
  let vars = sort (<) (frees ptm) in
  let decl_sexps = map sexp_mk_declare_const vars in
  let bound_sexps = mapfilter sexp_mk_assert_nonneg vars in
  let assert_sexp = sexp_mk_fn "assert" [sexp_of_term ptm] in
  let check_sexp = sexp_mk_fn "check-sat" [] in
  let getvals_sexps = sexp_mk_get_values (map name_of vars) in
  let getvals_sexps = if getvals then getvals_sexps else [] in
  let sexps = decl_sexps @
              bound_sexps @
              [assert_sexp; check_sexp] @ getvals_sexps in
  let path = "/workspaces/hol-light-devcontainer/code/HOL-Ants" in
  let pathname = path^"/"^fname in
  write_sexps_to_file pathname sexps;;
  *)
*)