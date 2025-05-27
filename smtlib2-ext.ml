(* ========================================================================= *)
(* SMT-LIB2 Interface for HOL Light                                          *)
(* This module provides functionality to translate (some) HOL terms into     *)
(* SMT-LIB2 format for automated theorem proving using SMT solvers like      *)
(* Z3, CVC4                                                                  *)
(* ========================================================================= *)

#use "topfind";;
#require "sexplib";;
#install_printer Sexplib.Sexp.pp_hum;;

(* ------------------------------------------------------------------------- *)
(* Basic S-expression manipulation functions                                 *)
(* These functions provide low-level operations for creating and handling    *)
(* S-expressions (symbolic expressions) used in SMT-LIB2 format              *)
(* ------------------------------------------------------------------------- *)

(* Pretty printer for S-expressions with human-readable formatting *)
let sexp_pp = Sexplib.Sexp.pp_hum;;

(* Convert S-expression to string representation *)
let string_of_sexp = Sexplib.Sexp.to_string;;

(* Create a list S-expression from a list of S-expressions *)
let sexp_mk_list (l : Sexplib.Sexp.t list) : Sexplib.Sexp.t =
  Sexplib.Sexp.List l;;

(* Remove prime suffixes from variable names and replace with underscore notation *)
(* This handles HOL's variable naming convention where x', x'', x''' become x_1, x_2, x_3 *)
let strip_prime s =
  let n = String.length s in
  (* Find the index where primes start (counting from the end) *)
  let rec findidx i =
    if i >= 0 && String.get s i = '\''
    then findidx (i-1)  (* Keep going back while we see primes *)
    else i in           (* Stop when we hit a non-prime character *)
  let i = findidx (n-1) + 1 in  (* Index after the last non-prime char *)
  let m = n - i in              (* Number of primes *)
  if m = 0 then s else          (* No primes, return original *)
  String.sub s 0 i^"_"^string_of_int m;;  (* Replace primes with _<count> *)

(* Test cases for strip_prime function *)
assert (strip_prime "a" = "a");;     (* No primes *)
assert (strip_prime "x'''" = "x_3");; (* Three primes become _3 *)

(* Create an atomic S-expression (leaf node) from a string *)
let sexp_mk_atom (s : string) : Sexplib.Sexp.t =
  Sexplib.Sexp.Atom (strip_prime s);;

(* Create a function application S-expression: (function_name arg1 arg2 ...) *)
let sexp_mk_fn (s : string) (l : Sexplib.Sexp.t list) : Sexplib.Sexp.t =
  sexp_mk_list (sexp_mk_atom s :: l);;

(* Print S-expression to a formatter with newline *)
let pp_sexp fmt sexp =
  Format.fprintf fmt "%a@." Sexplib.Sexp.pp_hum sexp;;

(* Print S-expression to standard output *)
let print_sexp sexp = pp_sexp Format.std_formatter;;

(* Write a list of S-expressions to a file (used for generating SMT-LIB2 files) *)
(* Includes proper error handling to ensure file is closed even if writing fails *)
let write_sexps_to_file filename sexps =
  let oc = open_out filename in
  try
    let fmt = Format.formatter_of_out_channel oc in
    do_list (pp_sexp fmt) sexps;  (* Write each S-expression *)
    close_out oc
  with e ->
    close_out oc;  (* Ensure file is closed even on error *)
    raise e;;

(* ------------------------------------------------------------------------- *)
(* Example usage of basic S-expression functions                             *)
(* ------------------------------------------------------------------------- *)

(* Create and display a simple list S-expression: (a b) *)
let mysexp = sexp_mk_list[sexp_mk_atom "a"; sexp_mk_atom "b"];;
Format.fprintf Format.std_formatter "%a@." sexp_pp mysexp;;

(* ------------------------------------------------------------------------- *)
(* Specialized S-expression constructors for common logical operations       *)
(* These functions handle the SMT-LIB2 syntax for boolean and arithmetic     *)
(* operations, including edge cases for empty and single-element lists       *)
(* ------------------------------------------------------------------------- *)

(* Create conjunction (AND): handles empty list as 'true', single element as itself *)
let sexp_mk_conj l =
  match l with
  | [] -> sexp_mk_atom "true"     (* Empty conjunction is true *)
  | [e] -> e                      (* Single element conjunction is the element itself *)
  | l -> sexp_mk_fn "and" l;;     (* Multiple elements: (and e1 e2 ...) *)

(* Create disjunction (OR): handles empty list as 'false', single element as itself *)
let sexp_mk_disj l =
  match l with
  | [] -> sexp_mk_atom "false"    (* Empty disjunction is false *)
  | [e] -> e                      (* Single element disjunction is the element itself *)
  | l -> sexp_mk_fn "or" l;;      (* Multiple elements: (or e1 e2 ...) *)

(* Create addition: handles empty list as '0', single element as itself *)
let sexp_mk_add l =
  match l with
  | [] -> sexp_mk_atom "0"        (* Empty sum is 0 *)
  | [e] -> e                      (* Single element sum is the element itself *)
  | l -> sexp_mk_fn "+" l;;       (* Multiple elements: (+ e1 e2 ...) *)

(* Create small integer numeral S-expression *)
let sexp_mk_small_numeral n =
  sexp_mk_atom (string_of_int n);;

(* ------------------------------------------------------------------------- *)
(* Net-based translation infrastructure from HOL terms to S-expressions      *)
(* This uses HOL Light's "net" data structure for efficient pattern matching *)
(* to determine how to translate different types of HOL terms                *)
(* ------------------------------------------------------------------------- *)

(* Global reference to the net that maps HOL term patterns to translation functions *)
let sexp_of_term_net : (term-> Sexplib.Sexp.t) net ref =
  ref empty_net;;

(* Main function to translate a HOL term to S-expression *)
(* Uses pattern matching via the net to find appropriate translation function *)
let sexp_of_term tm =
  let l = lookup tm !sexp_of_term_net in  (* Find matching translation functions *)
  try tryfind (fun f -> f tm) l with Failure s ->  (* Try each function until one works *)
  (* Fallback: if no pattern matches, handle variables and constants by name *)
  if is_var tm || is_const tm then sexp_mk_atom (name_of tm) else
  failwith ("sexp_of_term: "^string_of_term tm);;

(* Convenience function: translate HOL term to S-expression string *)
let strsexp_of_term = string_of_sexp o sexp_of_term;;

(* ------------------------------------------------------------------------- *)
(* Translation of HOL types to SMT-LIB2 sort names                           *)
(* Maps HOL type names to their SMT-LIB2 equivalents                         *)
(* ------------------------------------------------------------------------- *)

let sexp_of_type ty =
  match fst(dest_type ty) with
  | "bool" -> sexp_mk_atom "Bool"        (* HOL bool -> SMT Bool *)
  | "num" -> sexp_mk_atom "Int"          (* HOL num -> SMT Int *)
  | "real" -> sexp_mk_atom "Real"        (* HOL real -> SMT Real *)
  | "position" -> sexp_mk_atom "Position" (* Custom type *)
  | s -> failwith ("sexp_of_type: Unknown type: "^s);;

(* Alternative version that returns a default instead of failing *)
let sexp_of_type_safe ty =
  match fst(dest_type ty) with
  | "bool" -> sexp_mk_atom "Bool"        
  | "num" -> sexp_mk_atom "Int"          
  | "real" -> sexp_mk_atom "Real"        
  | "position" -> sexp_mk_atom "Position"
  | s -> sexp_mk_atom s;;  (* Use the type name as-is for unknown types *)

(* ------------------------------------------------------------------------- *)
(* Translation of equality expressions                                       *)
(* Handles both propositional equivalence (iff) and term equality (=)        *)
(* ------------------------------------------------------------------------- *)

let sexp_of_eq tm =
  let x,y = dest_eq tm in           (* Extract left and right sides of equality *)
  let e = sexp_of_term x
  and f = sexp_of_term y in
  (* Use 'iff' for boolean equality, '=' for other types *)
  let fn = if type_of x = bool_ty then "iff" else "=" in
  sexp_mk_fn fn [e; f];;

(* ------------------------------------------------------------------------- *)
(* Translation of boolean expressions                                        *)
(* Handles negation, conjunction, disjunction, and implication               *)
(* ------------------------------------------------------------------------- *)

(* Translate negation: ~P becomes (not P) *)
let sexp_of_neg tm =
  sexp_mk_fn "not" [sexp_of_term (dest_neg tm)];;

(* Translate conjunction: P /\ Q /\ R becomes (and P Q R) *)
let sexp_of_conj tm =
  if not(is_conj tm) then failwith "sexp_of_conj" else
  let args = striplist dest_conj tm in  (* Flatten nested conjunctions *)
  sexp_mk_conj (map sexp_of_term args);;

(* Translate disjunction: P \/ Q \/ R becomes (or P Q R) *)
let sexp_of_disj tm =
  if not(is_disj tm) then failwith "sexp_of_disj" else
  let args = striplist dest_disj tm in  (* Flatten nested disjunctions *)
  sexp_mk_disj (map sexp_of_term args);;

(* Translate implication: P ==> Q becomes (=> P Q) *)
let sexp_of_imp tm =
  let p,q = dest_imp tm in
  sexp_mk_fn "=>" [sexp_of_term p; sexp_of_term q];;

(* ------------------------------------------------------------------------- *)
(* Translation of conditional expressions                                    *)
(* HOL's "if-then-else" becomes SMT-LIB2's "ite" (if-then-else)              *)
(* ------------------------------------------------------------------------- *)

let sexp_of_cond tm =
  let b,(s,t) = dest_cond tm in    (* Extract condition, then-branch, else-branch *)
  sexp_mk_fn "ite" [sexp_of_term b;    (* (ite condition then-part else-part) *)
                    sexp_of_term s;
                    sexp_of_term t];;

(* ------------------------------------------------------------------------- *)
(* Translation of quantifiers (forall and exists)                            *)
(* Handles variable declarations and non-negativity constraints for numerics *)
(* ------------------------------------------------------------------------- *)

(* Create quantified variable declaration: (variable_name Type) *)
let mk_quant_var v =
  let nm,ty = dest_var v in
  sexp_mk_list[sexp_mk_atom nm;
               sexp_of_type ty];;

(* Create non-negativity constraint for numeric variables: (>= var 0) *)
(* SMT-LIB2 integers are unbounded, but HOL's num type is non-negative *)
let sexp_mk_nonneg =
  let sexp_0 = sexp_mk_atom "0" in
  fun v ->
    let nm,ty = dest_var v in
    let nty,_ = dest_type ty in
    if nty <> "num" then failwith "sexp_mk_nonneg" else
    sexp_mk_fn ">=" [sexp_mk_atom nm; sexp_0];;

(* Translate universal quantification: !x y. P becomes (forall ((x Type)(y Type)) P) *)
let sexp_of_forall tm =
  let vl,btm = strip_forall tm in  (* Extract quantified variables and body *)
  if vl = [] then failwith "sexp_of_forall" else
  let vsexps = sexp_mk_list (map mk_quant_var vl) in  (* Variable declarations *)
  let bounds = mapfilter sexp_mk_nonneg vl in         (* Non-negativity constraints *)
  let bdy = sexp_of_term btm in
  (* If there are bounds, add them as premises: (=> (and bounds...) body) *)
  let bdy = if bounds = [] then bdy else
            sexp_mk_fn "=>" [sexp_mk_conj bounds; bdy] in
  sexp_mk_fn "forall"  [vsexps; bdy];;

(* Translate existential quantification: ?x y. P becomes (exists ((x Type)(y Type)) P) *)
let sexp_of_exists tm =
  let vl,btm = strip_exists tm in  (* Extract quantified variables and body *)
  if vl = [] then failwith "sexp_of_exists" else
  let vsexps = sexp_mk_list (map mk_quant_var vl) in  (* Variable declarations *)
  let bounds = mapfilter sexp_mk_nonneg vl in         (* Non-negativity constraints *)
  let bdy = sexp_of_term btm in
  (* For exists, bounds become additional conjuncts: (and bounds... body) *)
  let bdy = if bounds = [] then bdy else
            sexp_mk_conj (bounds @ [bdy]) in
  sexp_mk_fn "exists"  [vsexps; bdy];;

(* ------------------------------------------------------------------------- *)
(* Translation of arithmetic expressions                                     *)
(* Handles numerals, addition, and comparison operations                     *)
(* ------------------------------------------------------------------------- *)

(* Translate HOL numerals to SMT-LIB2 integers *)
let sexp_of_numeral tm =
  sexp_mk_small_numeral (dest_small_numeral tm);;

(* Translate addition: x + y + z becomes (+ x y z) *)
let sexp_of_add =
  let is_add = is_binary "+" in
  let dest_add = dest_binary "+" in
  fun tm ->
    if not(is_add tm) then failwith "sexp_of_add" else
    let args = striplist dest_add tm in  (* Flatten nested additions *)
    sexp_mk_add (map sexp_of_term args);;

(* Translate less-than-or-equal: x <= y becomes (<= x y) *)
let sexp_of_le tm =
  let x,y = dest_binary "<=" tm in
  sexp_mk_fn "<=" [sexp_of_term x; sexp_of_term y];;

(* Translate greater-than: x > y becomes (> x y) *)
let sexp_of_gt tm =
  let x,y = dest_binary ">" tm in
  sexp_mk_fn ">" [sexp_of_term x; sexp_of_term y];;

(* Helper function to create multiplication (similar to addition) *)
let sexp_mk_mul l =
  match l with
  | [] -> sexp_mk_atom "1"        (* Empty product is 1 *)
  | [e] -> e                      (* Single element *)
  | l -> sexp_mk_fn "*" l;;       (* Multiple elements *)

(* Helper function to create subtraction: (- a b) *)
let sexp_mk_sub (a, b) =
  sexp_mk_fn "-" [a; b];;

(* ------------------------------------------------------------------------- *)
(* Default translation net setup                                             *)
(* This registers all the translation functions with their corresponding     *)
(* HOL term patterns for efficient pattern matching                          *)
(* ------------------------------------------------------------------------- *)

(* Build the default net with all translation patterns and functions *)
let basic_sexp_of_term_net = itlist (enter [])
  [`p:A = q`, sexp_of_eq;           (* Equality *)
   `~p`,sexp_of_neg;                (* Negation *)
   `p /\ q`, sexp_of_conj;          (* Conjunction *)
   `p \/ q`, sexp_of_disj;          (* Disjunction *)
   `p ==> q`, sexp_of_imp;          (* Implication *)
   `if p then q else r:A`, sexp_of_cond;  (* Conditional *)
   `!x:A. P`, sexp_of_forall;       (* Universal quantification *)
   `?x:A. P`, sexp_of_exists;       (* Existential quantification *)
   `NUMERAL n`, sexp_of_numeral;    (* Numeric literals *)
   `m + n:num`, sexp_of_add;        (* Addition *)
   `m <= n:num`, sexp_of_le;        (* Less-than-or-equal *)
   `m > n:num`, sexp_of_gt;         (* Greater-than *)
   `T`, K (sexp_mk_atom "true");    (* Boolean true *)
   `F`, K (sexp_mk_atom "false")]   (* Boolean false *)
  empty_net;;

(* Install the default translation net *)
sexp_of_term_net := basic_sexp_of_term_net;;

(* ------------------------------------------------------------------------- *)
(* Test cases to verify correct translation                                  *)
(* These assertions ensure the translation functions work as expected        *)
(* ------------------------------------------------------------------------- *)

(* Basic term translation tests *)
assert (strsexp_of_term `a:A` = "a");;                    (* Variable *)
assert (strsexp_of_term `T` = "true");;                   (* True *)
assert (strsexp_of_term `F` = "false");;                  (* False *)
assert (strsexp_of_term `T /\ a /\ p` = "(and true a p)");;     (* Conjunction *)
assert (strsexp_of_term `F \/ a \/ p` = "(or false a p)");;     (* Disjunction *)
assert (strsexp_of_term `T \/ a ==> p` = "(=>(or true a)p)");;  (* Implication with disjunction *)
assert (strsexp_of_term `T \/ a ==> p /\ q` = "(=>(or true a)(and p q))");; (* Complex formula *)
assert (strsexp_of_term `if a = b then x else a:A` = "(ite(= a b)x a)");; (* Conditional *)

(* Quantifier translation tests *)
assert (strsexp_of_term `!x:num y:bool z:num. y = F` =
  "(forall((x Int)(y Bool)(z Int))(=>(and(>= x 0)(>= z 0))(iff y false)))");;
assert (strsexp_of_term `!x:bool y:bool. x = F` =
  "(forall((x Bool)(y Bool))(iff x false))");;
assert (strsexp_of_term `!x:bool y:num. x = F` =
  "(forall((x Bool)(y Int))(=>(>= y 0)(iff x false)))");;

assert (strsexp_of_term `?x:num y:bool z:num. y = F` =
  "(exists((x Int)(y Bool)(z Int))(and(>= x 0)(>= z 0)(iff y false)))");;
assert (strsexp_of_term `?x:bool y:bool. x = F` =
  "(exists((x Bool)(y Bool))(iff y false))");;
assert (strsexp_of_term `?x:bool y:num. x = F` =
  "(exists((x Bool)(y Int))(and(>= y 0)(iff x false)))");;

(* Arithmetic translation tests *)
assert (strsexp_of_term `10 + x <= y` = "(<=(+ 10 x)y)");;      (* Addition with comparison *)
assert (strsexp_of_term `5 > y+1` = "(> 5(+ y 1))");;          (* Comparison with addition *)

(* ------------------------------------------------------------------------- *)
(* Additional helper functions for SMT-LIB2 command generation               *)
(* These functions create SMT-LIB2 commands for declarations and queries     *)
(* ------------------------------------------------------------------------- *)

(* Create datatype declaration command *)
(* Example: (declare-datatype Color ((Red) (Green) (Blue))) *)
let sexp_mk_declare_datatype sname cnames =
  let constrs = map (fun v -> sexp_mk_list [sexp_mk_atom v]) cnames in
  sexp_mk_fn "declare-datatype" [sexp_mk_atom sname; sexp_mk_list constrs];;

(* Create constant declaration command *)
(* Example: (declare-const x Int) *)
let sexp_mk_declare_const v =
  let nm,ty = dest_var v in
  sexp_mk_fn "declare-const" [sexp_mk_atom nm; sexp_of_type ty];;

(* Test constant declaration *)
assert (string_of_sexp(sexp_mk_declare_const `x:num`) =
        "(declare-const x Int)");;

(* Create assertion for non-negativity constraint *)
(* Example: (assert (>= x 0)) *)
let sexp_mk_assert_nonneg v =
  sexp_mk_fn "assert" [sexp_mk_nonneg v];;

(* Create get-value command for retrieving variable assignments *)
(* Example: (get-value (x y z)) *)
let sexp_mk_get_values (vars : string list) : Sexplib.Sexp.t list =
  if vars = [] then [] else
  [sexp_mk_fn "get-value" [sexp_mk_list (map sexp_mk_atom vars)]];;

(* ------------------------------------------------------------------------- *)
(* Main procedure for generating complete SMT-LIB2 files                     *)
(* This function takes a HOL formula and produces a complete SMT-LIB2 file   *)
(* that can be fed to an SMT solver                                          *)
(* ------------------------------------------------------------------------- *)

(* Generate SMT-LIB2 file with user-specified directory path *)
let generate_smtlib2_with_path ptm fname getvals path =
  (* Validate inputs *)
  if fname = "" then failwith "generate_smtlib2_with_path: filename cannot be empty" else
  
  (* Extract all free variables from the formula (these become SMT constants) *)
  let vars = sort (<) (frees ptm) in
  
  (* Generate constant declarations for all variables *)
  let decl_sexps = map sexp_mk_declare_const vars in
  
  (* Generate non-negativity constraints for numeric variables *)
  let bound_sexps = mapfilter sexp_mk_assert_nonneg vars in
  
  (* Create the main assertion for the formula *)
  let assert_sexp = sexp_mk_fn "assert" [sexp_of_term ptm] in
  
  (* Add check-sat command to ask solver for satisfiability *)
  let check_sexp = sexp_mk_fn "check-sat" [] in
  
  (* Optionally add get-value commands to retrieve variable assignments *)
  let getvals_sexps = if getvals && vars <> [] then 
                        sexp_mk_get_values (map name_of vars) 
                      else [] in
  
  (* Combine all commands in proper order *)
  let sexps = decl_sexps @        (* Variable declarations *)
              bound_sexps @       (* Non-negativity constraints *)
              [assert_sexp; check_sexp] @ getvals_sexps in (* Main query *)
  
  (* Construct full pathname, handling path separator properly *)
  let pathname = 
    if path = "" || path = "." then fname
    else if String.get path (String.length path - 1) = '/' then path ^ fname
    else path ^ "/" ^ fname in
  
  (* Write to file *)
  write_sexps_to_file pathname sexps;;

(* Convenience function that writes to current directory *)
let generate_smtlib2 ptm fname getvals =
  generate_smtlib2_with_path ptm fname getvals ".";;

(* Generate SMT-LIB2 with additional solver options *)
let generate_smtlib2_with_options ptm fname getvals path options =
  (* Standard generation *)
  generate_smtlib2_with_path ptm fname getvals path;
  
  (* Optionally add solver-specific options at the beginning *)
  if options <> [] then
    let oc = open_out (path ^ "/" ^ fname ^ ".with_options") in
    try
      let fmt = Format.formatter_of_out_channel oc in
      (* Write options first *)
      do_list (pp_sexp fmt) options;
      (* Then append the original content *)
      let ic = open_in (path ^ "/" ^ fname) in
      try
        while true do
          let line = input_line ic in
          Format.fprintf fmt "%s@." line
        done
      with End_of_file -> close_in ic;
      close_out oc
    with e ->
      close_out oc;
      raise e;;

(* Example of how to use with custom path and options: *)
(* let opts = [sexp_mk_fn "set-option" [sexp_mk_atom ":timeout"; sexp_mk_atom "1000"]] in *)
(* generate_smtlib2_with_options my_formula "problem.smt2" true "/path/to/output/dir" opts;; *)
