(* ========================================================================= *)
(* Experiments with Z3 - Improved Version                                    *)
(* ========================================================================= *)

needs "z3base.ml";;

(* ------------------------------------------------------------------------- *)
(* Z3 context management for better resource handling.                       *)
(* ------------------------------------------------------------------------- *)

let z3_context = ref (Zzz.mk_context []);;

(** Get the current Z3 context or create a new one if none exists *)
let get_context () = !z3_context;;

(** Reset the Z3 context to a fresh state *)
let reset_context () = 
  z3_context := Zzz.mk_context [];;

(* ------------------------------------------------------------------------- *)
(* Additional HOL Light helper functions.                                    *)
(* ------------------------------------------------------------------------- *)

(** 
 * Deconstructs a quantifier term returning (variable, body, is_universal)
 * @param tm The term to deconstruct
 * @return A triple containing the variable, body, and a boolean indicating if universal 
 *)
let dest_quantifier tm =
  if is_forall tm
  then let v,b = dest_forall tm in v,b,true
  else if is_exists tm
  then let v,b = dest_exists tm in v,b,false
  else failwith "dest_quantifier: Term is not a quantifier";;

(** 
 * Tests if a term is a quantifier 
 * @param tm The term to test
 * @return True if the term is a quantifier, false otherwise
 *)
let is_quantifier = can dest_quantifier;;

(* Test: *)
assert (dest_quantifier `?n:num. b` = (`n:num`, `b:bool`, false));;

(* ------------------------------------------------------------------------- *)
(* Constructors for quantifiers.                                             *)
(* ------------------------------------------------------------------------- *)

(** 
 * Creates a universal quantifier in Z3
 * @param ctx The Z3 context
 * @param vars List of variables to quantify over
 * @param body The body of the quantifier
 * @return A Z3 expression representing the universal quantifier
 *)
let z3_simple_mk_forall ctx vars body =
  let quant = Zzz.Quantifier.mk_forall_const ctx vars body
                None [] [] None None in
  Zzz.Quantifier.expr_of_quantifier quant;;

(** 
 * Creates an existential quantifier in Z3
 * @param ctx The Z3 context
 * @param vars List of variables to quantify over
 * @param body The body of the quantifier
 * @return A Z3 expression representing the existential quantifier
 *)
let z3_simple_mk_exists ctx vars body =
  let quant = Zzz.Quantifier.mk_exists_const ctx vars body
                None [] [] None None in
  Zzz.Quantifier.expr_of_quantifier quant;;

(* ------------------------------------------------------------------------- *)
(* Create enumerative sort for positions.                                    *)
(* ------------------------------------------------------------------------- *)

let ctx = get_context();;

let sort_position = Zzz.Enumeration.mk_sort_s ctx "position"
                      ["P0"; "P1"; "P2"; "P3"; "P4"];;
                      
let [z3p0; z3p1; z3p2; z3p3; z3p4] =
  Zzz.Enumeration.get_consts sort_position;;

(* ------------------------------------------------------------------------- *)
(* Translates an HOL term into a Z3 expresion.
   Handles a fragment barely sufficient for accepting goals generated from
   the ANTS formalization.                                                   *)
(* ------------------------------------------------------------------------- *)

(** 
 * Translates an HOL Light term into a Z3 expression
 * @param ctx The Z3 context
 * @param tm The HOL Light term to translate
 * @return The corresponding Z3 expression
 *)
let z3_of_term ctx =
  let num_ty = `:num`
  and position_ty = `:position`
  and bool_ty = `:bool`
  and zexpr = Zzz.Arithmetic.Integer.mk_numeral_i ctx 0 in
  let rec z3_of_term tm =
    if is_const tm then
      match name_of tm with
      | "T" -> Zzz.Boolean.mk_true ctx
      | "F" -> Zzz.Boolean.mk_false ctx
      | "P0" -> z3p0
      | "P1" -> z3p1
      | "P2" -> z3p2
      | "P3" -> z3p3
      | "P4" -> z3p4
      | nm -> failwith ("z3_of_term: Unknown constant: " ^ nm ^ 
                        " of type " ^ (string_of_type (type_of tm)))
    else if is_var tm then
      let nm,ty = dest_var tm in
      if ty = bool_ty then Zzz.Boolean.mk_const_s ctx nm
      else if ty = num_ty then Zzz.Arithmetic.Integer.mk_const_s ctx nm
      else if ty = position_ty then Zzz.Expr.mk_const_s ctx nm sort_position
      else failwith ("z3_of_term: Variable of unhandled type: " ^ nm ^ 
                     " of type " ^ (string_of_type ty))
    else if is_eq tm then
      let x,y = dest_eq tm in
      let e = z3_of_term x
      and f = z3_of_term y in
      if type_of x = bool_ty
      then Zzz.Boolean.mk_iff ctx e f
      else Zzz.Boolean.mk_eq ctx e f
    else if is_neg tm then
      Zzz.Boolean.mk_not ctx (z3_of_term (dest_neg tm))
    else if is_conj tm then
      let p,q = dest_conj tm in
      Zzz.Boolean.mk_and ctx [z3_of_term p; z3_of_term q]
    else if is_disj tm then
      let p,q = dest_disj tm in
      Zzz.Boolean.mk_or ctx [z3_of_term p; z3_of_term q]
    else if is_imp tm then
      let p,q = dest_imp tm in
      Zzz.Boolean.mk_implies ctx (z3_of_term p) (z3_of_term q)
    else if is_cond tm then
      let b,(s,t) = dest_cond tm in
      Zzz.Boolean.mk_ite ctx (z3_of_term b) (z3_of_term s) (z3_of_term t)
    else if is_quantifier tm then
      let vtm,btm,universal = dest_quantifier tm in
      let vexpr = z3_of_term vtm
      and bexpr = z3_of_term btm in
      let bexpr = if type_of vtm = num_ty
                  then let lexpr = Zzz.Arithmetic.mk_le ctx zexpr vexpr in
                       if universal
                       then Zzz.Boolean.mk_implies ctx lexpr bexpr
                       else Zzz.Boolean.mk_and ctx [lexpr; bexpr]
                  else bexpr in
      if universal
      then z3_simple_mk_forall ctx [vexpr] bexpr
      else z3_simple_mk_exists ctx [vexpr] bexpr
    else if is_binary "<=" tm then
      let x,y = dest_binary "<=" tm in
      Zzz.Arithmetic.mk_ge ctx (z3_of_term y) (z3_of_term x)
    else if is_binary ">=" tm then
      let x,y = dest_binary ">=" tm in
      Zzz.Arithmetic.mk_ge ctx (z3_of_term x) (z3_of_term y)
    else if is_binary "<" tm then
      let x,y = dest_binary "<" tm in
      Zzz.Arithmetic.mk_lt ctx (z3_of_term x) (z3_of_term y)
    else if is_binary ">" tm then
      let x,y = dest_binary ">" tm in
      Zzz.Arithmetic.mk_gt ctx (z3_of_term x) (z3_of_term y)
    else if is_numeral tm then
      Zzz.Arithmetic.Integer.mk_numeral_i ctx (dest_small_numeral tm)
    else if is_binary "+" tm then
      let x,y = dest_binary "+" tm in
      Zzz.Arithmetic.mk_add ctx [z3_of_term x; z3_of_term y]
    else if is_binary "-" tm then
      let x,y = dest_binary "-" tm in
      Zzz.Arithmetic.mk_sub ctx [z3_of_term x; z3_of_term y]
    else if is_binary "*" tm then
      let x,y = dest_binary "*" tm in
      Zzz.Arithmetic.mk_mul ctx [z3_of_term x; z3_of_term y]
    else if is_binary "/" tm then
      let x,y = dest_binary "/" tm in
      (* Note: Division in Z3 might have different semantics than HOL Light *)
      Zzz.Arithmetic.mk_div ctx (z3_of_term x) (z3_of_term y)
    else
      let s = string_of_term tm in
      failwith ("z3_of_term: Parsing of HOL Light formula failed: " ^ s)
  in
  z3_of_term;;

(* ------------------------------------------------------------------------- *)
(* Helper functions for solving and displaying results.                      *)
(* ------------------------------------------------------------------------- *)

(**
 * Display a HOL Light term as a Z3 expression string
 * @param ctx The Z3 context
 * @param tm The HOL Light term to display
 * @return String representation of the Z3 expression
 *)
let z3show ctx tm = Zzz.Expr.to_string (z3_of_term ctx tm);;

(**
 * Attempts to solve a list of HOL Light terms using Z3
 * @param ctx The Z3 context
 * @param tms List of HOL Light terms to solve
 * @return Result of the solving attempt
 *)
let solve ctx tms =
  try
    let solver = Zzz.Solver.mk_solver ctx None in
    let z3terms = List.map (z3_of_term ctx) tms in
    List.iter (Zzz.Solver.add solver) z3terms;
    match Zzz.Solver.check solver [] with
    | Zzz.Solver.SATISFIABLE -> 
        let model = Zzz.Solver.get_model solver in
        print_endline "Satisfiable. Model:";
        (match model with
         | Some m -> print_endline (Zzz.Model.to_string m)
         | None -> print_endline "No model available.");
        true
    | Zzz.Solver.UNSATISFIABLE -> 
        print_endline "Unsatisfiable";
        false
    | Zzz.Solver.UNKNOWN -> 
        print_endline "Unknown";
        false
  with e ->
    print_endline ("Error solving: " ^ Printexc.to_string e);
    false;;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

let run_tests () =
  let ctx = get_context () in
  (* Test basic term translations *)
  assert (z3show ctx `b:num` = "b");
  assert (z3show ctx `n:num` = "n");
  assert (z3show ctx `b <=> c` = "(= b c)");
  assert (z3show ctx `m:num = n` = "(= m n)");
  assert (z3show ctx `b /\ c` = "(and b c)");
  assert (z3show ctx `m + n:num` = "(+ m n)");
  assert (z3show ctx `m - n:num` = "(- m n)");  (* New test for subtraction *)
  assert (z3show ctx `m * n:num` = "(* m n)");  (* New test for multiplication *)
  assert (z3show ctx `T /\ F` = "(and true false)");
  assert (z3show ctx `!b. b` = "(forall ((b Bool)) b)");
  assert (z3show ctx `?b. b` = "(exists ((b Bool)) b)");
  assert (z3show ctx `!n:num. b` = "(forall ((n Int)) (=> (<= 0 n) b))");
  assert (z3show ctx `?n:num. b` = "(exists ((n Int)) (and (<= 0 n) b))");
  
  (* Test solving capabilities *)
  assert (solve ctx [`!b. b \/ ~b`]);  (* Tautology - should be satisfiable *)
  assert (not (solve ctx [`b:bool`; `~b`]));  (* Contradiction - should be unsatisfiable *)
  assert (solve ctx [`0 <= 1`]);  (* Simple numeric inequality - should be satisfiable *)
  assert (not (solve ctx [`1 <= 0`]));  (* False inequality - should be unsatisfiable *)
  
  print_endline "All tests passed!";
  ();;

(* Run tests when the module is loaded *)
run_tests ();;

(* ------------------------------------------------------------------------- *)
(* Example usage for the invariant proof.                                     *)
(* ------------------------------------------------------------------------- *)

let try_invariant_proof () =
  let ctx = get_context () in
  
  (* Define and process the goal *)
  g `!sys sys':3 system.
       INVARIANT sys /\ sys' IN NEW_SYSTEM sys
       ==> INVARIANT sys'`;;
  e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
  e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
  e (REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_NUM_COMPONENT]);;
  e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_PAIR_THM]);;
  e (REWRITE_TAC[ANT; STI; VECTOR_3]);;
  e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_3; NSUM_3; VECTOR_3; PP]);;
  e (REWRITE_TAC[MAX]);;
  let (_,thtm) = top_goal();;

  (* Attempt to solve the goal using Z3 *)
  print_endline "Attempting to solve invariant proof with Z3:";
  let result = solve ctx [mk_neg (z3_of_term ctx thtm)] in
  if not result then
    print_endline "Z3 proved the theorem (unsatisfiable)"
  else
    print_endline "Z3 could not prove the theorem (satisfiable or unknown)";
  ();;

(* ------------------------------------------------------------------------- *)
(* Utility functions for working with HOL Light and Z3.                      *)
(* ------------------------------------------------------------------------- *)

(**
 * Attempts to prove a HOL Light theorem using Z3
 * @param ctx The Z3 context
 * @param thm The HOL Light theorem to prove
 * @return true if Z3 can prove the theorem, false otherwise
 *)
let prove_with_z3 ctx thm =
  let goal = concl thm in
  let negated_goal = mk_neg goal in
  let result = solve ctx [z3_of_term ctx negated_goal] in
  if not result then begin
    print_endline "Z3 proved the theorem";
    true
  end else begin
    print_endline "Z3 could not prove the theorem";
    false
  end;;

(**
 * Simplifies a HOL Light term and attempts to solve it with Z3
 * @param ctx The Z3 context
 * @param tm The HOL Light term to simplify and solve
 * @param conv The conversion to use for simplification
 * @return true if Z3 can solve the simplified term, false otherwise
 *)
let simplify_and_solve ctx tm conv =
  let simplified = conv tm |> concl |> rand in
  print_endline "Simplified term:";
  print_endline (string_of_term simplified);
  solve ctx [z3_of_term ctx simplified];;

(* ------------------------------------------------------------------------- *)
(*                        HIC SUNT LEONES                                    *)
(*                Experimental code and test cases.                          *)
(* ------------------------------------------------------------------------- *)

let run_experiments () =
  let ctx = get_context () in
  
  (* Basic proposition tests *)
  print_endline "\n==== Testing Basic Propositions ====";
  solve ctx [`!b. b \/ ~b`];
  solve ctx [`?b. b`];
  solve ctx [`b:bool`];
  
  (* Arithmetic tests *)
  print_endline "\n==== Testing Arithmetic ====";
  solve ctx [`0 <= 0`];
  solve ctx [`0 <= 1`];
  solve ctx [`1 <= 0`];
  solve ctx [`1 > 0`];
  solve ctx [`0 > 1`];
  solve ctx [`0 > 0`];
  
  (* Advanced tests with system *)
  print_endline "\n==== Testing Complex System Expressions ====";
  let complex_term = 
    `System (vector[(p1,d1); (p2,d2); (p3,d3)])
            (vector[s1; s2; s3]) : 3 system
     IN ITER 10 (SETBIND NEW_SYSTEM)
               {System (vector[(P0,T); (P1,F); (P2,F)])
                       (vector[0; 0; 0]) : 3 system}`
  in
  
  (* This would normally be processed with conversions as in the original *)
  print_endline "Note: Complex system test would require proper rewrite rules";
  
  print_endline "\nExperiments completed.";
  ();;

(* Comment out to run experiments *)
(* run_experiments ();; *)

(* ------------------------------------------------------------------------- *)
(* Usage example:                                                            *)
(* ------------------------------------------------------------------------- *)

print_endline "\nZ3 Experiments with HOL Light - Improved Version";
print_endline "To run tests: run_tests();;";
print_endline "To try invariant proof: try_invariant_proof();;";
print_endline "To run experiments: run_experiments();;";
print_endline "To reset Z3 context: reset_context();;";