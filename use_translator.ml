(* ========================================================================= *)
(* Usage examples for the enhanced HOL Light to Z3 translator.                 *)
(*                                                                           *)
(* This file demonstrates how to use the enhanced translator to solve         *)
(* verification problems related to the ant system from ant.ml.               *)
(* ========================================================================= *)

(* Load the enhanced translator *)
needs "HOL-Ants/ant_to_z3_enhanced.ml";;

(* ------------------------------------------------------------------------- *)
(* Example 1: Verify the INVARIANT_STI property for a specific state vector  *)
(* ------------------------------------------------------------------------- *)

(* Create a state vector and check if it satisfies the INVARIANT_STI property *)
let example1 () =
  (* Create a state vector *)
  let sti = mk_vector 3 [num_5; num_2; num_1] in
  let inv_tm = mk_comb(mk_const("INVARIANT_STI", `:num^3->bool`), sti) in
  
  (* Print the property to be verified *)
  Printf.printf "Verifying property: %s\n" (string_of_term inv_tm);
  
  (* Check if the property holds *)
  let (is_sat, model_opt) = check_sat_with_z3 ant_z3_ctx inv_tm in
  if is_sat then
    Printf.printf "Result: The INVARIANT_STI property holds for the given vector.\n"
  else
    Printf.printf "Result: The INVARIANT_STI property does not hold for the given vector.\n";;

(* ------------------------------------------------------------------------- *)
(* Example 2: Check transitions using the NEW_ANT function                   *)
(* ------------------------------------------------------------------------- *)

(* Check if a specific transition is possible *)
let example2 () =
  (* Create a state vector *)
  let sti = mk_vector 3 [num_5; num_2; num_1] in
  
  (* Create an ant (position, direction) *)
  let ant = make_ant "P1" true in
  
  (* Check if (P4,T) is a possible next state for the ant *)
  let new_ant_tm = mk_comb(mk_comb(mk_const("NEW_ANT", `:num^3 -> position # bool -> (position # bool) -> bool`), 
                                  sti), ant) in
  
  let result_tm = mk_binop("IN", make_ant "P4" true, new_ant_tm) in
  
  (* Print the property to be verified *)
  Printf.printf "Checking if (P4,T) is a possible next state for (P1,T) with state [5;2;1]:\n";
  
  (* Verify the property *)
  let (is_sat, model_opt) = check_sat_with_z3 ant_z3_ctx result_tm in
  if is_sat then
    Printf.printf "Result: Yes, (P4,T) is a possible next state.\n"
  else
    Printf.printf "Result: No, (P4,T) is not a possible next state.\n";;

(* ------------------------------------------------------------------------- *)
(* Example 3: Check if a specific system configuration is reachable          *)
(* ------------------------------------------------------------------------- *)

let example3 () =
  (* Create an initial system with 2 ants *)
  let initial_sys = make_initial_system 2 [make_ant "P0" true; make_ant "P1" false] in
  
  (* Define a target system we want to check if reachable *)
  let target_sys = make_system 2 [make_ant "P4" true; make_ant "P1" true] [num_9; num_1; num_0] in
  
  (* Create a term for checking if target is reachable in 10 steps *)
  let reachability_tm = 
    mk_binop("IN", target_sys, 
             mk_comb(mk_comb(mk_const("ITER", `:num -> (A -> A -> bool) -> A -> A -> bool`), 
                           mk_small_numeral 10),
                   mk_comb(mk_const("SETBIND", `:(A -> B -> bool) -> A -> B -> bool`), 
                          mk_const("NEW_SYSTEM", `:N system -> N system -> bool`)),
                   mk_set [initial_sys])) in
  
  (* Print the property to be verified *)
  Printf.printf "Checking if system with ants [(P4,T); (P1,T)] and state [9;1;0] is reachable from\n";
  Printf.printf "initial system with ants [(P0,T); (P1,F)] and state [0;0;0] in 10 steps:\n";
  
  (* Verify the property *)
  let (is_sat, model_opt) = check_sat_with_z3 ant_z3_ctx reachability_tm in
  if is_sat then 
    Printf.printf "Result: The target configuration is reachable.\n"
  else
    Printf.printf "Result: The target configuration is not reachable.\n";;

(* ------------------------------------------------------------------------- *)
(* Example 4: Verify a lemma from the ant.ml file                            *)
(* ------------------------------------------------------------------------- *)

let example4 () =
  (* The INVARIANT_IN_NEW_ANT lemma from ant.ml *)
  let lemma_tm = `!sti p d p' d'.
                 INVARIANT_STI sti
                 ==> ((p',d') IN NEW_ANT sti (p,d) <=>
                      (p = P0 /\ p' = P1 /\ d') \/
                      (p = P4 /\ p' = P1 /\ ~d') \/
                      (p = P1 /\ d /\ p' = P4 /\ d') \/
                      (p = P1 /\ ~d /\ p' = P0 /\ ~d') \/
                      (p = P2 /\ d /\ p' = P3 /\ d') \/
                      (p = P2 /\ ~d /\ p' = P0 /\ ~d') \/
                      (p = P3 /\ d /\ p' = P4 /\ d') \/
                      (p = P3 /\ ~d /\ p' = P2 /\ ~d'))` in
  
  (* Print the lemma to be verified *)
  Printf.printf "Verifying lemma: INVARIANT_IN_NEW_ANT\n";
  
  (* Verify the lemma *)
  let is_valid = solve_with_z3 ant_z3_ctx lemma_tm in
  if is_valid then
    Printf.printf "Result: The INVARIANT_IN_NEW_ANT lemma is valid.\n"
  else
    Printf.printf "Result: The INVARIANT_IN_NEW_ANT lemma is invalid.\n";;

(* ------------------------------------------------------------------------- *)
(* Example 5: Verify the main invariant theorem from ant.ml                  *)
(* ------------------------------------------------------------------------- *)

let example5 () =
  (* The main invariant theorem from ant.ml *)
  let thm_tm = `!sys sys':2 system.
                INVARIANT sys /\ sys' IN NEW_SYSTEM sys
                ==> INVARIANT sys'` in
  
  (* Print the theorem to be verified *)
  Printf.printf "Verifying theorem: INVARIANT is preserved by NEW_SYSTEM transitions\n";
  
  (* Verify the theorem *)
  let is_valid = solve_with_z3 ant_z3_ctx thm_tm in
  if is_valid then
    Printf.printf "Result: The invariant theorem is valid.\n"
  else
    Printf.printf "Result: The invariant theorem is invalid.\n";;

(* ------------------------------------------------------------------------- *)
(* Run all examples                                                          *)
(* ------------------------------------------------------------------------- *)

(* Run each example with clear separation *)
let run_examples () =
  Printf.printf "\n============ EXAMPLE 1: INVARIANT_STI PROPERTY ============\n\n";
  example1 ();
  
  Printf.printf "\n\n============ EXAMPLE 2: NEW_ANT FUNCTION ============\n\n";
  example2 ();
  
  Printf.printf "\n\n============ EXAMPLE 3: REACHABILITY ============\n\n";
  example3 ();
  
  Printf.printf "\n\n============ EXAMPLE 4: INVARIANT_IN_NEW_ANT LEMMA ============\n\n";
  example4 ();
  
  Printf.printf "\n\n============ EXAMPLE 5: INVARIANT THEOREM ============\n\n";
  example5 ();;

(* Print a welcome message *)
Printf.printf "HOL Light Ant System to Z3 Translator Examples\n";
Printf.printf "==============================================\n\n";
Printf.printf "This script demonstrates how to use the enhanced translator to\n";
Printf.printf "solve verification problems related to the ant system from ant.ml.\n\n";
Printf.printf "To run all examples, execute: run_examples ();;\n";
Printf.printf "To run individual examples, execute: example1 ();; example2 ();; etc.\n\n";;

(* Uncomment to run all examples automatically *)
(* run_examples ();; *) 