(* ========================================================================= *)
(* Enhanced Translation of HOL Light ant constructions to Z3.                  *)
(*                                                                           *)
(* This file provides extended functionality to translate HOL Light           *)
(* constructions from the ant.ml file into Z3 expressions.                    *)
(* ========================================================================= *)

(* Load required libraries *)
needs "HOL-Ants/ant.ml";;
needs "HOL-Ants/z3_experiments.ml";;

(* ------------------------------------------------------------------------- *)
(* Enhanced translator for HOL Light ant constructions to Z3.                *)
(* ------------------------------------------------------------------------- *)

(* Initialize Z3 context *)
let ant_z3_ctx = Zzz.mk_context [];;

(* Helper function to create Z3 enumerative sort for positions *)
let create_position_sort ctx =
  let sort_position = Zzz.Enumeration.mk_sort_s ctx "position"
                      ["P0"; "P1"; "P2"; "P3"; "P4"] in
  let [z3p0; z3p1; z3p2; z3p3; z3p4] =
    Zzz.Enumeration.get_consts sort_position in
  (sort_position, z3p0, z3p1, z3p2, z3p3, z3p4);;

(* Create position sort and constants *)
let (sort_position, z3p0, z3p1, z3p2, z3p3, z3p4) = create_position_sort ant_z3_ctx;;

(* Helper function to create a bool sort *)
let create_bool_sort ctx = Zzz.Boolean.mk_sort ctx;;

(* Create bool sort *)
let sort_bool = create_bool_sort ant_z3_ctx;;

(* Helper function to translate a position constant to Z3 *)
let translate_position_const ctx pos =
  match pos with
  | "P0" -> z3p0
  | "P1" -> z3p1
  | "P2" -> z3p2
  | "P3" -> z3p3
  | "P4" -> z3p4
  | _ -> failwith ("Unknown position constant: " ^ pos);;

(* Create a product sort for ant (position * bool) *)
let create_ant_sort ctx pos_sort bool_sort =
  Zzz.Datatype.mk_tuple_sort ctx "ant" ["pos"; "dir"] [pos_sort; bool_sort];;

(* Create ant sort *)
let (ant_sort, ant_constructor, [ant_pos_accessor; ant_dir_accessor]) = 
  create_ant_sort ant_z3_ctx sort_position sort_bool;;

(* Create array sort for ant^N *)
let create_ant_array_sort ctx ant_sort n =
  Zzz.Z3Array.mk_sort ctx ant_sort (Zzz.Arithmetic.Integer.mk_sort ctx);;

(* Create num^3 sort (array of integers) *)
let create_num3_sort ctx = 
  Zzz.Z3Array.mk_sort ctx (Zzz.Arithmetic.Integer.mk_sort ctx) (Zzz.Arithmetic.Integer.mk_sort ctx);;

(* Create num3 sort *)
let num3_sort = create_num3_sort ant_z3_ctx;;

(* Helper function to create a system sort (ant^N * num^3) *)
let create_system_sort ctx ant_array_sort num3_sort =
  Zzz.Datatype.mk_tuple_sort ctx "system" ["ants"; "sti"] [ant_array_sort; num3_sort];;

(* Enhanced term translation supporting more complex HOL Light constructions *)
let rec translate_term_to_z3 ctx tm =
  let num_ty = `:num`
  and position_ty = `:position`
  and ant_ty = `:ant`
  and system_ty = `:N system`
  and int_zero = Zzz.Arithmetic.Integer.mk_numeral_i ctx 0 in
  
  if is_const tm then
    match name_of tm with
    | "T" -> Zzz.Boolean.mk_true ctx
    | "F" -> Zzz.Boolean.mk_false ctx
    | "P0" -> z3p0
    | "P1" -> z3p1
    | "P2" -> z3p2
    | "P3" -> z3p3
    | "P4" -> z3p4
    | nm -> failwith ("Unknown constant: " ^ nm)
  
  else if is_var tm then
    let nm, ty = dest_var tm in
    if ty = bool_ty then Zzz.Boolean.mk_const_s ctx nm
    else if ty = num_ty then Zzz.Arithmetic.Integer.mk_const_s ctx nm
    else if ty = position_ty then Zzz.Expr.mk_const_s ctx nm sort_position
    else if is_type ty "ant" then 
      (* Create a const of ant sort *)
      Zzz.Expr.mk_const_s ctx nm ant_sort
    else if is_type ty "system" then
      (* Handle system variables *)
      let system_array_sort = create_ant_array_sort ctx ant_sort 
                             (Zzz.Arithmetic.Integer.mk_numeral_i ctx 
                              (dest_small_numeral (hd(tl(dest_type ty))))) in
      let system_sort = create_system_sort ctx system_array_sort num3_sort in
      Zzz.Expr.mk_const_s ctx nm system_sort
    else failwith ("Variable of unhandled type: " ^ nm)
  
  else if is_eq tm then
    let x, y = dest_eq tm in
    let e = translate_term_to_z3 ctx x
    and f = translate_term_to_z3 ctx y in
    if type_of x = bool_ty 
    then Zzz.Boolean.mk_iff ctx e f
    else Zzz.Boolean.mk_eq ctx e f
  
  else if is_neg tm then
    Zzz.Boolean.mk_not ctx (translate_term_to_z3 ctx (dest_neg tm))
  
  else if is_conj tm then
    let p, q = dest_conj tm in
    Zzz.Boolean.mk_and ctx [translate_term_to_z3 ctx p; translate_term_to_z3 ctx q]
  
  else if is_disj tm then
    let p, q = dest_disj tm in
    Zzz.Boolean.mk_or ctx [translate_term_to_z3 ctx p; translate_term_to_z3 ctx q]
  
  else if is_imp tm then
    let p, q = dest_imp tm in
    Zzz.Boolean.mk_implies ctx (translate_term_to_z3 ctx p) (translate_term_to_z3 ctx q)
  
  else if is_cond tm then
    let b, (s, t) = dest_cond tm in
    Zzz.Boolean.mk_ite ctx (translate_term_to_z3 ctx b) 
                          (translate_term_to_z3 ctx s) 
                          (translate_term_to_z3 ctx t)
  
  else if is_quantifier tm then
    let vtm, btm, universal = dest_quantifier tm in
    let vexpr = translate_term_to_z3 ctx vtm
    and bexpr = translate_term_to_z3 ctx btm in
    let bexpr = if type_of vtm = num_ty
                then let lexpr = Zzz.Arithmetic.mk_le ctx int_zero vexpr in
                     if universal
                     then Zzz.Boolean.mk_implies ctx lexpr bexpr
                     else Zzz.Boolean.mk_and ctx [lexpr; bexpr]
                else bexpr in
    if universal
    then z3_simple_mk_forall ctx [vexpr] bexpr
    else z3_simple_mk_exists ctx [vexpr] bexpr
  
  else if is_binary "<=" tm then
    let x, y = dest_binary "<=" tm in
    Zzz.Arithmetic.mk_le ctx (translate_term_to_z3 ctx x) (translate_term_to_z3 ctx y)
  
  else if is_binary ">=" tm then
    let x, y = dest_binary ">=" tm in
    Zzz.Arithmetic.mk_ge ctx (translate_term_to_z3 ctx x) (translate_term_to_z3 ctx y)
  
  else if is_binary "<" tm then
    let x, y = dest_binary "<" tm in
    Zzz.Arithmetic.mk_lt ctx (translate_term_to_z3 ctx x) (translate_term_to_z3 ctx y)
  
  else if is_binary ">" tm then
    let x, y = dest_binary ">" tm in
    Zzz.Arithmetic.mk_gt ctx (translate_term_to_z3 ctx x) (translate_term_to_z3 ctx y)
  
  else if is_numeral tm then
    Zzz.Arithmetic.Integer.mk_numeral_i ctx (dest_small_numeral tm)
  
  else if is_binary "+" tm then
    let x, y = dest_binary "+" tm in
    Zzz.Arithmetic.mk_add ctx [translate_term_to_z3 ctx x; translate_term_to_z3 ctx y]
  
  else if is_binary "-" tm then
    let x, y = dest_binary "-" tm in
    Zzz.Arithmetic.mk_sub ctx [translate_term_to_z3 ctx x; translate_term_to_z3 ctx y]
  
  else if is_binary "*" tm then
    let x, y = dest_binary "*" tm in
    Zzz.Arithmetic.mk_mul ctx [translate_term_to_z3 ctx x; translate_term_to_z3 ctx y]
  
  else if is_pair tm then
    (* Handle (position, bool) pairs *)
    let fst_tm, snd_tm = dest_pair tm in
    let fst_expr = translate_term_to_z3 ctx fst_tm
    and snd_expr = translate_term_to_z3 ctx snd_tm in
    ant_constructor [fst_expr; snd_expr]
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "FST") then
    (* Handle FST applications *)
    let pair_tm = rand tm in
    let pair_expr = translate_term_to_z3 ctx pair_tm in
    Zzz.Datatype.get_accessor ctx ant_pos_accessor pair_expr
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "SND") then
    (* Handle SND applications *)
    let pair_tm = rand tm in
    let pair_expr = translate_term_to_z3 ctx pair_tm in
    Zzz.Datatype.get_accessor ctx ant_dir_accessor pair_expr
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "INVARIANT_STI") then
    (* Handle INVARIANT_STI function *)
    let sti_tm = rand tm in
    let sti_expr = translate_term_to_z3 ctx sti_tm in
    let max_expr = translate_term_to_z3 ctx `MAX (sti$2) (sti$3)` in
    Zzz.Arithmetic.mk_gt ctx (translate_term_to_z3 ctx `sti$1`) max_expr
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "INVARIANT") then
    (* Handle INVARIANT function *)
    let sys_tm = rand tm in
    let sys_expr = translate_term_to_z3 ctx sys_tm in
    
    (* Create a simplified version of the INVARIANT definition for Z3 *)
    let invariant_def = `!s t:N system. 
                         s IN NEW_SYSTEM sys /\ t IN NEW_SYSTEM s
                         ==> INVARIANT_STI (STI sys) /\
                             INVARIANT_STI (STI s) /\
                             INVARIANT_STI (STI t)` in
    translate_term_to_z3 ctx (subst [sys_tm, `sys:N system`] invariant_def)
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "NEW_ANT") then
    (* Handle NEW_ANT function *)
    let args = strip_comb tm in
    let sti_tm = el 1 args in
    let ant_tm = el 2 args in
    
    (* Attempt to unpack position and direction from ant *)
    let pos_tm, dir_tm = 
      try dest_pair ant_tm 
      with Failure _ -> 
        try (`FST ^ant_tm`, `SND ^ant_tm`) 
        with Failure _ -> failwith "Cannot extract position and direction from ant" in
    
    (* Translate the definition of NEW_ANT to Z3 *)
    let new_ant_def = `NEW_ANT (sti:num^3) (pos,dir) =
                      if pos = P1 then {((if dir then P4 else P0),dir)} else
                      if pos = P2 then {((if dir then P3 else P0),dir)} else
                      if pos = P3 then {((if dir then P4 else P2),dir)} else
                      if pos = P0
                      then {(pos,T) | sti$2 <= sti$1 /\ pos = P1 \/
                                     sti$1 <= sti$2 /\ pos = P2}
                      else {(pos,F) | sti$3 <= sti$1 /\ pos = P1 \/
                                     sti$1 <= sti$3 /\ pos = P3}` in
                           
    let subst_def = subst [sti_tm, `sti:num^3`; 
                           pos_tm, `pos:position`; 
                           dir_tm, `dir:bool`] new_ant_def in
    translate_term_to_z3 ctx subst_def
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "NEW_STI") then
    (* Handle NEW_STI function *)
    let sys_tm = rand tm in
    
    (* Translate the definition of NEW_STI to Z3 *)
    let new_sti_def = `NEW_STI (System ant sti : N system) : num^3 =
                      lambda p. sti$p +
                                nsum (1..dimindex(:N))
                                     (\i. if FST(ant$i) = PP p then 1 else 0)` in
    
    let subst_def = subst [sys_tm, `System ant sti : N system`] new_sti_def in
    translate_term_to_z3 ctx subst_def
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "NEW_SYSTEM") then
    (* Handle NEW_SYSTEM function *)
    let sys_tm = rand tm in
    
    (* Translate the definition of NEW_SYSTEM to Z3 *)
    let new_system_def = `NEW_SYSTEM (sys:N system) : N system -> bool =
                         {System ant' (NEW_STI sys) | ant':ant^N |
                          !i. 1 <= i /\ i <= dimindex(:N)
                              ==> ant'$i IN NEW_ANT (STI sys) (ANT sys$i)}` in
    
    let subst_def = subst [sys_tm, `sys:N system`] new_system_def in
    translate_term_to_z3 ctx subst_def
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "MAX") then
    (* Handle MAX function *)
    let args = strip_comb tm in
    let x_tm = el 1 args in
    let y_tm = el 2 args in
    Zzz.Boolean.mk_ite ctx
      (Zzz.Arithmetic.mk_ge ctx (translate_term_to_z3 ctx x_tm) (translate_term_to_z3 ctx y_tm))
      (translate_term_to_z3 ctx x_tm)
      (translate_term_to_z3 ctx y_tm)
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "System") then
    (* Handle System constructor *)
    let args = strip_comb tm in
    let ant_tm = el 1 args in
    let sti_tm = el 2 args in
    
    (* Create a system constructor for Z3 dynamically based on system size *)
    let system_size = 
      let system_ty = type_of tm in
      try dest_small_numeral (hd(tl(dest_type system_ty)))
      with Failure _ -> 
        try dest_small_numeral (hd(tl(dest_type (type_of ant_tm))))
        with Failure _ -> 4 (* Default to 4 if we can't determine size *) in
    
    let system_array_sort = create_ant_array_sort ctx ant_sort 
                           (Zzz.Arithmetic.Integer.mk_numeral_i ctx system_size) in
    let system_sort = create_system_sort ctx system_array_sort num3_sort in
    let (_, system_constructor, _) = system_sort in
    
    system_constructor [translate_term_to_z3 ctx ant_tm; translate_term_to_z3 ctx sti_tm]
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "ANT") then
    (* Handle ANT accessor *)
    let sys_tm = rand tm in
    let sys_expr = translate_term_to_z3 ctx sys_tm in
    (* Extract ant array from system *)
    Zzz.Datatype.get_accessor ctx (hd (snd (triple_of_pair_type sort_position sort_bool))) sys_expr
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "STI") then
    (* Handle STI accessor *)
    let sys_tm = rand tm in
    let sys_expr = translate_term_to_z3 ctx sys_tm in
    (* Extract sti array from system *)
    Zzz.Datatype.get_accessor ctx (hd (tl (snd (triple_of_pair_type sort_position sort_bool)))) sys_expr
  
  else if is_app tm && (is_const (rator tm) && name_of (rator tm) = "IN") then
    (* Handle set membership *)
    let args = strip_comb tm in
    let x_tm = el 1 args in
    let set_tm = el 2 args in
    
    (* Handle different types of set expressions *)
    if is_abs set_tm then
      (* Set comprehension *)
      let bvar, body = dest_abs set_tm in
      let body_expr = translate_term_to_z3 ctx (subst [x_tm, bvar] body) in
      body_expr
    else if is_set set_tm then
      (* Explicit set: check if x is equal to any element *)
      let elements = dest_set set_tm in
      if elements = [] then
        (* Empty set - x is not a member *)
        Zzz.Boolean.mk_false ctx
      else
        (* Check if x equals any element *)
        let eq_exprs = List.map (fun elem -> 
          Zzz.Boolean.mk_eq ctx (translate_term_to_z3 ctx x_tm) (translate_term_to_z3 ctx elem)
        ) elements in
        Zzz.Boolean.mk_or ctx eq_exprs
    else if is_binary "UNION" set_tm then
      (* Set union *)
      let s1, s2 = dest_binary "UNION" set_tm in
      Zzz.Boolean.mk_or ctx [
        translate_term_to_z3 ctx (mk_binop ("IN", x_tm, s1));
        translate_term_to_z3 ctx (mk_binop ("IN", x_tm, s2))
      ]
    else
      (* Other set operations - translate as is *)
      let set_expr = translate_term_to_z3 ctx set_tm in
      Zzz.Boolean.mk_eq ctx (translate_term_to_z3 ctx x_tm) set_expr
  
  else
    let s = string_of_term tm in
    failwith ("Translation of HOL Light formula failed: " ^ s);;

(* Function to solve a goal using Z3 *)
let solve_with_z3 ctx goal =
  let solver = Zzz.Solver.mk_solver ctx None in
  let goal_expr = translate_term_to_z3 ctx goal in
  let negated_goal = Zzz.Boolean.mk_not ctx goal_expr in
  Zzz.Solver.add solver [negated_goal];
  let result = Zzz.Solver.check solver [] in
  match result with
  | Zzz.Solver.UNSATISFIABLE -> true  (* Goal is valid *)
  | Zzz.Solver.SATISFIABLE -> 
      (* Goal is invalid - get a counterexample *)
      let model = Zzz.Solver.get_model solver in
      Printf.printf "Counterexample found:\n%s\n" (model_to_string model);
      false
  | Zzz.Solver.UNKNOWN -> 
      Printf.printf "Z3 returned UNKNOWN - the goal might be too complex\n";
      false;;

(* Function to check satisfiability of a formula using Z3 *)
let check_sat_with_z3 ctx formula =
  let solver = Zzz.Solver.mk_solver ctx None in
  let formula_expr = translate_term_to_z3 ctx formula in
  Zzz.Solver.add solver [formula_expr];
  let result = Zzz.Solver.check solver [] in
  match result with
  | Zzz.Solver.SATISFIABLE -> 
      let model = Zzz.Solver.get_model solver in
      (true, model)  (* Formula is satisfiable *)
  | Zzz.Solver.UNSATISFIABLE -> (false, None)  (* Formula is unsatisfiable *)
  | Zzz.Solver.UNKNOWN -> 
      Printf.printf "Z3 returned UNKNOWN - the formula might be too complex\n";
      (false, None);;

(* Convert model to string for display *)
let model_to_string model =
  let open Zzz in
  let n = Model.get_num_consts model in
  let rec loop i acc =
    if i >= n then acc
    else
      let decl = Model.get_const_decl model i in
      let name = FuncDecl.get_name decl in
      let sym = Symbol.to_string name in
      let value = Model.get_const_interp model decl in
      let s_val = Expr.to_string value in
      loop (i + 1) ((sym ^ " = " ^ s_val) :: acc)
  in
  String.concat "\n" (List.rev (loop 0 []));;

(* Create a position * bool pair (ant) *)
let make_ant pos dir =
  mk_pair (mk_const(pos, `:position`), if dir then mk_const("T", `:bool`) else mk_const("F", `:bool`));;

(* Create a system with n ants and a state indicator *)
let make_system n ants sti =
  let ant_arr = mk_vector n ants in
  let sti_arr = mk_vector 3 sti in
  mk_comb (mk_comb (mk_const("System", `:ant^N -> num^3 -> N system`), ant_arr), sti_arr);;

(* Create an initial system with n ants *)
let make_initial_system n ants =
  make_system n ants [num_0; num_0; num_0];;

(* ------------------------------------------------------------------------- *)
(* Testing the enhanced translator with key lemmas from ant.ml                *)
(* ------------------------------------------------------------------------- *)

(* Example 1: Test the INVARIANT_STI property *)
let test_invariant_sti_property () =
  let inv_sti_tm = `INVARIANT_STI (vector[5; 2; 1]:num^3)` in
  
  let (is_sat, model_opt) = check_sat_with_z3 ant_z3_ctx inv_sti_tm in
  if is_sat then
    Printf.printf "The INVARIANT_STI property holds for the given vector.\n"
  else
    Printf.printf "The INVARIANT_STI property does not hold for the given vector.\n";;

(* Example 2: Test the NEW_ANT function *)
let test_new_ant_function () =
  let sti = mk_vector 3 [num_5; num_2; num_1] in
  let ant_tm = make_ant "P1" true in
  
  let new_ant_tm = mk_comb(mk_comb(mk_const("NEW_ANT", `:num^3 -> position # bool -> (position # bool) -> bool`), 
                                 sti), ant_tm) in
  
  let result_tm = `(P4,T) IN ^new_ant_tm` in
  
  let is_valid = solve_with_z3 ant_z3_ctx result_tm in
  if is_valid then
    Printf.printf "The ant (P4,T) is in NEW_ANT for the given input.\n"
  else
    Printf.printf "The ant (P4,T) is not in NEW_ANT for the given input.\n";;

(* Example 3: Test the INVARIANT_IN_NEW_ANT lemma *)
let test_invariant_in_new_ant () =
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
  
  let is_valid = solve_with_z3 ant_z3_ctx lemma_tm in
  if is_valid then
    Printf.printf "The INVARIANT_IN_NEW_ANT lemma is valid.\n"
  else
    Printf.printf "The INVARIANT_IN_NEW_ANT lemma is invalid.\n";;

(* Example 4: Test the main invariant theorem *)
let test_invariant_theorem () =
  let thm_tm = `!sys sys':2 system.
                INVARIANT sys /\ sys' IN NEW_SYSTEM sys
                ==> INVARIANT sys'` in
  
  let is_valid = solve_with_z3 ant_z3_ctx thm_tm in
  if is_valid then
    Printf.printf "The invariant theorem is valid.\n"
  else
    Printf.printf "The invariant theorem is invalid.\n";;

(* Example 5: Check if a specific configuration is reachable in the ant system *)
let test_reachability () =
  let initial_sys = make_initial_system 2 [make_ant "P0" true; make_ant "P1" false] in
  let target_sys = make_system 2 [make_ant "P4" true; make_ant "P1" true] [num_9; num_1; num_0] in
  
  let reachability_tm = 
    mk_binop("IN", target_sys, 
            mk_comb(mk_comb(mk_const("ITER", `:num -> (A -> A -> bool) -> A -> A -> bool`), 
                          mk_small_numeral 10),
                  mk_comb(mk_const("SETBIND", `:(A -> B -> bool) -> A -> B -> bool`), 
                         mk_const("NEW_SYSTEM", `:N system -> N system -> bool`)),
                  mk_set [initial_sys])) in
  
  let (is_sat, model_opt) = check_sat_with_z3 ant_z3_ctx reachability_tm in
  if is_sat then 
    Printf.printf "The target configuration is reachable.\n"
  else
    Printf.printf "The target configuration is not reachable.\n";;

(* Function to run all tests *)
let run_all_tests () =
  Printf.printf "=== Testing INVARIANT_STI property ===\n";
  test_invariant_sti_property ();
  
  Printf.printf "\n=== Testing NEW_ANT function ===\n";
  test_new_ant_function ();
  
  Printf.printf "\n=== Testing INVARIANT_IN_NEW_ANT lemma ===\n";
  test_invariant_in_new_ant ();
  
  Printf.printf "\n=== Testing invariant theorem ===\n";
  test_invariant_theorem ();
  
  Printf.printf "\n=== Testing reachability ===\n";
  test_reachability ();;

(* Print a message that the enhanced translator is loaded *)
print_string "Enhanced HOL Light to Z3 translator for ant constructions loaded.\n";;

(* Uncomment to run all tests *)
(* run_all_tests ();; *) 