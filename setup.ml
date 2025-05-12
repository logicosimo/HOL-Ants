(* ========================================================================= *)
(* Loading of required libraries and other setup.                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Required libraries.                                                       *)
(* ------------------------------------------------------------------------- *)

needs "Library/iter.ml";;
needs "Multivariate/vectors.ml";;

(* ------------------------------------------------------------------------- *)
(* Theorem database and search mechanism.                                    *)
(* ------------------------------------------------------------------------- *)

loadt "update_database.ml";;

(* ------------------------------------------------------------------------- *)
(* Terse printing for theorems with invented types.                          *)
(* ------------------------------------------------------------------------- *)

let with_flag (flag:'v ref) (v:'v) (f:'a->'b) (x:'a) : 'b =
  let w = !flag in
  try flag := v;
      let ret = f x in
      flag := w;
      ret
  with e -> (flag := w; raise e);;

let pp_psearch fmt =
  let pp_print_strthm (s,th) =
    pp_print_string fmt s; pp_print_space fmt ();
    pp_print_thm fmt th; pp_print_newline fmt ();
    pp_print_newline fmt () in
  fun patts ->
    pp_print_newline fmt ();
    do_list pp_print_strthm (search patts);;

let psearch =
  with_flag print_types_of_subterms 0 (pp_psearch std_formatter);;

let pp_pthm fmt th =
  with_flag print_types_of_subterms 0 (pp_print_thm fmt) th;
  pp_print_newline fmt ();;

let pthm = pp_pthm std_formatter;;

(* ------------------------------------------------------------------------- *)
(* Final setup.                                                              *)
(* ------------------------------------------------------------------------- *)

unset_verbose_symbols();;
Gc.compact();;
