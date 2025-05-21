(* ========================================================================= *)
(* Simple functions for the invocation of the Z3 solver.                     *)
(* ========================================================================= *)

#use "topfind";;
#require "z3";;

(* ------------------------------------------------------------------------- *)
(* Additional HOL Light helper functions.                                    *)
(* ------------------------------------------------------------------------- *)

let dest_quantifier tm =
  if is_forall tm
  then let v,b = dest_forall tm in v,b,true
  else if is_exists tm
  then let v,b = dest_exists tm in v,b,false
  else failwith "dest_quantifier";;

let is_quantifier = can dest_quantifier;;

(* Test: *)
assert (dest_quantifier `?n:num. b` = (`n:num`, `b:bool`, false));;

(* ------------------------------------------------------------------------- *)
(* Rename idents for compatibility with the jrh lexer:                       *)
(*    Z3 -> Zzz
      Z3.FuncDecl -> Zzz.Funcdecl
      Z3.Solver.SATISFIABLE -> Zzz.Solver.satisfiable                        *)
(* ------------------------------------------------------------------------- *)

unset_jrh_lexer;;
module Zzz = struct
  include Z3
  module Funcdecl = Z3.FuncDecl
  module Solver = struct
    include Z3.Solver
    let satisfiable = Z3.Solver.SATISFIABLE
    let unsatisfiable = Z3.Solver.UNSATISFIABLE
    let unknown = Z3.Solver.UNKNOWN
  end
end;;
set_jrh_lexer;;

(* ------------------------------------------------------------------------- *)
(* Translate a model into an assoc list.                                     *)
(* ------------------------------------------------------------------------- *)

let assoc_of_model m =
  let ts = Zzz.Model.get_const_decls m
  and f t =
    let s = Zzz.Symbol.get_string (Zzz.Funcdecl.get_name t) in
    let v = Zzz.Model.get_const_interp m t in
    let v = match v with Some v -> v | None -> fail() in
    let v = Zzz.Expr.to_string v in
    s,v
  in
  mapfilter f ts;;

(* ------------------------------------------------------------------------- *)
(* Invocation of the Z3 checker.                                             *)
(* ------------------------------------------------------------------------- *)

let solve ctx exprs =
  let s = Zzz.Solver.mk_simple_solver ctx in
  let ret = Zzz.Solver.check s exprs in
  if ret = Zzz.Solver.unsatisfiable then failwith "Unsatisfiable" else
  if ret = Zzz.Solver.unknown then
    failwith ("Unknown: "^Zzz.Solver.get_reason_unknown s)
  else
    match Zzz.Solver.get_model s with
    | None -> failwith "Model not available"  (* Should not occur(?) *)
    | Some m -> assoc_of_model m;;

(* ------------------------------------------------------------------------- *)
(* Constructors for quantifiers.                                             *)
(* ------------------------------------------------------------------------- *)

let z3_simple_mk_forall ctx vars body =
  let quant = Zzz.Quantifier.mk_forall_const ctx vars body
                None [] [] None None in
  Zzz.Quantifier.expr_of_quantifier quant;;

let z3_simple_mk_exists ctx vars body =
  let quant = Zzz.Quantifier.mk_exists_const ctx vars body
                None [] [] None None in
  Zzz.Quantifier.expr_of_quantifier quant;;
