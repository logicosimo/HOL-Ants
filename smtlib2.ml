#use "topfind";;
#require "sexplib";;

(* ------------------------------------------------------------------------- *)
(* Basic functions.                                                          *)
(* ------------------------------------------------------------------------- *)

let sexp_pp = Sexplib.Sexp.pp_hum;;

let string_of_sexp = Sexplib.Sexp.to_string;;

let sexp_mk_list (l : Sexplib.Sexp.t list) : Sexplib.Sexp.t =
  Sexplib.Sexp.List l;;

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

(*
strip_prime "x'''";;
strip_prime "pippo''";;
strip_prime "a";;
*)

let sexp_mk_atom (s : string) : Sexplib.Sexp.t =
  Sexplib.Sexp.Atom (strip_prime s);;

let sexp_mk_fn (s : string) (l : Sexplib.Sexp.t list) : Sexplib.Sexp.t =
  sexp_mk_list (sexp_mk_atom s :: l);;

(* ------------------------------------------------------------------------- *)
(* Exam[le.                                                                ] *)
(* ------------------------------------------------------------------------- *)

let mysexp = sexp_mk_list[sexp_mk_atom "a"; sexp_mk_atom "b"];;

Format.fprintf Format.std_formatter "%a@." sexp_pp mysexp;;

(* ------------------------------------------------------------------------- *)
(* Handy sexp constructors.                                                  *)
(* ------------------------------------------------------------------------- *)

let sexp_mk_conj l =
  match l with
  | [] -> sexp_mk_atom "true"
  | [e] -> e
  | l -> sexp_mk_fn "and" l;;

let sexp_mk_disj l =
  match l with
  | [] -> sexp_mk_atom "false"
  | [e] -> e
  | l -> sexp_mk_fn "or" l;;

let sexp_mk_add l =
  match l with
  | [] -> sexp_mk_atom "0"
  | [e] -> e
  | l -> sexp_mk_fn "+" l;;

let sexp_mk_small_numeral n =
  sexp_mk_atom (string_of_int n);;

(* ------------------------------------------------------------------------- *)
(* Net-based translation infrastructure from HOL terms to sexps.             *)
(* ------------------------------------------------------------------------- *)

let sexp_of_term_net : (term-> Sexplib.Sexp.t) net ref =
  ref empty_net;;

let sexp_of_term tm =
  let l = lookup tm !sexp_of_term_net in
  try tryfind (fun f -> f tm) l with Failure s ->
  if is_var tm || is_const tm then sexp_mk_atom (name_of tm) else
  failwith ("sexp_of_term: "^string_of_term tm);;

let strsexp_of_term = string_of_sexp o sexp_of_term;;

(* ------------------------------------------------------------------------- *)
(* Translation of types.                                                     *)
(* ------------------------------------------------------------------------- *)

let sexp_of_type ty =
  match fst(dest_type ty) with
  | "bool" -> sexp_mk_atom "Bool"
  | "num" -> sexp_mk_atom "Int"
  | "position" -> sexp_mk_atom "Position"
  | s -> failwith ("sexp_of_type: Unknown type: "^s);;

(* ------------------------------------------------------------------------- *)
(* Translation of identity expressions.                                      *)
(* ------------------------------------------------------------------------- *)

let sexp_of_eq tm =
  let x,y = dest_eq tm in
  let e = sexp_of_term x
  and f = sexp_of_term y in
  if type_of x = bool_ty
  then sexp_mk_fn "iff" [e; f]
  else sexp_mk_fn "=" [e; f];;

(* ------------------------------------------------------------------------- *)
(* Translation of boolean expressions.                                       *)
(* ------------------------------------------------------------------------- *)

let sexp_of_neg tm =
  sexp_mk_fn "not" [sexp_of_term (dest_neg tm)];;

let sexp_of_conj tm =
  if not(is_conj tm) then failwith "sexp_of_conj" else
  let args = striplist dest_conj tm in
  sexp_mk_conj (map sexp_of_term args);;

let sexp_of_disj tm =
  if not(is_disj tm) then failwith "sexp_of_disj" else
  let args = striplist dest_disj tm in
  sexp_mk_disj (map sexp_of_term args);;

let sexp_of_imp tm =
  let p,q = dest_imp tm in
  sexp_mk_fn "=>" [sexp_of_term p; sexp_of_term q];;

(* ------------------------------------------------------------------------- *)
(* Translation of conditional constructions.                                 *)
(* ------------------------------------------------------------------------- *)

let sexp_of_cond tm =
  let b,(s,t) = dest_cond tm in
  sexp_mk_fn "ite" [sexp_of_term b;
                    sexp_of_term s;
                    sexp_of_term t];;

(* ------------------------------------------------------------------------- *)
(* Translation of quantifiers.                                               *)
(* ------------------------------------------------------------------------- *)

let mk_quant_var v =
  let nm,ty = dest_var v in
  sexp_mk_list[sexp_mk_atom nm;
               sexp_of_type ty];;

let sexp_mk_nonneg =
  let sexp_0 = sexp_mk_atom "0" in
  fun v ->
    let nm,ty = dest_var v in
    let nty,_ = dest_type ty in
    if nty <> "num" then failwith "sexp_mk_nonneg" else
    sexp_mk_fn ">=" [sexp_mk_atom nm; sexp_0];;

let sexp_of_forall tm =
  let vl,btm = strip_forall tm in
  if vl = [] then failwith "sexp_of_forall" else
  let vsexps = sexp_mk_list (map mk_quant_var vl) in
  let bounds = mapfilter sexp_mk_nonneg vl in
  let bdy = sexp_of_term btm in
  let bdy = if bounds = [] then bdy else
            sexp_mk_fn "=>" [sexp_mk_conj bounds; bdy] in
  sexp_mk_fn "forall"  [vsexps; bdy];;

let sexp_of_exists tm =
  let vl,btm = strip_exists tm in
  if vl = [] then failwith "sexp_of_exists" else
  let vsexps = sexp_mk_list (map mk_quant_var vl) in
  let bounds = mapfilter sexp_mk_nonneg vl in
  let bdy = sexp_of_term btm in
  let bdy = if bounds = [] then bdy else
            sexp_mk_conj (bounds @ [bdy]) in
  sexp_mk_fn "exists"  [vsexps; bdy];;

(* ------------------------------------------------------------------------- *)
(* Translation of arithmetical expressions.                                  *)
(* ------------------------------------------------------------------------- *)

let sexp_of_numeral tm =
  sexp_mk_small_numeral (dest_small_numeral tm);;

let sexp_of_add =
  let is_add = is_binary "+" in
  let dest_add = dest_binary "+" in
  fun tm ->
    if not(is_add tm) then failwith "sexp_of_add" else
    let args = striplist dest_add tm in
    sexp_mk_add (map sexp_of_term args);;

let sexp_of_le tm =
  let x,y = dest_binary "<=" tm in
  sexp_mk_fn "<=" [sexp_of_term x; sexp_of_term y];;

let sexp_of_gt tm =
  let x,y = dest_binary ">" tm in
  sexp_mk_fn ">" [sexp_of_term x; sexp_of_term y];;

let sexp_mk_mul l =
  match l with
  | [] -> sexp_mk_atom "1"
  | [e] -> e
  | l -> sexp_mk_fn "*" l;;

let sexp_mk_sub (a, b) =
  sexp_mk_fn "-" [a; b];;

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

sexp_of_term_net := basic_sexp_of_term_net;;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
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
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

let ptm =
  `((~(a > b) \/ ~(a > c)) \/ ~(a + 1 > b) \/ ~(a + 1 > c)) /\
   c <= a + 1
   ==> ?a b a_ b_.
           (((a = x /\ b = y /\ c = z) /\ y <= x) /\
            a_ = a + 1 /\
            b_ = b /\
            c_ = c)`;;

let ptm =
  `((~(x' > y') \/ ~(x' > z')) \/ ~(x' + 1 > y') \/ ~(x' + 1 > z')) /\
   z' <= x' + 1
   ==> ?x' y' x'' y''.
           (((x' = x /\ y' = y /\ z' = z) /\ y <= x) /\
            x'' = x' + 1 /\
            y'' = y' /\
            z'' = z')`;;

g `!sys sys':1 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
e (REWRITE_TAC[CART_EQ; DIMINDEX_1; FORALL_1; DIMINDEX_3; FORALL_3; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_VECTOR_1; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_3; VECTOR_1]);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_3; DIMINDEX_1; NSUM_1; VECTOR_3; VECTOR_1; PP]);;
e (REWRITE_TAC[MAX]);;
let _,pth = top_goal();;

g `!sys sys':2 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
e (REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; DIMINDEX_3; FORALL_3; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_VECTOR_2; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_3; VECTOR_2]);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_3; DIMINDEX_2; NSUM_2; VECTOR_3; VECTOR_2; PP]);;
e (REWRITE_TAC[MAX]);;
let _,pth = top_goal();;

g `!sys sys':3 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
e (REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; DIMINDEX_3; FORALL_3; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_VECTOR_3; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_3; VECTOR_3]);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_3; DIMINDEX_3; NSUM_3; VECTOR_3; VECTOR_3; PP]);;
e (REWRITE_TAC[MAX]);;
let _,pth = top_goal();;

g `!sys sys':4 system.
     INVARIANT sys /\ sys' IN NEW_SYSTEM sys
     ==> INVARIANT sys'`;;
e (REWRITE_TAC[INVARIANT; INVARIANT_STI]);;
e (REWRITE_TAC[IN_NEW_SYSTEM_ALT; NEW_ANT_ALT; NEW_STI_ALT]);;
e (REWRITE_TAC[CART_EQ; DIMINDEX_4; FORALL_4; DIMINDEX_3; FORALL_3; VECTOR_ADD_NUM_COMPONENT]);;
e (REWRITE_TAC[FORALL_SYSTEM_THM; FORALL_VECTOR_3; FORALL_VECTOR_4; FORALL_PAIR_THM]);;
e (REWRITE_TAC[ANT; STI; VECTOR_3; VECTOR_4]);;
e (REWRITE_TAC[DELTA_STI_COMPONENT_ALT; DIMINDEX_3; DIMINDEX_4; NSUM_4; VECTOR_3; VECTOR_4; PP]);;
e (REWRITE_TAC[MAX]);;
let _,pth = top_goal();;

let xtm = list_mk_forall (frees ptm,ptm) in
let xtm = mk_neg xtm in
let expr = sexp_mk_fn "assert" [sexp_of_term xtm] in
Format.fprintf Format.std_formatter "%a@." sexp_pp expr;;


let sim4 =
  `System (vector[(a0,d0); (a1,d1); (a2,d2); (a3,d3)])
          (vector[s1; s2; s3]) : 4 system IN
   ITER 5 (SETBIND NEW_SYSTEM)
          {System (vector[(P0,T); (P1,F); (P2,F); (P4,F)])
                  (vector[0; 0; 0])}`;;

sim4 |> REWRITE_CONV[TOP_SWEEP_CONV num_CONV `5`; ITER; IN_SETBIND;
                     IN_NEW_SYSTEM_ALT; DIMINDEX_4; FORALL_4;
                     ANT; STI;
                     NEW_ANT_ALT;
                     NEW_STI_ALT;
                     DELTA_STI_COMPONENT_ALT;
                     VECTOR_ADD_NUM_COMPONENT;
                     EXISTS_SYSTEM_THM;
                     EXISTS_PAIR_THM;
                     EXISTS_VECTOR_4; VECTOR_4;
                     EXISTS_VECTOR_3; VECTOR_3; FORALL_3;
                     NSUM_4; PP;
                     CART_EQ; DIMINDEX_3; VECTOR_3;
                     IN_INSERT; NOT_IN_EMPTY];;

concl it |> variables |> map dest_var;;                     