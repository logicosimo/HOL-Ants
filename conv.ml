(* ========================================================================= *)
(* Conversions.                                                              *)
(*                                                                           *)
(* Copyright (c) 2015 Marco Maggesi                                          *)
(* ========================================================================= *)

let (FAIL_CONV : string -> conv) =
  fun tok _ -> failwith tok;;

let COND_CONV : conv =
  let tth,fth = CONJ_PAIR (SPEC_ALL COND_CLAUSES) in
  REWR_CONV tth ORELSEC REWR_CONV fth ORELSEC FAIL_CONV "COND_CONV";;

let CONJ_CONV : conv =
  let tth,fth = CONJ_PAIR (TAUT `(T /\ a <=> a) /\ (F /\ a <=> F)`) in
  REWR_CONV tth ORELSEC REWR_CONV fth ORELSEC FAIL_CONV "CONJ_CONV";;

let DISJ_CONV : conv =
  let tth,fth = CONJ_PAIR (TAUT `(T \/ a <=> T) /\ (F \/ a <=> a)`) in
  REWR_CONV tth ORELSEC REWR_CONV fth ORELSEC FAIL_CONV "DISJ_CONV";;

(* 
let COND_CONV = GEN_REWRITE_CONV I [COND_CLAUSES];;
let AND_CONV = GEN_REWRITE_CONV I [TAUT `(F /\ a <=> F) /\ (T /\ a <=> a)`];;
let OR_CONV = GEN_REWRITE_CONV I [TAUT `(F \/ a <=> a) /\ (T \/ a <=> T)`];;
*)
