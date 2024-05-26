(* ========================================================================= *)
(* Modelling framework for an idealised system of foraging ants.             *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2023-2024.              *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Sets as nondeterministc monad.                                            *)
(* ========================================================================= *)

let SETBIND = new_definition
  `!f:A->B->bool s:A->bool. SETBIND f s = UNIONS (IMAGE f s)`;;

let SETBIND_CLAUSES = prove
 (`(!f:A->B->bool. SETBIND f {} = {}) /\
   (!f:A->B->bool x s. SETBIND f (x INSERT s) = f x UNION SETBIND f s)`,
  REWRITE_TAC[SETBIND; IMAGE_CLAUSES; UNIONS_0; UNIONS_INSERT]);;

let SETBIND_RID = prove
 (`!f:A->B->bool x. SETBIND f {x} = f x`,
  REWRITE_TAC[SETBIND_CLAUSES; UNION_EMPTY]);;

let IN_SETBIND = prove
 (`!f:A->B->bool s y. y IN SETBIND f s <=> ?x. x IN s /\ y IN f x`,
  REWRITE_TAC[SETBIND; IN_UNIONS; EXISTS_IN_IMAGE]);;

let FORALL_IN_SETBIND = prove
 (`!P f:A->B->bool s.
     (!y. y IN SETBIND f s ==> P y) <=>
     (!x y. x IN s /\ y IN f x ==> P y)`,
  REWRITE_TAC[IN_SETBIND] THEN MESON_TAC[]);;

let EXISTS_IN_SETBIND = prove
 (`!P f:A->B->bool s.
     (?y. y IN SETBIND f s /\ P y) <=>
     (?x y. x IN s /\ y IN f x /\ P y)`,
  REWRITE_TAC[IN_SETBIND] THEN MESON_TAC[]);;

let SETBIND_LID = prove
 (`!s. SETBIND (\x:A. {x}) s = s`,
  GEN_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET] THEN CONJ_TAC THEN
  REWRITE_TAC[FORALL_IN_SETBIND] THEN REWRITE_TAC[IN_SETBIND] THEN SET_TAC[]);;

let SETBIND_SETBIND = prove
 (`! (f:A->B->bool) (g:B->C->bool) s.
     SETBIND g (SETBIND f s) = SETBIND (SETBIND g o f) s`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_SETBIND;
              IMP_CONJ; RIGHT_FORALL_IMP_THM; o_THM] THEN
  REWRITE_TAC[IN_SETBIND; o_THM] THEN MESON_TAC[]);;

let SETBIND_UNION = prove
 (`!f:A->B->bool s t. SETBIND f (s UNION t) = SETBIND f s UNION SETBIND f t`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_SETBIND;
              FORALL_IN_UNION; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_SETBIND; IN_UNION] THEN MESON_TAC[])

let SETBIND_MONO = prove
 (`!f:A->B->bool s t. s SUBSET t ==> SETBIND f s SUBSET SETBIND f t`,
  REWRITE_TAC[SUBSET; FORALL_IN_SETBIND] THEN REWRITE_TAC[IN_SETBIND] THEN
  MESON_TAC[]);;

let SETBIND_SUBSET = prove
 (`!f g:A->B->bool s. (!x. x IN s ==> f x SUBSET g x)
                      ==> SETBIND f s SUBSET SETBIND g s`,
  REWRITE_TAC[SUBSET; FORALL_IN_SETBIND] THEN
  REWRITE_TAC[IN_SETBIND] THEN MESON_TAC[]);;

let SETBIND_EXTENS = prove
 (`!f g:A->B->bool s. (!x. x IN s ==> f x = g x)
                      ==> SETBIND f s = SETBIND g s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  ASM_MESON_TAC[SETBIND_SUBSET; SUBSET_REFL]);;

let IMAGE_EQ_SETBIND = prove
 (`!f:A->B s. IMAGE f s = SETBIND (\x. {f x}) s`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET;
              FORALL_IN_IMAGE; FORALL_IN_SETBIND] THEN
  REWRITE_TAC[IN_IMAGE; IN_SETBIND] THEN SET_TAC[]);;

let UNIONS_EQ_SETBIND = prove
 (`!u:(A->bool)->bool. UNIONS u = SETBIND I u`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET;
              FORALL_IN_UNIONS; FORALL_IN_SETBIND] THEN
  REWRITE_TAC[IN_UNIONS; IN_SETBIND; I_THM] THEN SET_TAC[]);;

let IMAGE_SETBIND = prove
 (`!f:B->C u:A->B->bool s.
     IMAGE f (SETBIND u s) = SETBIND (IMAGE f o u) s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_SETBIND; o_THM;
              IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_SETBIND; IN_IMAGE; o_THM] THEN MESON_TAC[]);;