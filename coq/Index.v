(** This file contains main results of the paper **)

Require Import LibLN.
Require Main_ott Main_Proofs.
Require Recur_ott Recur_Proofs.
Require Full_ott Full_Proofs.
Require Alg_Proofs.

(* ******* Definition ******* *)

(* Lemmas in Section 4 *)

Module Type Metatheory.
  
(* **** Syntax and Relations **** *)

  (* Term *)
  Parameter trm : Set.
  Parameter trm_star : trm.

  (* Context *)
  Parameter binding : Set.
  Parameter bind_sub : trm -> trm -> binding.
  Definition env := LibEnv.env binding.
  Notation "x ~< e ~: A" := (x ~ bind_sub e A) (at level 20).
    (* In paper: x <: e : A *)

  (* Substitution *)
  Parameter subst : var -> trm -> trm -> trm.
  Parameter substenv : var -> trm -> binding -> binding.
  Notation "t [ z := u ]" := (subst z u t) (at level 68).
  Notation "t [[ z := u ]]" := (map (substenv z u) t) (at level 68).

  (* Operational Semantics *)
  Parameter reduct : trm -> trm -> Prop.
  Parameter value : trm -> Prop.
  Notation "t1 --> t2" := (reduct t1 t2) (at level 67).

  (* Unified Subtyping *)
  Parameter sub : env -> trm -> trm -> trm -> Prop.
  Notation "G |= e1 << e2 ~: A" := (sub G e1 e2 A) (at level 67).
    (* In paper: G |- e1 <: e2 : A *)
  Notation "G |= e ~: A" := (sub G e e A) (at level 67).
    (* In paper: G |- e : A *)

  (* Context Well-formedness *)
  Parameter wf : env -> Prop.
  Notation "|= G" := (wf G) (at level 67).
    (* In paper: |- G *)

(* **** Lemmas **** *)
  
  (* Lemma 4.1: Reflexivity *)
  Parameter lem_reflexivity : forall G e1 e2 A,
    G |= e1 << e2 ~: A ->
    G |= e1 ~: A /\ G |= e2 ~: A.

  (* Lemma 4.2: Left Reflexivity *)
  Parameter lem_left_reflexivity : forall G e1 e2 A,
    G |= e1 << e2 ~: A -> 
    G |= e1 ~: A.

  (* Lemma 4.3: Right Reflexivity *)
  Parameter lem_right_reflexivity : forall G e1 e2 A,
    G |= e1 << e2 ~: A -> 
    G |= e2 ~: A.

  (* Lemma 4.4: Weakening *)
  Parameter lem_weakening : forall G3 G1 G2 e1 e2 A,
    G1 & G3 |= e1 << e2 ~: A ->
    |= G1 & G2 & G3 ->
    G1 & G2 & G3 |= e1 << e2 ~: A.

  (* Lemma 4.5: Consistency of Typing *)
  Parameter lem_consistency_of_typing : forall B G e1 e2 A,
    G |= e1 ~: A -> 
    G |= e1 << e2 ~: B ->
    G |= e1 << e2 ~: A.

  (* Lemma 4.6: Type Narrowing *)
  Parameter lem_type_narrowing : forall e A B G2 G1 C x e1 e2,
    G1 & x ~< e ~: B & G2 |= e1 << e2 ~: C ->
    G1 |= e ~: A ->
    G1 |= A << B ~: trm_star  ->
    G1 & x ~< e ~: A & G2 |= e1 << e2 ~: C.

  (* Lemma 4.7: Bound Narrowing *)
  Parameter lem_bound_narrowing : forall e G2 G1 B C x e' e1 e2,
    G1 & x ~< e ~: B & G2 |= e1 << e2 ~: C ->
    G1 |= e' << e ~: B ->
    G1 & x ~< e' ~: B & G2 |= e1 << e2 ~: C.

  (* Lemma 4.8: Generalized Transitivity *)
  Parameter lem_generalized_transitivity : forall e2 G e1 e3 A B,
    G |= e1 << e2 ~: A ->
    G |= e2 << e3 ~: B ->
    G |= e1 << e3 ~: A.

  (* Lemma 4.9: Transitivity *)
  Parameter lem_transitivity : forall e2 G e1 e3 A,
    G |= e1 << e2 ~: A ->
    G |= e2 << e3 ~: A ->
    G |= e1 << e3 ~: A.

  (* Lemma 4.10: Substitution *)
  Parameter lem_substitution : forall B e (G2:env) e' (G1:env) x e1 e2 A,
    G1 |= e' << e ~: B ->
    G1 & x ~< e ~: B & G2 |= e1 << e2 ~: A ->
    G1 & (G2 [[x := e']]) |= (e1 [x := e']) << (e2 [x := e']) ~: (A [x := e']).

  (* Lemma 4.11: Correctness of Types *)
  Parameter lem_correctness_of_types : forall G e1 e2 A,
    G |= e1 << e2 ~: A ->
    G |= A ~: trm_star.

  (* Lemma 4.12: Determinacy of Reduction *)
  Parameter lem_determinacy_of_reduction : forall e e1 e2,
    e --> e1 -> e --> e2 -> e1 = e2.

  (* Lemma 4.13: Type Preservation *)
  Parameter lem_type_preservation : forall G e e' A,
    G |= e ~: A ->
    e --> e' ->
    G |= e' ~: A.

  (* Lemma 4.14: Subtype Preservation *)
  Parameter lem_subtype_preservation : forall G e1 e2 e1' e2' A,
    G |= e1 << e2 ~: A -> 
    e1 --> e1' ->
    e2 --> e2' ->
    G |= e1' << e2' ~: A.

  (* Lemma 4.15: Generalized Subtype Preservation *)
  Parameter SubLemma : env -> trm -> trm -> trm -> Prop.
  (* SubLemma is defined as follows: *)
  (* Definition SubLemma G e1 e2 A := *)
  (*   match e1,e2 with *)
  (*   | trm_castup B e1',trm_castup _ e2' => forall A' B', *)
  (*       A --> A' -> B --> B' -> G |= e1' << e2' ~: A' *)
  (*   | _,_ => forall e1' e2', *)
  (*       e1 --> e1' -> e2 --> e2' -> G |= e1' << e2' ~: A *)
  (*   end. *)
  Parameter lem_generalized_subtype_preservation : forall G e1 e2 A,
    G |= e1 << e2 ~: A -> SubLemma G e1 e2 A.

  (* Lemma 4.16: Reduction Exists in the Middle *)
  Parameter lem_reduction_exists_in_the_middle : forall G B A A' C C' D,
    G |= B << A ~: D ->
    A --> A' ->
    G |= C << B ~: D ->
    C --> C' ->
    exists B', B --> B'.

  (* Lemma 4.17: Progress *)
  Parameter lem_progress : forall e A,
    empty |= e ~: A ->
    value e \/ exists e', e --> e'.

  (* Lemma 4.18: Generalized Progress *)
  Parameter lem_generalized_progress : forall G e A,
    G |= e ~: A ->
    value e \/ exists e', e --> e'.

End Metatheory.

(* Theorems in Section 5 *)

Module Type Algorithmic.

(* **** Syntax and Relations **** *)

  (* Term *)
  Parameter trm : Set.
  
  (* Context *)
  Parameter binding : Set.
  Definition env := LibEnv.env binding.

  (* Unified Subtyping *)
  Parameter sub : env -> trm -> trm -> trm -> Prop.
  Notation "G |= e1 << e2 ~: A" := (sub G e1 e2 A) (at level 67).
    (* In paper: G |- e1 <: e2 : A *)

  (* Erasure *)
  Parameter erasure : trm -> trm.
  Notation "[# e #]" := (erasure e) (at level 2).
    (* In paper: |e| *)
  Parameter rem_anno_env : binding -> binding.
  Notation "{# G #}" := (map rem_anno_env G) (at level 2).
    (* In paper: |G| *)

  (* Algorithmic Subtyping *)
  Parameter dsub : env -> trm -> trm -> Prop.

  (* Bidirectional Typing *)
  Parameter dir : Set. (* Directions *)
  Parameter inf : dir. (* Synthesis direction *)
  Parameter dtyping : dir -> env -> trm -> trm -> Prop.

(* **** Theorems **** *)
  
  (* Theorem 5.1: Soundness of Algorithm *)
  Parameter lem_soundness : forall G d e1 e2 A,
    dtyping d G e1 A -> 
    dtyping d G e2 A ->
    dsub G e1 e2 ->
    {#G#} |= [#e1#] << [#e2#] ~: [#A#].

  (* Theorem 5.2: Completeness of Algorithm *)
  Parameter lem_completeness : forall G e1 e2 A,
     G |= e1 << e2 ~: A ->
     dsub G e1 e2 /\
     exists e1' e2',
       dtyping inf G e1' A /\ 
       dtyping inf G e2' A /\
       [#e1'#] = e1 /\ 
       [#e2'#] = e2.

End Algorithmic.

(* ******* Verification ******* *)

(* "Main" variant implements all lemmas in Section 4 *)

Module MainImpl : Metatheory.
  Module M := Main_ott.
  Module P := Main_Proofs.
  Definition trm := M.trm.
  Definition trm_star := M.trm_star.
  Definition binding := M.binding.
  Definition bind_sub := M.bind_sub.
  Definition env := M.env.
  Definition subst z u t := M.subst_trm u z t.
  Definition substenv := P.substenv.
  Definition reduct := M.reduct.
  Definition value := M.value.
  Definition sub := M.sub.
  Definition wf := M.wf.

  Definition lem_reflexivity := P.sub_refl.
  Definition lem_left_reflexivity := P.sub_refl_left.
  Definition lem_right_reflexivity := P.sub_refl_right.
  Definition lem_weakening := P.sub_weaken.
  Definition lem_consistency_of_typing := P.sub_typekeep.
  Definition lem_type_narrowing := P.sub_narrowing_typ.
  Definition lem_bound_narrowing := P.sub_narrowing.
  Definition lem_generalized_transitivity := P.sub_trans_aux.
  Definition lem_transitivity := P.sub_trans.
  Definition lem_substitution := P.sub_substitution.
  Definition lem_correctness_of_types := P.sub_wf_from_sub.
  Definition lem_determinacy_of_reduction := P.reduct_determ.
  Definition lem_type_preservation := P.subject_reduction_wh.
  Definition lem_subtype_preservation := P.sub_reduct_preserve.
  Definition SubLemma := P.SubLemma.
  Definition lem_generalized_subtype_preservation := P.sub_reduct_preserve1.
  Definition lem_reduction_exists_in_the_middle := P.sub_reduct_middle.
  Definition lem_progress := P.progress_empty_wh.
  Definition lem_generalized_progress := P.progress_wh.
End MainImpl.

(* "Recur" variant implements all lemmas in Section 4 *)

Module RecurImpl : Metatheory.
  Module M := Recur_ott.
  Module P := Recur_Proofs.
  Definition trm := M.trm.
  Definition trm_star := M.trm_star.
  Definition binding := M.binding.
  Definition bind_sub := M.bind_sub.
  Definition env := M.env.
  Definition subst z u t := M.subst_trm u z t.
  Definition substenv := P.substenv.
  Definition reduct := M.reduct.
  Definition value := M.value.
  Definition sub := M.sub.
  Definition wf := M.wf.

  Definition lem_reflexivity := P.sub_refl.
  Definition lem_left_reflexivity := P.sub_refl_left.
  Definition lem_right_reflexivity := P.sub_refl_right.
  Definition lem_weakening := P.sub_weaken.
  Definition lem_consistency_of_typing := P.sub_typekeep.
  Definition lem_type_narrowing := P.sub_narrowing_typ.
  Definition lem_bound_narrowing := P.sub_narrowing.
  Definition lem_generalized_transitivity := P.sub_trans_aux.
  Definition lem_transitivity := P.sub_trans.
  Definition lem_substitution := P.sub_substitution.
  Definition lem_correctness_of_types := P.sub_wf_from_sub.
  Definition lem_determinacy_of_reduction := P.reduct_determ.
  Definition lem_type_preservation := P.subject_reduction_wh.
  Definition lem_subtype_preservation := P.sub_reduct_preserve.
  Definition SubLemma := P.SubLemma.
  Definition lem_generalized_subtype_preservation := P.sub_reduct_preserve1.
  Definition lem_reduction_exists_in_the_middle := P.sub_reduct_middle.
  Definition lem_progress := P.progress_empty_wh.
  Definition lem_generalized_progress := P.progress_wh.
End RecurImpl.

(* "Full" variant implements all lemmas in Section 4 *)

Module FullImpl : Metatheory.
  Module M := Full_ott.
  Module P := Full_Proofs.
  Definition trm := M.trm.
  Definition trm_star := M.trm_star.
  Definition binding := M.binding.
  Definition bind_sub := M.bind_sub.
  Definition env := M.env.
  Definition subst z u t := M.subst_trm u z t.
  Definition substenv := P.substenv.
  Definition reduct := M.reduct.
  Definition value := M.value.
  Definition sub := M.sub.
  Definition wf := M.wf.

  Definition lem_reflexivity := P.sub_refl.
  Definition lem_left_reflexivity := P.sub_refl_left.
  Definition lem_right_reflexivity := P.sub_refl_right.
  Definition lem_weakening := P.sub_weaken.
  Definition lem_consistency_of_typing := P.sub_typekeep.
  Definition lem_type_narrowing := P.sub_narrowing_typ.
  Definition lem_bound_narrowing := P.sub_narrowing.
  Definition lem_generalized_transitivity := P.sub_trans_aux.
  Definition lem_transitivity := P.sub_trans.
  Definition lem_substitution := P.sub_substitution.
  Definition lem_correctness_of_types := P.sub_wf_from_sub.
  Definition lem_determinacy_of_reduction := P.reduct_determ.
  Definition lem_type_preservation := P.subject_reduction_wh.
  Definition lem_subtype_preservation := P.sub_reduct_preserve.
  Definition SubLemma := P.SubLemma.
  Definition lem_generalized_subtype_preservation := P.sub_reduct_preserve1.
  Definition lem_reduction_exists_in_the_middle := P.sub_reduct_middle.
  Definition lem_progress := P.progress_empty_wh.
  Definition lem_generalized_progress := P.progress_wh.
End FullImpl.

(* "Alg" proves all theorems in Section 5 *)

Module AlgImpl : Algorithmic.
  Module M := Main_ott.
  Module P := Alg_Proofs.
  Definition trm := M.trm.
  Definition binding := M.binding.
  Definition env := M.env.
  Definition sub := M.sub.
  Definition erasure := P.remove_anno.
  Definition rem_anno_env := P.rem_anno_env.
  Definition dsub := P.dsub.
  Definition dir := P.dir.
  Definition inf := P.inf.
  Definition dtyping := P.dtyping.

  Definition lem_soundness := P.bidir_to_sub.
  Definition lem_completeness := P.sub_to_bidir.
End AlgImpl.

