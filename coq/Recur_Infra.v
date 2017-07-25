Set Implicit Arguments.
Require Import LibLN.
Require Import Recur_ott.
Implicit Types x : var.

(* Syntax *)

Notation "{ k ~> u } t" := (open_trm_wrt_trm_rec k u t) (at level 67).
Notation "t ^^ u" := (open_trm_wrt_trm t u) (at level 67).
Notation "t ^ x" := (open_trm_wrt_trm t (trm_var_f x)).

Definition body t :=
  exists L, forall x, x \notin L -> lc_trm (t ^ x). 

Definition relation := trm -> trm -> Prop.

Notation "t --> t'" := (reduct t t') (at level 67).

(* Typing *)

Implicit Types E : env.

Scheme sub_induct := Induction for sub Sort Prop
  with wf_induct := Induction for wf Sort Prop.

Lemma sub_sub' : forall A (G:env) (e1 e2 B:trm),
  sub G e1 e2 A ->
  sub G A B trm_star ->
  sub G e1 e2 B.
Proof.
  intros. eauto 2.
Qed.

(* infrastructure *)
Definition fv := fv_trm.
Definition subst z u t := subst_trm u z t.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

Fixpoint close_var_rec (k : nat) (z : var) (t : trm) {struct t} : trm :=
  match t with
  | trm_var_b i        => trm_var_b i 
  | trm_var_f x        => If x = z then (trm_var_b k) else (trm_var_f x)
  | trm_star          => trm_star
  | trm_top           => trm_top
  | trm_app t1 t2     => trm_app (close_var_rec k z t1) (close_var_rec k z t2)
  | trm_abs t0 t1 t2  => trm_abs (close_var_rec k z t0) (close_var_rec k z t1) (close_var_rec (S k) z t2) 
  | trm_prod t0 t1 t2 => trm_prod (close_var_rec k z t0) (close_var_rec k z t1) (close_var_rec (S k) z t2) 
  | trm_mu t0 t1      => trm_mu (close_var_rec k z t0) (close_var_rec (S k) z t1)
  | trm_castup t1 t2  => trm_castup (close_var_rec k z t1) (close_var_rec k z t2)
  | trm_castdn t1     => trm_castdn (close_var_rec k z t1)
  | trm_anno t1 t2    => trm_anno (close_var_rec k z t1) (close_var_rec k z t2)
  end.

Definition close_var z t := close_var_rec 0 z t.

Definition contains_terms E :=
  forall x T U, binds x (bind_sub T U) E -> lc_trm T /\ lc_trm U.

Definition red_regular (R : relation) :=
  forall t t', R t t' -> lc_trm t /\ lc_trm t'.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv x) in
  let D := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u C \u D).

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

Ltac exists_fresh := 
  let L := gather_vars_with (fun x : vars => x) in exists L.

Lemma open_rec_term_core :forall e j v i u, i <> j ->
  {j ~> v}e = {i ~> u}({j ~> v}e) -> e = {i ~> u}e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*.
Qed.

Lemma open_rec_term : forall t u,
  lc_trm t -> forall k, t = {k ~> u}t.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open_trm_wrt_trm. pick_fresh x.
   apply* (@open_rec_term_core e2 0 (trm_var_f x)).
  unfolds open_trm_wrt_trm. pick_fresh x. 
   apply* (@open_rec_term_core B 0 (trm_var_f x)).
  unfolds open_trm_wrt_trm. pick_fresh x. 
   apply* (@open_rec_term_core e 0 (trm_var_f x)).
Qed.

Lemma subst_fresh : forall x t u, 
  x \notin fv t -> [x ~> u] t = t.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*. 
Qed.

Lemma subst_open : forall x u t1 t2, lc_trm u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold open_trm_wrt_trm. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* open_rec_term.
Qed.

Lemma subst_open_var : forall x y u e, y <> x -> lc_trm u ->
  ([x ~> u]e) ^ y = [x ~> u] (e ^ y).
Proof.
  introv Neq Wu. rewrite* subst_open.
  simpl. case_var*.
Qed.

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> lc_trm u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite* subst_open.
  rewrite* subst_fresh. simpl. case_var*.
Qed.

Ltac cross := 
  rewrite subst_open_var; try cross.

Tactic Notation "cross" "*" := 
  cross; autos*.

Lemma subst_term : forall t z u,
  lc_trm u -> lc_trm t -> lc_trm ([z ~> u]t).
Proof.
  induction 2; simple*.
  case_var*.
  apply_fresh* lc_trm_abs as y. rewrite* subst_open_var.
  apply_fresh* lc_trm_prod as y. rewrite* subst_open_var.
  apply_fresh* lc_trm_mu as y. rewrite* subst_open_var.
Qed.

Lemma open_term : forall t u,
  body t -> lc_trm u -> lc_trm (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y.
  rewrite* (@subst_intro y). apply* subst_term.
Qed.

Hint Resolve subst_term open_term.

Lemma lc_trm_abs0 : forall t1 t2 t0,
  lc_trm (trm_abs t0 t1 t2) -> lc_trm t0.
Proof.
  intros. inversion* H.
Qed.

Lemma lc_trm_abs1 : forall t0 t2 t1,
  lc_trm (trm_abs t0 t1 t2) -> lc_trm t1.
Proof.
  intros. inversion* H.
Qed.

Lemma body_abs2 : forall t0 t1 t2,  
  lc_trm (trm_abs t0 t1 t2) -> body t2.
Proof.
  intros. unfold body. inversion* H.
Qed.

Lemma lc_trm_prod0 : forall t1 t2 t0,
  lc_trm (trm_prod t0 t1 t2) -> lc_trm t0.
Proof.
  intros. inversion* H.
Qed.

Lemma lc_trm_prod1 : forall t0 t2 t1,
  lc_trm (trm_prod t0 t1 t2) -> lc_trm t1.
Proof.
  intros. inversion* H.
Qed.

Lemma body_prod2 : forall t0 t1 t2,  
  lc_trm (trm_prod t0 t1 t2) -> body t2.
Proof.
  intros. unfold body. inversion* H.
Qed.

Lemma lc_trm_mu1 : forall t1 t0,
  lc_trm (trm_mu t0 t1) -> lc_trm t0.
Proof.
  intros. inversion* H.
Qed.

Lemma body_mu2 : forall t0 t1,  
  lc_trm (trm_mu t0 t1) -> body t1.
Proof.
  intros. unfold body. inversion* H.
Qed.

Hint Extern 1 (lc_trm ?t0) =>
  match goal with
  | H: lc_trm (trm_abs t0 ?t1 ?t2) |- _ => apply (@lc_trm_abs0 t1 t2)
  | H: lc_trm (trm_prod t0 ?t1 ?t2) |- _ => apply (@lc_trm_prod0 t1 t2)
  | H: lc_trm (trm_mu t0 ?t1) |- _ => apply (@lc_trm_mu1 t1)
  end.

Hint Extern 1 (lc_trm ?t1) =>
  match goal with
  | H: lc_trm (trm_abs ?t0 t1 ?t2) |- _ => apply (@lc_trm_abs1 t0 t2)
  | H: lc_trm (trm_prod ?t0 t1 ?t2) |- _ => apply (@lc_trm_prod1 t0 t2)
  end.

Hint Extern 3 (body ?t) =>
  match goal with 
  | H: context [trm_abs ?t0 ?t1 t] |- _ => apply (@body_abs2 t0 t1)
  | H: context [trm_prod ?t0 ?t1 t] |- _ => apply (@body_prod2 t0 t1)
  | H: context [trm_mu ?t0 t] |- _ => apply (@body_mu2 t0)
  end.

Hint Extern 1 (body ?t) =>
  match goal with 
  | H: context [t ^ _] |- _ =>
      let x := fresh in let Fr := fresh in
      let P := fresh in
      let L := gather_vars in exists L; intros x Fr; 
      lets P: H x __; [ notin_solve 
                      | try destructs P ]
  end.

Lemma lc_trm_abs_prove : forall t0 t1 t2,
  lc_trm t0 -> lc_trm t1 -> body t2 -> lc_trm (trm_abs t0 t1 t2).
Proof.
  intros. apply_fresh* lc_trm_abs as x.
Qed.

Lemma lc_trm_prod_prove : forall t0 t1 t2,
  lc_trm t0 -> lc_trm t1 -> body t2 -> lc_trm (trm_prod t0 t1 t2).
Proof.
  intros. apply_fresh* lc_trm_prod as x.
Qed.

Lemma lc_trm_mu_prove : forall t0 t1,
  lc_trm t0 -> body t1 -> lc_trm (trm_mu t0 t1).
Proof.
  intros. apply_fresh* lc_trm_mu as x.
Qed.

Hint Resolve lc_trm_abs_prove lc_trm_prod_prove lc_trm_mu_prove.

Lemma body_prove : forall L t,
  (forall x, x \notin L -> lc_trm (t ^ x)) -> body t.
Proof.
  intros. exists* L.
Qed.

Hint Extern 1 (body ?t) =>
  match goal with 
  | H: forall _, _ \notin ?L -> lc_trm (t ^ _)  |- _ =>
    apply (@body_prove L)
  end. 

Lemma body_subst : forall x t u,
  lc_trm u -> body t -> body ([x ~> u]t).
Proof.
  introv. intros Wu [L Bt].
  exists (\{x} \u L). intros y Fr. cross*.
Qed.

Hint Resolve body_subst.

Lemma open_var_inj : forall x t1 t2, 
  x \notin (fv t1) -> x \notin (fv t2) -> 
  (t1 ^ x = t2 ^ x) -> (t1 = t2).
Proof.
  intros x t1. unfold open_trm_wrt_trm. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal* 
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

Lemma close_var_rec_open : forall x y z t1 i j,
  i <> j -> y <> x -> y \notin (fv t1) ->
    {i ~> trm_var_f y} ({j ~> trm_var_f z} (close_var_rec j x t1) )
  = {j ~> trm_var_f z} (close_var_rec j x ({i ~> trm_var_f y}t1) ).
Proof.
  induction t1; simpl; intros; try solve [ f_equal* ].
  do 2 (case_nat; simpl); try solve [ case_var* | case_nat* ]. 
  case_var*. simpl. case_nat*. 
Qed.

Lemma close_var_fresh : forall x t,
  x \notin fv (close_var x t).
Proof.
  introv. unfold close_var. generalize 0.
  induction t; intros k; simpls; notin_simpl; auto.
  case_var; simple*.
Qed.

Lemma close_var_body : forall x t,
  lc_trm t -> body (close_var x t).
Proof.
  introv W. exists \{x}. intros y Fr.
  unfold open_trm_wrt_trm, close_var. generalize 0. gen y.
  induction W; intros y Fr k; simpls; try solve [autos*].
  case_var; simple*. case_nat*.
  apply_fresh* lc_trm_abs as z.
   unfolds open_trm_wrt_trm. rewrite* close_var_rec_open.
  apply_fresh* lc_trm_prod as z.
   unfolds open_trm_wrt_trm. rewrite* close_var_rec_open.
  apply_fresh* lc_trm_mu as z.
   unfolds open_trm_wrt_trm. rewrite* close_var_rec_open.
Qed.

Lemma close_var_open : forall x t,
  lc_trm t -> t = (close_var x t) ^ x.
Proof.
  introv W. unfold close_var, open_trm_wrt_trm. generalize 0.
  induction W; intros k; simpls; f_equal*.
  case_var*. simpl. case_nat*.
  let L := gather_vars in match goal with |- _ = ?t => 
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open_trm_wrt_trm. rewrite* close_var_rec_open.
  let L := gather_vars in match goal with |- _ = ?t => 
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open_trm_wrt_trm. rewrite* close_var_rec_open.
  let L := gather_vars in match goal with |- _ = ?t => 
    destruct (var_fresh (L \u fv t)) as [y Fr] end.
  apply* (@open_var_inj y).
  unfolds open_trm_wrt_trm. rewrite* close_var_rec_open.
Qed. 

Lemma close_var_spec : forall t x, lc_trm t -> 
  exists u, t = u ^ x /\ body u /\ x \notin (fv u).
Proof.
  intros. exists (close_var x t). splits 3.
  apply* close_var_open.
  apply* close_var_body.
  apply* close_var_fresh.
Qed. 

Lemma ivalue_is_term : forall t, ivalue t -> lc_trm t.
Proof.
  intros_all. induction* H.
Qed.

Lemma value_is_term : forall t, value t -> lc_trm t.
Proof.
  intros_all. induction* H.
  apply* ivalue_is_term.
Qed.

Hint Extern 1 (lc_trm ?t) => match goal with
  | H: ivalue t |- _ => apply (ivalue_is_term H)
  | H: value t |- _ => apply (value_is_term H) end.

Lemma red_regular_reduct : red_regular reduct.
Proof.
  intros_all. induction* H.
Qed.

Hint Extern 1 (lc_trm ?t) => match goal with
  | H: reduct t _ |- _ => apply (proj1 (red_regular_reduct H))
  | H: reduct _ t |- _ => apply (proj2 (red_regular_reduct H))
  end.

Hint Extern 1 (lc_trm (trm_abs ([?x ~> ?u]?t0) ([?x ~> ?u]?t1) ([?x ~> ?u]?t2))) =>
  match goal with H: lc_trm (trm_abs t0 t1 t2) |- _ => 
  unsimpl ([x ~> u](trm_abs t0 t1 t2)) end.

Hint Extern 1 (lc_trm (trm_prod ([?x ~> ?u]?t0) ([?x ~> ?u]?t1) ([?x ~> ?u]?t2))) =>
  match goal with H: lc_trm (trm_prod t0 t1 t2) |- _ => 
  unsimpl ([x ~> u](trm_prod t0 t1 t2)) end.

Lemma regular_sub : forall G e1 e2 A,
  sub G e1 e2 A ->
  (wf G /\ ok G /\ contains_terms G /\ lc_trm e1 /\ lc_trm e2 /\ lc_trm A). 
Proof.
  apply sub_induct with
  (P0 := fun E (_ : wf E) => ok E /\ contains_terms E);
    unfolds contains_terms; intros; splits*.
  destruct H as [? ?].
  destructs~ (H0 _ e A b).
  intros. false* binds_empty_inv.
  intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]].
    inversion H3. subst*.
    destruct H0 as (? & ? & HH & ?). apply* HH.
Qed.

Hint Extern 1 (lc_trm ?t) => match goal with
  | H: sub _ t _ _ |- _ => apply (proj31 (proj44 (regular_sub H)))
  | H: sub _ _ t _ |- _ => apply (proj32 (proj44 (regular_sub H)))
  | H: sub _ _ _ t |- _ => apply (proj33 (proj44 (regular_sub H)))
  end.

Lemma ok_from_wf : forall G, wf G -> ok G.
Proof.
  induction 1. auto. autos* (regular_sub H0).
Qed.

Hint Extern 1 (ok ?E) => match goal with
  | H: wf E |- _ => apply (ok_from_wf H)
  end.

Hint Extern 1 (wf ?E) => match goal with
  | H: sub E _ _ _ |- _ => apply (proj1 (regular_sub H))
  end.

Lemma wf_push_inv : forall G x A B,
  wf (G & x ~ bind_sub A B) -> wf G /\ lc_trm A /\ lc_trm B.
Proof.
  introv W. inversions W. 
  false (empty_push_inv H0).
  destruct (eq_push_inv H) as [? [? ?]]. inversion H3.
  subst~.
  destruct (eq_push_inv H) as [? [? ?]]. inversion H4.
  subst~.
Qed.

Lemma lc_trm_from_binds_in_wf : forall x E T U,
  wf E -> binds x (bind_sub T U) E -> lc_trm T /\ lc_trm U.
Proof.
  introv W Has. gen E. induction E using env_ind; intros.
  false* binds_empty_inv.
  induction v.
  destruct (wf_push_inv W). 
  destruct (binds_push_inv Has) as [[? ?] | [? ?]].
  inversion H2. subst*.
  apply* IHE.
Qed.

Lemma lc_trm_from_binds_in_wf_left : forall x E T U,
  wf E -> binds x (bind_sub T U) E -> lc_trm T.
Proof.
  intros. destruct~ (lc_trm_from_binds_in_wf H H0).
Qed.

Lemma lc_trm_from_binds_in_wf_right : forall x E T U,
  wf E -> binds x (bind_sub T U) E -> lc_trm U.
Proof.
  intros. destruct~ (lc_trm_from_binds_in_wf H H0).
Qed.

Hint Extern 1 (lc_trm ?t) => match goal with
  | H: binds ?x (bind_sub t ?t2) ?E |- _ => apply (@lc_trm_from_binds_in_wf_left x E)
  | H: binds ?x (bind_sub ?t2 t) ?E |- _ => apply (@lc_trm_from_binds_in_wf_right x E)
  end.

Lemma wf_left : forall E F : env,
  wf (E & F) -> wf E.
Proof.
  intros. induction F using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in H.
   inversions H. false (empty_push_inv H1).
   destruct (eq_push_inv H0) as [? [? ?]]. subst~. 
Qed.

Implicit Arguments wf_left [E F].

Lemma fv_open_var : forall y x t,
  x <> y -> x \notin fv (t ^ y) -> x \notin fv t.
Proof.
  introv Neq. unfold open_trm_wrt_trm. generalize 0. 
  induction t; simpl; intros; try notin_solve.
  specializes IHt1 n. auto. specializes IHt2 n. auto.
  specializes IHt1 n. auto. specializes IHt2 n. auto. specializes IHt3 (S n). auto.
  specializes IHt1 n. auto. specializes IHt2 n. auto. specializes IHt3 (S n). auto.
  specializes IHt1 n. auto. specializes IHt2 (S n). auto.
  specializes IHt1 n. auto. specializes IHt2 n. auto.
  specializes IHt n. auto.
  specializes IHt1 n. auto. specializes IHt2 n. auto.
Qed.

Lemma fresh_false : forall G x (v:binding),
  x # G & x ~ v -> False.
Proof.
  intros. simpl_dom.
  destruct (notin_union x \{x} (dom G)) as [H1 _].
  lets: H1 H.
  destruct H0 as [H3 _].
  apply* notin_same.
Qed.

Lemma and_simpl : forall (A : Prop),
    A -> A /\ A.
Proof.
  intros. auto.
Qed.

Lemma fv_open_term : forall A B x,
  x \notin fv A -> x \notin fv B ->
  x \notin fv (A ^^ B).
Proof.
  intros A. unfold open_trm_wrt_trm. generalize 0. 
  induction A; simpl; intros; try (notin_simpl); autos*.
  case_nat~. 
Qed.

Lemma fv_close_var : forall y x t,
  x <> y -> x \notin fv t -> x \notin fv (t ^ y).
Proof.
  introv Neq. unfold open_trm_wrt_trm. generalize 0. 
  induction t; simpl; intros; try notin_solve; try autos*.
  case_nat~. simpl. auto.
Qed.

Lemma sub_fresh : forall G A B C x,
  sub G A B C -> x # G -> (x \notin fv A) /\ (x \notin fv B).
Proof.
  introv Typ.
  induction Typ; simpls; intros; try (apply and_simpl).
  auto.
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H0 H1.
  split.
    rewrite notin_singleton. intro. subst. applys binds_fresh_inv H H0.
    apply* IHTyp.
  splits*. 
  auto.
  destruct (IHTyp1 H3).
  destruct (IHTyp2 H3).
  split; notin_simpl; auto.
  pick_fresh y. apply* (@fv_open_var y).
  destruct (H0 y). auto. auto. auto.
  pick_fresh y. apply* (@fv_open_var y).
  destruct (H0 y). auto. auto. auto.
  splits*.
  destruct (IHTyp1 H3).
  destruct (IHTyp2 H3).
  split; notin_simpl; auto.
  pick_fresh y. apply* (@fv_open_var y).
  destruct (H0 y). auto. auto. auto.
  pick_fresh y. apply* (@fv_open_var y).
  destruct (H2 y). auto. auto. auto.
  notin_simpl; auto. apply* IHTyp.
  pick_fresh y. apply* (@fv_open_var y).
  destruct (H0 y). auto. auto. auto.
  splits*.
  splits*.
  auto.
Qed.

Lemma notin_fv_from_wf : forall E F x U T,
  wf (E & x ~ bind_sub U T & F) -> x \notin fv T.
Proof.
  intros.
  lets W: (wf_left H). inversions W.
  false (empty_push_inv H1). 
  destruct (eq_push_inv H0) as [? [? ?]]. inversion H5. subst~.
  apply* sub_fresh.
Qed.

Lemma notin_fv_from_binds_right : forall x y T U E,
  wf E -> binds y (bind_sub T U) E -> x # E -> x \notin fv U.
Proof.
  induction E using env_ind; intros.
  false* binds_empty_inv.
  induction v.
  destruct (wf_push_inv H).
    destruct (binds_push_inv H0) as [[? ?] | [? ?]].
    inversion H5. subst. inversions H. false* (empty_push_inv H6).
     destruct (eq_push_inv H4) as [? [? ?]].  inversion H9. subst~. 
     apply* sub_fresh.
    autos*.
Qed.

Lemma notin_fv_from_binds : forall x y T U E,
  wf E -> binds y (bind_sub T U) E -> x # E -> x \notin fv T /\ x \notin fv U.
Proof.
  induction E using env_ind; intros.
  false* binds_empty_inv.
  induction v.
  destruct (wf_push_inv H).
    destruct (binds_push_inv H0) as [[? ?] | [? ?]].
    inversion H5. subst. inversions H. false* (empty_push_inv H6).
     destruct (eq_push_inv H4) as [? [? ?]].  inversion H9. subst~. 
     split; apply* sub_fresh.
    autos*.
Qed.

Lemma notin_fv_from_binds' : forall E F x V1 V2 y U1 U2,
  wf (E & x ~ bind_sub V1 V2 & F) -> 
  binds y (bind_sub U1 U2) E ->
  x \notin fv U1 /\ x \notin fv U2.
Proof.
  intros. lets W: (wf_left H). inversions keep W.
  false (empty_push_inv H2). 
  destruct (eq_push_inv H1) as [? [? ?]]. inversion H5. subst~. 
  lets W': (wf_left W). apply* notin_fv_from_binds.
Qed.

Lemma notin_fv_from_binds'_left : forall E F x V y U1 U2,
  wf (E & x ~ V & F) -> 
  binds y (bind_sub U1 U2) E ->
  x \notin fv U1.
Proof.
  intros. induction V.
  destruct~ (notin_fv_from_binds' H H0).
Qed.
  
Lemma notin_fv_from_binds'_right : forall E F x V y U1 U2,
  wf (E & x ~ V & F) -> 
  binds y (bind_sub U1 U2) E ->
  x \notin fv U2.
Proof.
  intros. induction V.
  destruct~ (notin_fv_from_binds' H H0).
Qed.

Hint Extern 1 (?x \notin fv ?V) => 
  match goal with H: wf (?E & x ~ (bind_sub ?U V) & ?F) |- _ =>
    apply (@notin_fv_from_wf E F) end.

Hint Extern 1 (?x \notin fv ?U) => 
  match goal with H: wf (?E & x ~ ?V & ?F), B: binds ?y (bind_sub U ?U') ?E |- _ =>
    apply (@notin_fv_from_binds'_left E F x V y) end.

Hint Extern 1 (?x \notin fv ?U) => 
  match goal with H: wf (?E & x ~ ?V & ?F), B: binds ?y (bind_sub ?U' U) ?E |- _ =>
    apply (@notin_fv_from_binds'_right E F x V y) end.

