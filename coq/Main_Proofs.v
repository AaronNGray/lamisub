Set Implicit Arguments.
Require Import LibLN.
Require Import Main_ott Main_Infra.
Implicit Types x : var.

Lemma wf_to_wt : forall G x e A,
  wf (G & x ~ bind_sub e A) -> sub G e e A /\ sub G A A (trm_star).
Proof.
  intros. inversions H.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H0) as [? [? ?]]. inversion H4. subst*.
Qed.

Lemma sub_prod_prod_inv1 : forall G e A B B0 C,
   sub G (trm_prod e A B) (trm_prod e A B0) C ->
   sub G e e A /\
   (sub G A A (trm_star)).
Proof.
  intros. inductions H; eauto.
Qed.

Lemma sub_refl_left : forall G e1 e2 A,
  sub G e1 e2 A ->
  sub G e1 e1 A.
Proof.
  intros. inductions H; try solve [eauto 2].
  apply_fresh* (@sub_prod) as y.
Qed.

Hint Extern 1 (sub ?G ?A ?A ?B) => match goal with
  | H: sub G A _ B |- _ => apply ((sub_refl_left H))
  end.

Lemma sub_weaken : forall G E F t1 t2 T,
  sub (E & G) t1 t2 T ->
  wf (E & F & G) ->
  sub (E & F & G) t1 t2 T.
Proof.
  introv Typ. gen_eq Env: (E & G). gen E F G.
  induction Typ; introv EQ W; subst; eauto.
  (* case: var refl *)
  apply* sub_var_refl. apply* binds_weaken.
  (* case: var trans *)
  apply* sub_var_trans. apply* binds_weaken.
  (* case: trm_abs *)
  lets: (IHTyp1 E F G0 eq_refl W).
  lets: (IHTyp2 E F G0 eq_refl W).
  apply_fresh* (@sub_abs) as y.
  apply_ih_bind* H0.
  apply_ih_bind* H2.
  (* case: trm_prod *)
  apply_fresh* (@sub_prod) as y;
    lets: (IHTyp1 E F G0 eq_refl W);
    lets: (IHTyp2 E F G0 eq_refl W);
    lets: (sub_refl_left H4).
  apply_ih_bind* H0.
  apply_ih_bind* H2.
Qed.

Lemma sub_typekeep' : forall Q E T A B,
  sub E Q T B -> sub E Q Q A -> sub E Q T A.
Proof.
  intros. gen A.
  inductions H; intros; eauto 2.
  inductions H1.
    lets: (binds_func H H2).
    inversions H3. apply* (@sub_var_trans).
    lets: (binds_func H H2).
    inversions H3. apply* (@sub_var_trans).
    autos*.
  inductions H5.
    apply_fresh* sub_abs as y.
    apply* (@sub_sub).
  inductions H1.
    apply sub_app with (B := B0) (e3 := e4). auto. auto.
    apply* (@sub_sub).
  inductions H6.
    apply_fresh* (@sub_prod) as y.
    apply* (@sub_sub).
  inductions H2.
    apply* sub_castup.
    apply* (@sub_sub).
  inductions H2.
    apply sub_castdn with (A := A0). auto. auto. auto.
    apply* (@sub_sub).
Qed.

Lemma sub_typekeep : forall B G e1 e2 A,
  sub G e1 e1 A ->
  sub G e1 e2 B ->
  sub G e1 e2 A.
Proof.
  intros. apply* sub_typekeep'.
Qed.

Lemma sub_narrowing_typ : forall Q A' A F E B Z S T,
  sub (E & Z ~ bind_sub Q A & F) S T B ->
  sub E Q Q A' ->
  sub E A' A (trm_star) ->
  sub (E & Z ~ bind_sub Q A' & F) S T B.
Proof.
  introv Sa Sb Sc.
  gen_eq G: (E & Z ~ bind_sub Q A & F). gen F.
  apply sub_induct with
    (P := fun G S T B (Sub: sub G S T B) =>
            forall F, G = E & Z ~ bind_sub Q A & F ->
                      sub (E & Z ~ bind_sub Q A' & F) S T B)
    (P0 := fun G (W: wf G) =>
            forall F, G = E & Z ~ bind_sub Q A & F ->
                      wf (E & Z ~ bind_sub Q A' & F));
    intros; subst; simpls subst.
   (* case: ax *)
  apply* sub_ax.
  (* case: var refl *)
  rename x5 into x.
  tests EQ: (x = Z).
    asserts~ N1: (wf (E & Z ~ bind_sub Q A' & F)).
    asserts~ N': (ok (E & Z ~ bind_sub Q A & F)).
    lets: (binds_middle_eq_inv b N').
    destruct (ok_middle_inv N').
    inversions H0.
    apply (@sub_sub' A').
    apply sub_var_refl with (e := Q). auto.
    apply* binds_middle_eq.
    apply_empty* sub_weaken.
    apply_empty* sub_weaken.
    asserts* W1: (x # (Z ~ bind_sub Q A)).
    lets: (binds_remove b W1).
    lets: (H F eq_refl).
    apply sub_var_refl with (e := e). auto.
    apply binds_weaken. auto. auto.
  (* case: var trans *)
  rename x5 into x.
  tests EQ: (x = Z).
    asserts~ WF: (wf (E & Z ~ bind_sub Q A & F)).
    asserts~ N: (ok (E & Z ~ bind_sub Q A & F)).
    destruct (ok_middle_inv N).
    lets: (binds_middle_eq_inv b N).
    inversions H2.
    apply (@sub_sub' A').
    apply sub_var_trans with (e1 := Q). auto.
    lets: (H F eq_refl).
    lets: (@sub_typekeep' Q (E & Z ~ bind_sub Q A' & F) e2 A' A).
    apply H3. auto. apply_empty* sub_weaken.
    apply_empty* sub_weaken.
    apply_empty* sub_weaken.
    apply_empty* sub_weaken.
    lets: (H F eq_refl). auto.
    asserts* W1: (x # (Z ~ bind_sub Q A)).
    lets: (binds_remove b W1).
    lets: (H F eq_refl).
    apply sub_var_trans with (e1 := e1). auto.
    apply binds_weaken. auto. 
    asserts* WF: (wf (E & Z ~ bind_sub Q A' & F)). auto.
    auto.
  (* case: top *)
  autos*.
  (* case: top refl *)
  autos*.
  (* case: abs *)
  apply_fresh* sub_abs as Y.
  apply_ih_bind* H1.
  apply_ih_bind* H2.
  (* case: app *)
  autos*.
  (* case: prod *)
  apply_fresh* (@sub_prod) as Y.
  apply_ih_bind* H2. apply_ih_bind* H3.
  (* case: castup *)
  autos*.
  (* case: castdn *)
  autos*.
  (* case: sub *)
  autos*.
  (* case: wf nil *)
  false. apply* empty_middle_inv.
  (* case: wf cons *)
  destruct (env_case F).
    subst. rewrite concat_empty_r.
    rewrite concat_empty_r in H1.
    destruct (eq_push_inv H1) as [? [? ?]].
    inversions H3. apply* wf_cons.
    destruct H2 as [y [v' [E' Eq]]].
    induction v'. subst.
    rewrite concat_assoc.
    rewrite concat_assoc in H1.
    destruct (eq_push_inv H1) as [? [? ?]].
    inversions H3. apply* wf_cons.
  (* conclusion *)
  auto.
Qed.

Definition substenv (x:var) (v:trm) (p:binding) :=
  match p with
  | bind_sub e A => bind_sub (subst x v e) (subst x v A)
  end.

Lemma substenv_eq : forall x v e1 e2,
  bind_sub ([x ~> v] e1) ([x ~> v] e2) = substenv x v (bind_sub e1 e2).
Proof.
  intros. simpls*.
Qed.

Lemma substenv_fresh : forall x t1 t2 u, 
  x \notin fv t1 -> x \notin fv t2 ->
  substenv x u (bind_sub t1 t2) = bind_sub t1 t2.
Proof.
  intros. unfolds substenv.
  rewrite* subst_fresh.
  rewrite* subst_fresh.
Qed.

Lemma notin_fv_from_wf_left : forall E F x U T,
  wf (E & x ~ bind_sub U T & F) -> x \notin fv U.
Proof.
  intros.
  lets W: (wf_left H). inversions W.
  false (empty_push_inv H1). 
  destruct (eq_push_inv H0) as [? [? ?]]. inversion H5. subst~.
  apply* sub_fresh.
Qed.

Lemma map_substenv_fresh : forall x v F, 
  wf F -> x # F -> map (substenv x v) F = F.
Proof.
  intros. induction F using env_ind.
  apply* map_empty.
  rewrite* map_push.
  inductions v0.
  asserts* b: (binds x0 (bind_sub e A) (F & x0 ~ bind_sub e A)).
  lets: (notin_fv_from_binds H b H0).
  destruct H1.
  rewrite* (@substenv_fresh x _ _ v H1 H2).
  lets: wf_left H.
  lets: IHF H3 __. auto.
  rewrite* H4.
Qed.

Definition red_out (R : relation) :=
  forall x u t t', lc_trm u -> R t t' -> 
  R ([x~>u]t) ([x~>u]t').

Lemma reduct_red_out : red_out reduct.
Proof.
  intros_all. induction H0; simpl.
  rewrite* subst_open.
  apply* reduct_app.
  apply* reduct_castdn.
  apply* reduct_castelim.
Qed.

Lemma ivalue_cannot_red : forall t t',
    ivalue t -> reduct t t' -> False.
Proof.
  introv H1. gen t'.
  induction H1; introv H2; inversions H2.
  inversions H1.
  apply* IHivalue.
  apply* IHivalue.
  inversions H1.
Qed.

Lemma value_cannot_red : forall t t',
    value t -> reduct t t' -> False.
Proof.
  introv H1. gen t'.
  induction H1; introv H2;
    try solve [inversions H2; apply* ivalue_cannot_red].
  apply (ivalue_cannot_red H H2).
Qed.

Lemma reduct_determ : forall t t1 t2,
    reduct t t1 -> reduct t t2 -> t1 = t2.
Proof.
  introv H1. gen t2. induction H1; introv HH; inversions HH.
  auto. inversion H7.
  inversions H1.
  pose (IHreduct e1'0 H5). rewrite e. auto.
  pose (IHreduct e1'0 H0). rewrite e. auto.
  inversions H1. inversions H2.
  auto.
Qed.

Definition transitivity_on Q := forall E S T A,
  sub E S Q A -> sub E Q T A -> sub E S T A.

Hint Unfold transitivity_on.

Lemma sub_substitution_aux : forall V e (F:env) v (E:env) x t1 t2 T,
  transitivity_on e ->
  sub E v e V ->
  sub (E & x ~ bind_sub e V & F) t1 t2 T ->
  sub (E & (map (substenv x v) F)) (subst x v t1) (subst x v t2) (subst x v T).
Proof.
  introv TransE Typv Typt.
  gen_eq G: (E & x ~ bind_sub e V & F). gen F.
  apply sub_induct with
   (P := fun (G:env) t1 t2 T (Typt : sub G t1 t2 T) =>
      forall (F:env), G = E & x ~ bind_sub e V & F ->
      sub (E & map (substenv x v) F) ([x ~> v]t1) ([x ~> v]t2) ([x ~> v]T))
   (P0 := fun (G:env) (W:wf G) =>
      forall F, G = E & x ~ bind_sub e V & F ->
      wf (E & (map (substenv x v) F)));
   intros; subst; simpls subst.
  (* case: ax *)
  autos*.
  (* case: var refl *)
  case_var.
    binds_mid~. inversions TEMP. rewrite* subst_fresh. apply_empty* sub_weaken.
    apply* notin_fv_from_wf.
    apply sub_var_refl with (e := [x ~> v] e0). auto.
    rewrite substenv_eq.
    destruct~ (binds_not_middle_inv b) as [K|[Fr K]].
    lets: (@notin_fv_from_binds' E F x e V x5 e0 A w) __. auto.
    rewrite* substenv_fresh.
  (* case: var trans *)
  case_var.
    binds_mid~. apply* ok_from_wf. inversions TEMP.
    lets: H F __. auto.
    apply* TransE.
    rewrite* subst_fresh.
    apply_empty* sub_weaken.
    asserts* W: (wf (E & x ~ bind_sub e V & F)).
    apply* notin_fv_from_wf.
    assert ([x ~> v] e = e).
    apply* subst_fresh.
    apply notin_fv_from_wf_left with (E := E) (F := F) (T := V).
    auto.
    rewrite <- H1. auto.
    lets: H F __. auto.
    apply sub_var_trans with (e1 := ([x ~> v]e1)). auto.
    destruct~ (binds_not_middle_inv b) as [K|[Fr K]].
    rewrite* substenv_eq.
    asserts* w: (wf (E & x ~ bind_sub e V & F)).
    lets: wf_left (wf_left w).
    asserts N: (x # E).
    lets: (wf_left w).
    inversions H2. false (empty_push_inv H4). 
    destruct (eq_push_inv H3) as [? [? ?]]. inversion H7. subst~.
    destruct~ (notin_fv_from_binds H1 K N).
    rewrite* subst_fresh.
    rewrite* subst_fresh.
    auto.
  (* case: top *)
  autos*.  
  (* case: top refl *)
  autos*.  
  (* case: abs *)
  apply_fresh* (@sub_abs) as y; rewrite* substenv_eq.
  cross; auto. apply_ih_map_bind* H1.
  cross; auto. apply_ih_map_bind* H2.
  (* case: app *)
  rewrite* subst_open.
  (* case: prod *)
  apply_fresh* (@sub_prod) as y; rewrite* substenv_eq.
  cross; auto. apply_ih_map_bind* H2.
  cross; auto. apply_ih_map_bind* H3.
  (* case: castup *)
  apply* sub_castup. apply* reduct_red_out.
  (* case: castdn *)
  apply* sub_castdn. apply* reduct_red_out.
  (* case: sub *)
  autos*.
  (* case: wf empty *)
  false. apply* empty_middle_inv.
  (* case: wf cons *)
  change LibEnv.env with LibEnv.env in *.
  induction F using env_ind.
    rewrite concat_empty_r in H1.
     destruct (eq_push_inv H1) as [? [? ?]]. subst.
     rewrite map_empty. rewrite~ concat_empty_r.
    clear IHF. rewrite concat_assoc in H1.
     destruct (eq_push_inv H1) as [? [? ?]]. subst.
     rewrite map_push. rewrite concat_assoc. apply* (@wf_cons). 
  (* case: conclusion *)
  auto.
Qed.

Lemma sub_wf_from_context : forall x T U (E:env),
  binds x (bind_sub T U) E -> 
  wf E -> 
  sub E T T U /\
  sub E U U trm_star.
Proof.
  introv B W. induction E using env_ind. 
  false* binds_empty_inv. 
  destruct (binds_push_inv B) as [[? ?]|[? ?]]. 
    inductions v. inversions H0.
    inversions W. false (empty_push_inv H0).
     destruct (eq_push_inv H) as [? [? ?]]. inversions H4.
     splits. apply_empty* sub_weaken.
     apply_empty* sub_weaken.
    inductions v.
    destruct (wf_push_inv W). forwards~ [k P]: IHE.
     splits. apply_empty* sub_weaken.
     apply_empty* sub_weaken.
Qed.

Lemma sub_prod_prod_inv : forall G e A B B0 C,
   sub G (trm_prod e A B) (trm_prod e A B0) C ->
   (exists L, forall x, x \notin L ->
        sub (G & x ~ bind_sub e A) (B ^ x) (B0 ^ x) (trm_star)).
Proof.
  intros. inductions H; eauto.
Qed.

Lemma sub_narrowing_aux : forall Q F E A B Z P S T,
  transitivity_on Q ->
  sub (E & Z ~ bind_sub Q A & F) S T B ->
  sub E P Q A ->
  sub (E & Z ~ bind_sub P A & F) S T B.
Proof.
  introv TransQ SsubT PsubQ.
  gen_eq G: (E & Z ~ bind_sub Q A & F). gen F.
  apply sub_induct with
    (P := fun G S T B (Sub: sub G S T B) =>
            forall F, G = E & Z ~ bind_sub Q A & F ->
                      sub (E & Z ~ bind_sub P A & F) S T B)
    (P0 := fun G (W: wf G) =>
            forall F, G = E & Z ~ bind_sub Q A & F ->
                      wf (E & Z ~ bind_sub P A & F));
    intros; subst; simpls subst.
  (* case: ax *)
  apply* sub_ax.
  (* case: var refl *)
  rename x5 into x.
  tests EQ: (x = Z).
    asserts~ N: (ok (E & Z ~ bind_sub Q A & F)).
    destruct (ok_middle_inv N).
    lets: (binds_middle_eq_inv b N).
    inversions H2.
    apply* sub_var_refl.
    apply sub_var_refl with (e := e). auto.
    asserts* W1: (x # (Z ~ bind_sub Q A)).
    lets: (binds_remove b W1).
    lets: (H F eq_refl).
    apply* binds_weaken.
  (* case: var trans *)
  rename x5 into x.
  tests EQ: (x = Z).
    asserts~ N: (ok (E & Z ~ bind_sub Q A & F)).
    apply* ok_from_wf.
    destruct (ok_middle_inv N).
    lets: (binds_middle_eq_inv b N).
    inversions H2.
    applys~ (@sub_var_trans).
    apply TransQ.
    lets: H F __. auto.
    do_rew* concat_assoc (apply_empty* sub_weaken).
    autos*.
    apply* sub_var_trans.
    asserts* W1: (x # (Z ~ bind_sub Q A)).
    lets: (binds_remove b W1).
    lets: (H F eq_refl).
    apply* binds_weaken.
    apply* ok_from_wf.
  (* case: top *)
  autos*.
  (* case: top refl *)
  autos*.
  (* case: abs *)
  apply_fresh* sub_abs as Y.
  apply_ih_bind* H1.
  apply_ih_bind* H2.
  (* case: app *)
  autos*.
  (* case: prod *)
  apply_fresh* (@sub_prod) as Y.
  apply_ih_bind* H2. apply_ih_bind* H3.
  (* case: castup *)
  autos*.
  (* case: castdn *)
  autos*.
  (* case: sub *)
  autos*.
  (* case: wf nil *)
  false. apply* empty_middle_inv.
  (* case: wf cons *)
  destruct (env_case F).
    subst. rewrite concat_empty_r.
    rewrite concat_empty_r in H1.
    destruct (eq_push_inv H1) as [? [? ?]].
    inversions H3. apply* wf_cons.
    destruct H2 as [y [v' [E' Eq]]].
    induction v'. subst.
    rewrite concat_assoc.
    rewrite concat_assoc in H1.
    destruct (eq_push_inv H1) as [? [? ?]].
    inversions H3. apply* wf_cons.
  (* conclusion *)
  auto.
Qed.

Lemma sub_trans_aux : forall e2 G e1 e3 A B,
  sub G e1 e2 A -> sub G e2 e3 B -> sub G e1 e3 A.
Proof.
  introv S1. asserts* W: (lc_trm e2).
  gen G A e1 B e3. set_eq e2' eq: e2. gen e2' eq.
  induction W; intros e2' eq G AA e1' S1;
    induction S1; try discriminate; inversions eq;
      intros B' e3' S2; try solve [eauto 3 using sub_var_trans].
  (* case: var refl *)
  inductions S2; eauto 3.
  lets: binds_func H1 H0. inversions H2.
  apply* sub_var_trans.
  (* case: star *)
  inductions S2; eauto 3.
  (* case: top *)
  inductions S2; eauto 3.
  (* case: top refl *)
  inductions S2; eauto 3.
  (* case: app *)
  clear IHS1_1 IHS1_2 IHW2 W1 W2.
  inductions S2. apply~ sub_top.
  apply sub_app with (B := B) (e3 := e4). auto. auto.
  apply sub_app with (B := B) (e3 := e4). apply* IHW1. auto.
  apply* IHS2_1.
  (* case lam *)
  clear IHS1_1 IHS1_2 IHW2 W1 W2.
  inductions S2. apply sub_top.
  pick_fresh y.
  apply (@sub_abs L0). auto. auto. intros.
  lets: (sub_refl_left (H1 x5 H5)). auto.
  intros. lets: (sub_refl_left (H3 x5 H5)). auto.
  apply_fresh sub_abs as y. auto. auto.
  lets: H0 y __. auto.
  lets: H9 (e2 ^ y) __. auto.
  apply* H10. auto.
  apply* IHS2_1.
  (* case pi *)
  clear IHS1_1 IHS1_2 W1 W2.
  clear IHS1_3 H H4 H2.
  inductions S2. apply sub_top.
  pick_fresh y.
  lets: H1 y __. auto. asserts* W: (wf (G & y ~ bind_sub e A0)).
  destruct (wf_to_wt W) as [? ?].
  apply (@sub_prod (L \u L0)). auto. auto. auto. intros.
  apply* H1. intros. apply* H1.
  pick_fresh y.
  lets: H5 y __. auto. asserts* W: (wf (G & y ~ bind_sub e A')).
  destruct (wf_to_wt W) as [? ?].
  apply (@sub_prod (L \u L0 \u L1)). auto.
  lets: IHW2 A __. auto.
  apply H9 with (B := (trm_star)). auto.
  auto. auto. auto.
  intros. apply* H1. intros.
  lets: H0 x5 __. auto.  lets: H10 (B ^ x5) __. auto.
  apply H11 with (B0 := (trm_star)).
  lets: H3 x5 __. auto.
  apply_empty* (@sub_narrowing_typ e A' A).
  apply* H5.
  clear IHS2_2.
  lets: IHS2_1 S1_3 H0 IHW2 IHW1 H3. auto. auto.
  apply* H.
  (* case: castup *)
  clear IHS1_1 IHS1_2 W1 W2 IHW1.
  inductions S2. apply~ sub_top.
  apply sub_castup with (A := A0). auto. auto. auto.
  apply* sub_castup.
  apply* IHS2_1.
  (* case: castdn *)
  clear IHS1_1 IHS1_2 W.
  inductions S2. apply~ sub_top.
  apply sub_castdn with (A := A). auto. auto. auto.
  apply* sub_castdn.
  apply* IHS2_1.
Qed.

Lemma sub_trans : forall e2 G e1 e3 A,
  sub G e1 e2 A -> sub G e2 e3 A -> sub G e1 e3 A.
Proof.
  intros. apply* (@sub_trans_aux e2).
Qed.

Lemma sub_narrowing : forall Q F E A B Z P S T,
  sub (E & Z ~ bind_sub Q A & F) S T B ->
  sub E P Q A ->
  sub (E & Z ~ bind_sub P A & F) S T B.
Proof.
  intros.
  apply* sub_narrowing_aux.
  unfold transitivity_on.
  intros. apply* (@sub_trans Q).
Qed.

Lemma sub_substitution : forall V e (F:env) v (E:env) x t1 t2 T,
  sub E v e V ->
  sub (E & x ~ bind_sub e V & F) t1 t2 T ->
  sub (E & (map (substenv x v) F)) (subst x v t1) (subst x v t2) (subst x v T).
Proof.
  intros.
  apply sub_substitution_aux with (V := V) (e := e).
  unfold transitivity_on.
  intros. apply* (@sub_trans e).
  auto. auto.
Qed.

Lemma sub_refl_right : forall G e1 e2 A,
  sub G e1 e2 A ->
  sub G e2 e2 A
with sub_wf_from_sub : forall G e1 e2 A,
  sub G e1 e2 A ->
  sub G A A trm_star.
Proof.
  clear sub_refl_right.
  introv H. inductions H; try solve [eauto 2].
  apply sub_top_refl. apply (sub_wf_from_sub G e e A H).

  clear sub_wf_from_sub.
  intros. inductions H; try solve [eauto 2].
  destruct* (sub_wf_from_context H0).
  destruct (sub_prod_prod_inv IHsub1) as [L T'].
  pick_fresh x. rewrite~ (@subst_intro x).
  unsimpl ([x ~> A](trm_star)).
  apply_empty* (@sub_substitution B e3).
Qed.

Hint Extern 1 (sub ?G ?A ?A ?B) => match goal with
  | H: sub G _ A B |- _ => apply ((sub_refl_right H))
  end.

Lemma sub_refl : forall G e1 e2 A,
  sub G e1 e2 A ->
  sub G e1 e1 A /\ sub G e2 e2 A.
Proof.
  intros. splits*.
Qed.

Lemma sub_abs_abs_inv : forall G e e0 A A0 B B0 C,
   sub G (trm_abs e A B) (trm_abs e0 A0 B0) C -> exists C',
   A = A0 /\ e = e0 /\
   sub G (trm_prod e A C') C (trm_star) /\
   (exists L, forall x, x \notin L ->
        sub (G & x ~ bind_sub e A) (B ^ x) (B0 ^ x) (C' ^ x)).
Proof.
  intros. inductions H; eauto.
  exists B1. splits; auto.
  apply_fresh* sub_prod as y.
  exists L. intros. apply* H1.
  destruct (IHsub1 _ _ _ _ _ _ eq_refl eq_refl) as [C' [? [? ?]]].
  exists C'. splits*.
  apply* (@sub_trans_aux A1).
Qed.

Lemma sub_sort_any_inv : forall E A B,
  sub E (trm_star) A B ->
  A = trm_star \/ A = trm_top.
Proof.
  intros. inductions H; auto.
Qed.

Lemma sub_top_any_inv : forall E A B,
  sub E trm_top A B ->
  A = trm_top.
Proof.
  intros. inductions H; auto.
Qed.

Lemma sub_prod_prod_inv2 : forall G e e' A A' B B0 C,
   sub G (trm_prod e A B) (trm_prod e' A' B0) C ->
   ((C = trm_star) \/ C = trm_top) /\
   e = e' /\
   sub G e e A' /\
   sub G A' A (trm_star) /\
   (exists L, forall x, x \notin L ->
        sub (G & x ~ bind_sub e A') (B ^ x) (B0 ^ x) (trm_star)).
Proof.
  intros. inductions H; eauto.
  splits*. destructs (IHsub1 _ _ _ _ _ _ eq_refl eq_refl).
  splits*. destruct H1.
  subst. destruct (sub_sort_any_inv H0).
  left*. right*.
  subst. lets: sub_top_any_inv H0. right*.
Qed.

Lemma sub_star_star_inv : forall E A,
  sub E trm_star trm_star A ->
  sub E trm_star A trm_star.
Proof.
  intros. inductions H; auto.
  apply* (@sub_trans A).
Qed.

Lemma sub_star_any_inv : forall E A B,
  sub E trm_star A B ->
  A = trm_star \/ (A = trm_top).
Proof.
  intros. inductions H; auto.
Qed.

Lemma sub_star_star_inv2 : forall E A,
  sub E trm_star trm_star A ->
  A = trm_star \/ (A = trm_top).
Proof.
  intros. inductions H; auto.
  destruct (IHsub1 eq_refl eq_refl); subst.
  destruct (sub_star_any_inv H0); auto.
  right.
  destruct~ (sub_top_any_inv H0).
Qed.

Lemma sub_castup_inv : forall E t1 t2 t1' t2' B,
  sub E (trm_castup t1 t2) (trm_castup t1' t2') B ->
  exists A, t1 = t1' /\ sub E t2 t2' A /\
              reduct t1 A /\
              sub E t1 B trm_star.
Proof.
  intros. inductions H.
  exists A. splits*.
  destruct (IHsub1 _ _ _ _ eq_refl eq_refl) as [A0 [? [? ?]]].
  exists A0. splits*.
  apply* (@sub_trans_aux A).
Qed.

Lemma sub_any_prod_inv : forall E P e1 A B C,
  sub E P (trm_prod e1 A B) C ->
  (exists x, P = trm_var_f x) \/
  (exists e1' A' B', P = trm_prod e1' A' B').
Proof.
  intros. inductions H; autos*.
Qed.

Lemma sub_prod_any_inv : forall E P e1 A B C,
  sub E (trm_prod e1 A B) P C ->
  P = trm_top \/
  (exists e1' A' B', P = trm_prod e1' A' B').
Proof.
  intros. inductions H; autos*.
Qed.

Lemma sub_abs_any_inv : forall E P e1 A B C,
  sub E (trm_abs e1 A B) P C ->
  P = trm_top \/
  (exists e1' A' B', P = trm_abs e1' A' B').
Proof.
  intros. inductions H; autos*.
Qed.

Lemma sub_any_abs_inv : forall E P e1 A B C,
  sub E P (trm_abs e1 A B) C ->
  (exists x, P = trm_var_f x) \/
  (exists e1' A' B', P = trm_abs e1' A' B').
Proof.
  intros. inductions H; autos*.
Qed.

Lemma sub_castup_any_inv : forall E P A B C,
  sub E (trm_castup A B) P C ->
  P = trm_top \/
  (exists A' B', P = trm_castup A' B').
Proof.
  intros. inductions H; autos*.
Qed.

Lemma sub_any_castup_inv : forall E P A B C,
  sub E P (trm_castup A B) C ->
  (exists x, P = trm_var_f x) \/
  (exists A' B', P = trm_castup A' B').
Proof.
  intros. inductions H; autos*.
Qed.

Lemma sub_star_prod_false : forall E e A B C,
  sub E trm_star (trm_prod e A B) C ->
  False.
Proof.
  intros. destruct (sub_any_prod_inv H).
  destruct H0 as [? ?]. inversions H0.
  destruct H0 as [? [? [? ?]]]. inversions H0.
Qed.

Lemma sub_prod_star_false : forall E e A B C,
  sub E (trm_prod e A B) trm_star C ->
  False.
Proof.
  intros. destruct (sub_prod_any_inv H).
  inversions H0.
  destruct H0 as [? [? [? ?]]]. inversions H0.
Qed. 

Definition SubLemma E t1 t2 A :=
  match t1,t2 with
    | trm_castup B t1', trm_castup _ t2' => forall C D, A --> C -> B --> D -> sub E t1' t2' C
    | _,_ => forall t1' t2', t1 --> t1' -> t2 --> t2' -> sub E t1' t2' A
  end.

Lemma preserve_not_cast : forall t1 t2 E A, SubLemma E t1 t2 A -> forall t1' t2', t1 --> t1' -> t2 --> t2' -> sub E t1' t2' A.
  intros.
  unfold SubLemma in H; destruct t1; auto.
  inversion H0.
Defined.

Lemma reduce_sub_var_false : forall E e0 x A e1,
  sub E e0 (trm_var_f x) A ->
  e0 --> e1 -> False.
Proof.
  intros. inductions H; tryfalse.
  inversions H1. inversions H1.
  apply* IHsub1.
Qed.

Lemma sub_any_var_inv : forall E e x A,
  sub E e (trm_var_f x) A ->
  (exists y, e = trm_var_f y).
Proof.
  intros. inductions H.
  exists* x.
  exists* x5.
  apply* IHsub1.
Qed.

Lemma sub_any_app_inv : forall E P e1 A C,
  sub E P (trm_app e1 A) C ->
  (exists x, P = trm_var_f x) \/
  (exists e1' A', P = trm_app e1' A').
Proof.
  intros. inductions H; autos*.
Qed.

Lemma sub_app_inv : forall E e1 e2 A A' T,
  sub E (trm_app e1 A) (trm_app e2 A') T ->
  exists e3 B C, A = A' /\ sub E A e3 B /\
                 sub E e1 e2 (trm_prod e3 B C).
Proof.
  intros. inductions H; autos*.
  exists e3 B C. splits*.
Qed.

Lemma sub_app_any_inv : forall E P e1 A C,
  sub E (trm_app e1 A) P C ->
  P = trm_top \/
  (exists e1' A', P = trm_app e1' A').
Proof.
  intros. inductions H; autos*.
Qed.

Lemma sub_castdn_any_inv : forall E P A C,
  sub E (trm_castdn A) P C ->
  P = trm_top \/
  (exists A', P = trm_castdn A').
Proof.
  intros. inductions H; autos*.
Qed.

Lemma sub_any_castdn_inv : forall E P A C,
  sub E P (trm_castdn A) C ->
  (exists x, P = trm_var_f x) \/
  (exists A', P = trm_castdn A').
Proof.
  intros. inductions H; autos*.
Qed.

Lemma sub_castdn_inv : forall E t2 t2' B,
  sub E (trm_castdn t2) (trm_castdn t2') B ->
  exists A t1, sub E t2 t2' A /\
               reduct A t1 /\
               sub E t1 B trm_star.
Proof.
  intros. inductions H.
  exists A B. splits*.
  destruct (IHsub1 _ _ eq_refl eq_refl) as [A0 [t1 [? ?]]].
  exists A0 t1. splits*.
  apply* (@sub_trans_aux A).
Qed.

Lemma sub_reduct_middle : forall E A B C e1 e3 T,
  sub E A B T ->
  B --> C ->
  sub E e1 A T ->
  e1 --> e3 ->
  exists D, A --> D.
Proof.
  intros. gen e3 B C.
  inductions H1; introv R1 S R2; try solve [inversion R1 | inversion R2].
  (* case: app *)
  lets: (sub_top_any_inv S). subst. inversions R2.
  inversions R1.
  destruct (sub_app_any_inv S) as [? | [K1 [K2 ?]]]; subst.
  inversions R2.
  destruct (sub_abs_any_inv H1_) as [? | [J1 [J2 [J3 ?]]]]; subst.
  destruct (sub_app_inv S) as [e3' [B' [C' (?&?&?)]]].
  lets: (sub_top_any_inv H4). subst.
  asserts* W: (ivalue (trm_app trm_top K2)).
  false (ivalue_cannot_red W R2).
  exists (J3 ^^ A).  asserts~ Q: (lc_trm (trm_abs J1 J2 J3)).
  apply* reduct_beta.
  destruct (sub_app_any_inv S) as [? | [K1 [K2 ?]]]; subst.
  inversions R2.
  destruct (sub_app_inv S) as [e3' [B' [C' (?&?&?)]]].
  inversions R2.
  destruct (sub_any_abs_inv H2) as [[x ?] | [J1 [J2 [J3 ?]]]]; subst.
  destruct (sub_any_var_inv H1_); subst. inversions H3.
  exists (J3 ^^ K2). asserts~ Q: (lc_trm (trm_abs J1 J2 J3)).
  apply* reduct_beta. 
  lets P: sub_typekeep (sub_refl_right H1_) H2.
  lets P1: IHsub1 H3 P H8.
  destruct P1 as [e2' ?].
  exists* (trm_app e2' K2).
  (* case: castdn *)
  destruct (sub_castdn_any_inv S) as [? | [K ?]]; subst.
  inversions R2. 
  destruct (sub_castdn_inv S) as [J1 [J2 (?&?&?)]].
  inversions R1; inversions R2.
  lets P1: IHsub2 H4.
  lets P2: sub_typekeep (sub_refl_right H1_0) H0.
  lets P3: P1 P2 H5.
  destruct P3 as [e2' ?]. exists* (trm_castdn e2').
  destruct (sub_any_castup_inv H0) as [[x ?] | [M1 [M2 ?]]]; subst.
  destruct (sub_any_var_inv H1_0) as [y ?]; subst. inversions H4.
  asserts* W: (lc_trm (trm_castup M1 M2)). inversion W.
  exists* M2.
  destruct (sub_castup_any_inv H1_0) as [? | [M1 [M2 ?]]]; subst.
  lets: (sub_top_any_inv H0). subst. inversions H6.
  asserts* W: (lc_trm (trm_castup M1 M2)). inversion W.
  exists* M2.
  destruct (sub_castup_any_inv H1_0) as [? | [M1 [M2 ?]]]; subst.
  lets: (sub_top_any_inv H0). inversions H3.
  asserts* W: (lc_trm (trm_castup M1 M2)). inversion W.
  exists* M2.
  (* case: sub *)
  lets P1: IHsub1 R1.
  lets P2: P1 (sub_typekeep (sub_refl_right H1_) S).
  apply* P2.
Qed.

Lemma is_castup_dec : forall e,
  (exists A B, e = trm_castup A B) \/
  ~(exists A B, e = trm_castup A B).
Proof.
  intros. unfold not. 
  induction e;
    try solve [right; intro N;
               destruct N as [J1 [J2 Eq]]; inversions Eq].
  left*.
Qed.

Lemma is_castup_dec' : forall e1 e2,
  (exists t e, e1 = trm_castup t e) /\ (exists t e, e2 = trm_castup t e) \/
 not ((exists t e, e1 = trm_castup t e) /\ (exists t e, e2 = trm_castup t e)).
Proof.
  intros. unfolds not.
  destruct (is_castup_dec e1);
    destruct (is_castup_dec e2);
    try solve [right* | left*].
Qed.

Lemma not_eq_castup_inv : forall e1 e2,
  ((exists t e, e1 = trm_castup t e) /\
   (exists t e, e2 = trm_castup t e) -> False) ->
  (((exists t e, e1 = trm_castup t e) -> False) /\
   ((exists t e, e2 = trm_castup t e) -> False)) \/
  ((exists t e, e1 = trm_castup t e) /\
   ((exists t e, e2 = trm_castup t e) -> False)) \/
  (((exists t e, e1 = trm_castup t e) -> False) /\
   (exists t e, e2 = trm_castup t e)).
Proof.
  intros.
  intros. unfolds not.
  destruct (is_castup_dec e1);
    destruct (is_castup_dec e2).
  false*.
  right. left*.
  right. right*.
  left*.
Qed.

Lemma sub_reduct_preserve1 : forall E t1 t2 A,
  sub E t1 t2 A -> SubLemma E t1 t2 A.
Proof.
  introv Typ.
  induction Typ; try solve [unfold SubLemma; introv Red1 Red; inversions Red1].
  unfold SubLemma; destruct e; intros; inversion H0.
  unfold SubLemma; introv Red1 Red2.
  (* Case App *)
  inversions Red1; inversions Red2.
  destruct (sub_abs_abs_inv Typ1) as [C' (? & ? & ? & [L ?])]. subst.
  destruct (sub_prod_prod_inv2 H8) as (? & ? & ? & ? & (L' & ?)). subst.
  pick_fresh x.
   rewrite* (@subst_intro x e4).
   rewrite* (@subst_intro x e5).
   rewrite* (@subst_intro x C).
  apply_empty* (@sub_substitution B e3).
  lets: H13 x __. auto.
  apply* (@sub_sub' (C' ^ x)).
  apply_empty* (@sub_narrowing_typ e3 B A1).

  destruct (sub_abs_any_inv Typ1).
    subst. inversions H7.
    destruct H as [? [? [? ?]]]. subst. inversions H7.
  
  destruct (sub_any_abs_inv Typ1).
    destruct H as [? ?]. subst. inversions H3.
    destruct H as [? [? [? ?]]]. subst. inversions H3.
  
    apply sub_app with (e3 := e3) (B := B). auto.
    assert (forall t1' t2', e1 --> t1' -> e2 --> t2' -> sub G t1' t2' (trm_prod e3 B C)).
    apply preserve_not_cast. auto.
  apply* H.
  auto.
  unfold SubLemma; introv Red1 Red2.
  assert (A = C). apply reduct_determ with (t := B); auto. subst. auto.
  (* Case castdn *)
  unfold SubLemma; introv Red1 Red2.
  inversions Red1; inversions Red2.
  apply sub_castdn with (A := A). auto.
  apply* preserve_not_cast. auto.
  destruct (sub_any_castup_inv Typ2).
    destruct H0. subst. inversions H1.
    destruct H0 as [? [? ?]]. subst. inversions H1.
  destruct (sub_castup_any_inv Typ2).
    subst. inversions H3.
    destruct H0 as [? [? ?]]. subst. inversions H3.
  destruct (sub_castup_inv Typ2). destruct H0. destruct H5. destruct H6. subst.
    unfold SubLemma in IHTyp2.
    apply IHTyp2 with (D := x); auto.
  (* Last case *)
  assert ((exists t e, e1 = trm_castup t e) /\ (exists t e, e2 = trm_castup t e) \/ not ((exists t e, e1 = trm_castup t e) /\ (exists t e, e2 = trm_castup t e))).
  apply is_castup_dec'.
  destruct H. destruct H. destruct H. destruct H. destruct H0. destruct H0. subst.
  unfold SubLemma. intros.
  unfold SubLemma in IHTyp1.
  destruct (sub_castup_inv Typ1). destruct H1. destruct H2. destruct H3. subst.
  assert (forall t1' t2', A --> t1' -> B --> t2' -> sub G t1' t2' trm_star). (* B is reducible, so IHTyp2 should have this form *)
  apply* preserve_not_cast.
  assert (D = x3). apply reduct_determ with (t := x1); auto. subst.
  (*apply IHTyp1 with (D := x3). *)
  assert (exists D, A --> D).
  lets: sub_reduct_middle Typ2 H H4 H0. auto.
  destruct H5 as [D ?].
  pose (IHTyp1 _ _  H5 H3). pose (H1 _ _ H5 H).
  apply sub_sub with (A := D). auto. auto.
  destruct (not_eq_castup_inv H) as [(?&?)|[(?&?)|(?&?)]].
  lets: preserve_not_cast IHTyp1.  
  induction e1; induction e2; simpl; intros; try solve [apply* (@sub_sub' A)].
  false*.
  lets: preserve_not_cast IHTyp1.  
  induction e1; induction e2; simpl; intros; try solve [apply* (@sub_sub' A)].
  false*.
  lets: preserve_not_cast IHTyp1.  
  induction e1; induction e2; simpl; intros; try solve [apply* (@sub_sub' A)].
  false*.
Qed.

Lemma sub_reduct_preserve : forall E t1 t2 t1' t2' A,
  sub E t1 t2 A -> 
  t1 --> t1' ->
  t2 --> t2' ->
  sub E t1' t2' A.
  intros.
  apply (@preserve_not_cast t1 t2). apply sub_reduct_preserve1. auto. auto. auto.
Defined.

Lemma subject_reduction_wh : forall E t t' T,
  sub E t t T -> t --> t' -> sub E t' t' T.
Proof.
  introv S R.
  lets: sub_reduct_preserve S R R.
  auto.
Qed.

Lemma progress_wh : forall E t T,
  sub E t t T ->
  value t \/ exists t', t --> t'.
Proof.
  intros. inductions H; auto.
  (* case: abs *)
  left. apply value_abs. auto. auto.
  apply* lc_trm_abs.
  intros. lets: H1 x5 H5. auto.
  (* case: app *)
  destruct~ (IHsub1 eq_refl). inductions H1.
    lets: (sub_star_star_inv H). false* sub_star_prod_false.
    left. apply* value_ivalue.
    right. exists* (e2 ^^ A).
    destruct (sub_prod_prod_inv2 H) as (? & ? & ? & ? & (L' & ?)).
    destruct H4; false.
    false. destruct (sub_castup_inv H) as [A' (? & ? & ? & ?)].
      destruct (sub_any_prod_inv H6). destruct H7; subst. inversions H5.
      destruct H7 as [? [? [? ?]]]; subst. inversions H5.
    destruct H1 as [e1' ?].  right. exists* (trm_app e1' A).
  (* case: prod *)
  left. apply value_prod. auto. auto. apply* lc_trm_prod.
  intros. lets: H4 x5 H6. auto.
  (* case: castdn *)
  destruct~ (IHsub2 eq_refl). inductions H2.
    destruct (sub_star_star_inv2 H0); subst. inversions H1. 
    inversions H1.
    left*.
    destruct (sub_abs_abs_inv H0) as [C' [? [? [? [L ?]]]]].
    destruct (sub_prod_any_inv H7); subst. 
    inversions H1. destruct H9 as [? [? [? ?]]]; subst; inversions H1.
    destruct (sub_prod_prod_inv2 H0) as (? & ? & ? & ? & (L' & ?)).
    destruct H5; subst. inversions H1. inversions H1.
    right. exists* e.
    right. destruct H2 as [t' ?]. exists* (trm_castdn t').
Qed.

Lemma progress_empty_wh : forall t T,
  sub empty t t T ->
  value t \/ exists t', t --> t'.
Proof.
  intros. apply* progress_wh.
Qed.

