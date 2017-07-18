Set Implicit Arguments.
Require Import LibLN Main_ott Main_Infra Main_Proofs.
Implicit Types x : var.
Implicit Types G : env.

Inductive _typing : env -> trm -> trm -> Prop :=
  | _typing_star : forall G,
      _wf G -> _typing G trm_star trm_star
  | _typing_var : forall e G x A,
      _wf G -> binds x (bind_sub e A) G -> _typing G (trm_var_f x) A
  | _typing_top : forall G A,
      _typing G A trm_star -> _typing G trm_top A
  | _typing_lam : forall L G e1 e2 A B,
      _typing G e1 A ->
      _typing G A trm_star ->
      (forall x, x \notin L ->
                 _typing (G & x ~ bind_sub e1 A) (B ^ x) trm_star) ->
      (forall x, x \notin L ->
                 _typing (G & x ~ bind_sub e1 A) (e2 ^ x) (B ^ x)) ->
      _typing G (trm_abs e1 A e2) (trm_prod e1 A B)
  | _typing_app : forall e3 G e A B C,
      _typing G A B ->
      _sub G A e3 ->
      _typing G e (trm_prod e3 B C) ->
      _typing G (trm_app e A) (C ^^ A)
  | _typing_pi : forall L G e A B,
      _typing G e A ->
      _typing G A trm_star ->
      (forall x, x \notin L ->
        _typing (G & x ~ bind_sub e A) (B ^ x) trm_star) ->
      _typing G (trm_prod e A B) trm_star
  | _typing_castup : forall G e A B,
      _typing G B trm_star ->
      _typing G e A ->
      reduct B A ->
      _typing G (trm_castup B e) B
  | _typing_castdn : forall G e A B,
      _typing G B trm_star ->
      _typing G e A ->
      reduct A B ->
      _typing G (trm_castdn e) B
  | _typing_sub : forall A G e B,
      _typing G e A ->
      _sub G A B ->
      _typing G B trm_star ->
      _typing G e B

with _wf : env -> Prop :=
  | _wf_nil : _wf empty
  | _wf_cons : forall G x e A,
      x # G ->
      _typing G e A ->
      _typing G A trm_star ->
      _wf (G & x ~ bind_sub e A)

with _sub : env -> trm -> trm -> Prop :=
  | _sub_star : forall G, _wf G -> _sub G trm_star trm_star
  | _sub_var_refl : forall G x e A,
      _wf G -> binds x (bind_sub e A) G -> _sub G (trm_var_f x) (trm_var_f x)
  | _sub_var_trans : forall e1 A G x e2,
      binds x (bind_sub e1 A) G -> _sub G e1 e2 -> 
      _sub G (trm_var_f x) e2
  | _sub_top : forall G e,
      _wf G -> lc_trm e -> _sub G e trm_top
  | _sub_top_refl : forall G,
      _wf G -> _sub G trm_top trm_top
  | _sub_lam : forall L G e1 e2 e3 A,
      _typing G e3 A ->
      _typing G A trm_star ->
      (forall x, x \notin L -> _sub (G & x ~ bind_sub e3 A) (e1 ^ x) (e2 ^ x)) ->
      _sub G (trm_abs e3 A e1) (trm_abs e3 A e2)
  | _sub_app : forall G e1 e2 A,
      lc_trm A ->
      _sub G e1 e2 -> _sub G (trm_app e1 A) (trm_app e2 A)
  | _sub_pi : forall L G e A B C D,
      _typing G e C ->
      _typing G C trm_star ->
      _sub G C A ->
      (forall x, x \notin L -> _sub (G & x ~ bind_sub e C) (B ^ x) (D ^ x)) ->
      _sub G (trm_prod e A B) (trm_prod e C D)
  | _sub_castup : forall G A e1 e2,
      lc_trm A -> _sub G e1 e2 -> _sub G (trm_castup A e1) (trm_castup A e2)
  | _sub_castdn : forall G e1 e2,
      _sub G e1 e2 -> _sub G (trm_castdn e1) (trm_castdn e2).

Hint Constructors _typing _sub _wf.

Scheme typing_induct := Induction for _typing Sort Prop
  with twf_induct := Induction for _wf Sort Prop
  with tsub_induct := Induction for _sub Sort Prop.

Lemma regular_typing : forall E t T, _typing E t T ->
  (_wf E /\ ok E /\ contains_terms E /\ lc_trm t /\ lc_trm T). 
Proof.
  apply typing_induct with
  (P0 := fun E (_ : _wf E) => ok E /\ contains_terms E)
  (P1 := fun E t1 t2 (_: _sub E t1 t2) => _wf E /\ ok E /\ contains_terms E /\ lc_trm t2); 
    unfolds contains_terms; intros; splits*.
  destructs H. lets: H0 b. jauto.
  intros. false* (binds_empty_inv).
  intros. destruct (binds_push_inv H1) as [[? P]|[? ?]]; try (inversions P); subst*.
  destructs H. apply* H5.
Qed.

Lemma regular_tsub : forall E t T, _sub E t T ->
  (_wf E /\ ok E /\ contains_terms E /\ lc_trm t /\ lc_trm T). 
Proof.
  apply tsub_induct with
  (P0 := fun E (_ : _wf E) => ok E /\ contains_terms E)
  (P := fun E t1 t2 (_: _typing E t1 t2) => _wf E /\ ok E /\ contains_terms E /\ lc_trm t1 /\lc_trm t2); 
   unfolds contains_terms; intros; splits*.
  destructs H. lets: H0 b. jauto.
  intros. false* (binds_empty_inv).
  intros. destruct (binds_push_inv H1) as [[? P]|[? ?]]; try (inversions P); subst*.
  destructs H. apply* H5.
Qed.

Hint Extern 1 (lc_trm ?t) => match goal with
  | H: _typing _ t _ |- _ => apply (proj32 (proj33 (regular_typing H)))
  | H: _typing _ _ t |- _ => apply (proj33 (proj33 (regular_typing H)))
  | H: _sub _ t _ |- _ => apply (proj32 (proj33 (regular_tsub H)))
  | H: _sub _ _ t |- _ => apply (proj33 (proj33 (regular_tsub H)))
  end.

Lemma ok_from_twf : forall E, _wf E -> ok E.
Proof.
  induction 1. auto. autos* (regular_typing H0).
Qed.

Hint Extern 1 (ok ?E) => match goal with
  | H: _wf E |- _ => apply (ok_from_twf H)
  end.

Hint Extern 1 (_wf ?E) => match goal with
  | H: _typing E _ _ |- _ => apply (proj1 (regular_typing H))
  | H: _sub E _ _ |- _ => apply (proj1 (regular_tsub H))
  end.

Lemma twf_push_inv : forall E x T U,
  _wf (E & x ~ bind_sub T U) -> _wf E /\ lc_trm T /\ lc_trm U.
Proof.
  introv W. inversions W. 
  false (empty_push_inv H0).
  destruct (eq_push_inv H) as [? [? ?]]. inversions H4. subst~.
Qed.

Lemma term_from_binds_in_twf : forall x E T U,
  _wf E -> binds x (bind_sub T U) E -> lc_trm T /\ lc_trm U.
Proof.
  introv W Has. gen E. induction E using env_ind; intros.
  false* binds_empty_inv.
  induction v.
  destruct (twf_push_inv W).
  destruct (binds_push_inv Has) as [[? ?] | [? ?]].
  inversion H2. subst*.
  apply* IHE.
Qed.

Lemma term_from_binds_in_twf_left : forall x E T U,
  _wf E -> binds x (bind_sub T U) E -> lc_trm T.
Proof.
  intros. destruct~ (term_from_binds_in_twf H H0).
Qed.

Lemma term_from_binds_in_twf_right : forall x E T U,
  _wf E -> binds x (bind_sub T U) E -> lc_trm U.
Proof.
  intros. destruct~ (term_from_binds_in_twf H H0).
Qed.

Hint Extern 1 (lc_trm ?t) => match goal with
  | H: binds ?x (bind_sub t ?t2) ?E |- _ => apply (@term_from_binds_in_twf_left x E)
  | H: binds ?x (bind_sub ?t2 t) ?E |- _ => apply (@term_from_binds_in_twf_right x E)
  end.

Lemma twf_left : forall E F : env,
  _wf (E & F) -> _wf E.
Proof.
  intros. induction F using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in H.
   inversions H. false (empty_push_inv H1).
   destruct (eq_push_inv H0) as [? [? ?]]. subst~. 
Qed.

Implicit Arguments twf_left [E F].

Lemma typing_fresh : forall E T U x,
  _typing E T U -> x # E -> x \notin fv T.
Proof.
  introv Typ.
  induction Typ; simpls; intros; try solve [eauto 4].
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H0 H1.
  pick_fresh y. notin_simpl; auto. apply* (@fv_open_var y).
  pick_fresh y. notin_simpl; auto. apply* (@fv_open_var y).
Qed.

Lemma notin_fv_from_twf : forall E F x U V,
  _wf (E & x ~ bind_sub U V & F) -> x \notin fv U /\ x \notin fv V.
Proof.
  intros.
  lets W: (twf_left H). inversions W.
  false (empty_push_inv H1). 
  destruct (eq_push_inv H0) as [? [P ?]]. inversions P.
  split; apply* typing_fresh.
Qed.

Hint Extern 1 (?x \notin fv ?U) => 
  match goal with H: _wf (?E & x ~ (bind_sub U ?V) & ?F) |- _ =>
    apply (proj1 (notin_fv_from_twf H)) end.

Hint Extern 1 (?x \notin fv ?V) => 
  match goal with H: _wf (?E & x ~ (bind_sub ?U V) & ?F) |- _ =>
    apply (proj2 (notin_fv_from_twf H)) end.

Lemma notin_fv_from_tbinds : forall x y T U E,
  _wf E -> binds y (bind_sub T U) E -> x # E -> x \notin fv T /\ x \notin fv U.
Proof.
  induction E using env_ind; intros.
  false* binds_empty_inv.
  induction v.
  destruct (twf_push_inv H).
    destruct (binds_push_inv H0) as [[? ?] | [? ?]].
    inversion H5. subst. inversions H. false* (empty_push_inv H6).
     destruct (eq_push_inv H4) as [? [? ?]].  inversion H9. subst~. 
     split; apply* typing_fresh.
    autos*.
Qed.

Lemma notin_fv_from_tbinds_left : forall x y T U E,
  _wf E -> binds y (bind_sub T U) E -> x # E -> x \notin fv T.
Proof.
  introv A B C. destructs~ (notin_fv_from_tbinds A B C).
Qed.
  
Lemma notin_fv_from_tbinds_right : forall x y T U E,
  _wf E -> binds y (bind_sub T U) E -> x # E -> x \notin fv U.
Proof.
  introv A B C. destructs~ (notin_fv_from_tbinds A B C).
Qed.

Lemma notin_fv_from_tbinds' : forall E F x V y U1 U2,
  _wf (E & x ~ V & F) -> 
  binds y (bind_sub U1 U2) E ->
  x \notin fv U1 /\ x \notin fv U2.
Proof.
  intros. lets W: (twf_left H). inversions keep W.
  false (empty_push_inv H2). 
  induction V.
  destruct (eq_push_inv H1) as [? [P ?]]. inversion P. subst~. 
  lets W': (twf_left W). apply* notin_fv_from_tbinds.
Qed.

Hint Extern 1 (?x \notin fv ?U1) => 
  match goal with H: _wf (?E & x ~ ?V & ?F), B: binds ?y (bind_sub U1 ?U2) ?E |- _ =>
    apply (proj1 (notin_fv_from_tbinds' H B)) end.

Hint Extern 1 (?x \notin fv ?U2) => 
  match goal with H: _wf (?E & x ~ ?V & ?F), B: binds ?y (bind_sub ?U1 U2) ?E |- _ =>
    apply (proj2 (notin_fv_from_tbinds' H B)) end.

Lemma tsub_fresh : forall E A B x,
  _sub E A B -> x # E -> x \notin fv A -> x \notin fv B.
Proof.
  introv S. induction S; simpls; intros; try solve [eauto 3].
  apply* IHS. rewrite notin_singleton in *. apply* notin_fv_from_tbinds_left.
  notin_simpl; auto; try solve [apply* typing_fresh].
    pick_fresh y. apply~ (@fv_open_var y). apply* H2.
    apply* fv_close_var.
  notin_simpl; auto; try solve [apply* typing_fresh].
    pick_fresh y. apply~ (@fv_open_var y). apply* H2.
    apply* fv_close_var.
Qed.

Lemma typing_fresh_all : forall E T U x,
  _typing E T U -> x # E -> x \notin fv T /\ x \notin fv U.
Proof.
  introv Typ.
  induction Typ; simpls; intros; try solve [splits*].
  splits. rewrite notin_singleton. intro. subst. applys binds_fresh_inv H0 H1.
    apply* notin_fv_from_tbinds_right.
  destructs~ IHTyp1. destructs~ IHTyp2.
    pick_fresh y. split; notin_simpl; auto. 
    apply* (@fv_open_var y). apply* H2.
    apply* (@fv_open_var y). apply* H2.
  destructs~ IHTyp1. destructs~ IHTyp2.
    split; notin_simpl; auto. apply* fv_open_term.
  destructs~ IHTyp1. destructs~ IHTyp2.
    pick_fresh y. split; notin_simpl; auto.
    apply* (@fv_open_var y). apply* H0.
  (* splits*. apply* tsub_fresh. *)
Qed.

Lemma typing_fresh_typ : forall E T U x,
  _typing E T U -> x # E -> x \notin fv U.
Proof.
  introv P Q. destructs~ (typing_fresh_all P Q).
Qed.

Lemma tsub_weaken : forall G E F t T,
  _sub (E & G) t T ->
  _wf (E & F & G) ->
  _sub (E & F & G) t T
with typing_weaken : forall G E F t T,
  _typing (E & G) t T ->
  _wf (E & F & G) -> 
  _typing (E & F & G) t T.
Proof.
  clear tsub_weaken.
  introv Typ. gen_eq Env: (E & G). gen G.
  induction Typ; introv EQ W; subst; eauto.
  (* case: var *)
  apply* _sub_var_refl. apply* binds_weaken.
  (* case: trans *)
  apply* (@_sub_var_trans e1 A). apply* binds_weaken.
  (* case: trm_abs *)
  apply_fresh* (@_sub_lam) as y.
  apply_ih_bind* H2.
  (* case: trm_prod *)
  apply_fresh* (@_sub_pi) as y. apply_ih_bind* H2.

  clear typing_weaken.
  introv Typ. gen_eq Env: (E & G). gen G.
  induction Typ; introv EQ W; subst; eauto.
  (* case: var *)
  apply* _typing_var. apply* binds_weaken.
  (* case: trm_abs *)
  apply_fresh* (@_typing_lam) as y.
  forwards TypP: (IHTyp1 G0); auto.
  apply_ih_bind* H0. apply_ih_bind* H2.
  (* case: trm_prod *)
  apply_fresh* (@_typing_pi) as y. apply_ih_bind* H0.
Qed.

Lemma tsub_refl : forall G t T,
  _typing G t T -> _sub G t t.
Proof.
  intros. inductions H; eauto.
Qed.

Lemma typing_wf_from_context : forall x T U (E:env),
  binds x (bind_sub T U) E -> 
  _wf E -> 
  _typing E T U /\
  _typing E U trm_star.
Proof.
  introv B W. induction E using env_ind. 
  false* binds_empty_inv. 
  destruct (binds_push_inv B) as [[? ?]|[? ?]]. 
    subst. inversions W. false (empty_push_inv H0).
     destruct (eq_push_inv H) as [? [P ?]]. inversions P. subst.
     split; apply_empty* typing_weaken.
    induction v.
    destruct (twf_push_inv W).
     split; apply_empty* typing_weaken.
Qed.

Lemma typing_wf_from_twf : forall G x e A,
  _wf (G & x ~ bind_sub e A) -> _typing G e A /\ _typing G A (trm_star).
Proof.
  intros. inversions H.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H0) as [? [? ?]]. inversion H4. subst*.
Qed.

Lemma typing_narrowing_typ : forall Q B A F x E C e,
  _typing (E & x ~ bind_sub Q B & F) e C ->
  _sub E A B ->
  _wf (E & x ~ bind_sub Q A & F) ->
  _typing (E & x ~ bind_sub Q A & F) e C
with tsub_narrowing_typ : forall Q B A F x E e1 e2,
  _sub (E & x ~ bind_sub Q B & F) e1 e2 ->
  _sub E A B ->
  _wf (E & x ~ bind_sub Q A & F) ->
  _sub (E & x ~ bind_sub Q A & F) e1 e2.
Proof.
  clear typing_narrowing_typ.
  intros. gen_eq G: (E & x ~ bind_sub Q B & F). gen E F.
  induction H; intros; subst; eauto.
  (* case var *)
  asserts W: (_wf (E & x ~ bind_sub Q A)). apply* twf_left.
  destruct (binds_concat_inv H0).
  apply* _typing_var.
  destruct H3.
  destruct (binds_push_inv H4). destructs H5.
  inversions H6. apply* (@_typing_sub A).
  apply_empty* tsub_weaken. apply_empty* tsub_weaken.
  destructs (typing_wf_from_twf (twf_left H)).
  apply_empty* typing_weaken.
  apply_empty* typing_weaken.
  apply_empty* typing_weaken.
  (* case lam *)
  apply_fresh* (@_typing_lam) as y. 
  apply_ih_bind* H2. apply_ih_bind* H4.
  (* case pi *)
  apply_fresh* (@_typing_pi) as y.
  apply_ih_bind* H2.
  
  clear tsub_narrowing_typ.
  intros. gen_eq G: (E & x ~ bind_sub Q B & F). gen E F.
  induction H; intros; subst; eauto.
  (* case var *)
  asserts W1: (_wf (E & x ~ bind_sub Q A)). apply* twf_left.
  destruct (binds_concat_inv H0).
  apply* _sub_var_refl.
  destruct H3.
  destruct (binds_push_inv H4). destructs H5.
  inversions H6. apply_empty* tsub_weaken.
  apply_empty* tsub_weaken.
  (* case trans *)
  asserts W1: (_wf (E & x ~ bind_sub Q A)). apply* twf_left.
  destruct (binds_concat_inv H).
  apply* _sub_var_trans.
  destruct H3. destruct (binds_push_inv H4). destructs H5. inversions H6.
  apply* _sub_var_trans.
  apply* _sub_var_trans.
  (* case lam *)
  apply_fresh* (@_sub_lam) as y. 
  apply_ih_bind* H2.
  (* case pi *)
  apply_fresh* (@_sub_pi) as y.
  apply_ih_bind* H3.
Qed.

Lemma tsub_trans : forall B G A C,
  _sub G A B -> _sub G B C -> _sub G A C.
Proof.
  introv S1. asserts* W: (lc_trm B).
  gen G A C. set_eq B' eq: B. gen B' eq.
  induction W; intros B' eq G AA S1;
    induction S1; try discriminate; inversions eq;
      intros C' S2; inversions keep S2; 
        try solve [eauto 3].
  apply~ _sub_top.
  apply_fresh _sub_lam as y.
    auto. auto. lets P1: H0 y __. auto.
    lets P2: (P1 _ eq_refl).
    lets Q1: H3 y __. auto. lets Q2: H12 y __. auto.
    lets: P2 Q1 Q2. auto.
  apply~ _sub_top.
  apply_fresh _sub_pi as y.
    auto. auto. apply* IHW2.
    lets P1: H0 y __. auto. lets P2: (P1 _ eq_refl).
    lets Q1: H3 y __. auto. lets Q2: H13 y __. auto.
    apply~ P2. apply_empty* (@tsub_narrowing_typ e A C).
Qed.

Hint Resolve tsub_trans.

Lemma typing_prod_inv : forall E e U T P,
  _typing E (trm_prod e U T) P ->
     _sub E trm_star P
  /\ _typing E e U
  /\ _typing E U trm_star
  /\ exists L, forall x, x \notin L -> _typing (E & x ~ bind_sub e U) (T ^ x) trm_star.
Proof.
  introv Typ. gen_eq P1: (trm_prod e U T).
  induction Typ; intros; subst; tryfalse.
  inversions EQP1. splits*. 
  destructs~ (IHTyp1 eq_refl).
  splits*.
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

Lemma typing_substitution : forall V e (F:env) v (E:env) x t T,
  _typing E v V ->
  _sub E v e ->
  _typing (E & x ~ bind_sub e V & F) t T ->
  _typing (E & (map (substenv x v) F)) (subst x v t) (subst x v T).
Proof.
  introv Typv Sub Typt.
  gen_eq G: (E & x ~ bind_sub e V & F). gen F. 
  apply typing_induct with
   (P := fun (G:env) t T (Typt : _typing G t T) => 
      forall (F:env), G = E & x ~ bind_sub e V & F -> 
      _typing (E & map (substenv x v) F) ([x ~> v]t) ([x ~> v]T))
   (P0 := fun (G:env) (W: _wf G) => 
      forall F, G = E & x ~ bind_sub e V & F -> 
      _wf (E & (map (substenv x v) F)))
   (P1 := fun (G:env) t T (Subt : _sub G t T) => 
      forall (F:env), G = E & x ~ bind_sub e V & F -> 
      _sub (E & map (substenv x v) F) ([x ~> v]t) ([x ~> v]T)); 
   intros; subst; simpls subst; try solve [eauto 4].
  (* case: trm_star *)
  autos*.
  (* case: var *)
  case_var.
    binds_mid~. inversions TEMP. rewrite* subst_fresh. apply_empty* typing_weaken.
    apply~ (@_typing_var ([x~>v]e0)). rewrite substenv_eq.
    destruct~ (binds_not_middle_inv b) as [K|[Fr K]]. rewrite* substenv_fresh.
  (* case: trm_abs *)
  apply_fresh* (@_typing_lam) as y; rewrite* substenv_eq.
   cross; auto. apply_ih_map_bind* H1.
   cross; auto. apply_ih_map_bind* H2.
  (* case: trm_app *)
  rewrite* subst_open.
  (* case: trm_prod *)
  apply_fresh* (@_typing_pi) as y; rewrite* substenv_eq.
   cross; auto. apply_ih_map_bind* H1. 
  (* case: castup *)
  apply* _typing_castup. apply* reduct_red_out.
  (* case: castdn *)
  apply* _typing_castdn. apply* reduct_red_out.
  (* case: sub *)
  apply* (@_typing_sub ([x ~> v] A)).
  (* case: wf nil *)
  false (empty_middle_inv H).
  (* case: wf cons *)
  change LibEnv.env with LibEnv.env in *.
  induction F using env_ind.
    rewrite concat_empty_r in H1.
     destruct (eq_push_inv H1) as [? [? ?]]. subst.
     rewrite map_empty. rewrite~ concat_empty_r.
    clear IHF. rewrite concat_assoc in H1.
     destruct (eq_push_inv H1) as [? [? ?]]. subst.
     rewrite map_push. rewrite concat_assoc. apply* (@_wf_cons). 
  (* case sub_var *)
  case_var.
    binds_mid~. apply_empty* tsub_weaken. apply* tsub_refl.
    apply _sub_var_refl with (A := [x ~> v] A) (e := [x ~> v] e0). auto.
    rewrite substenv_eq.
    destruct~ (binds_not_middle_inv b) as [K|[Fr K]]. rewrite* substenv_fresh.
  (* case sub_var trans *)
  asserts* W: (_wf (E & x ~ bind_sub e V & F)).
  case_var.
    binds_mid~. inversions TEMP.
    lets: (H _ eq_refl).
    apply~ (@tsub_trans ([x ~> v] e)).
    rewrite* subst_fresh.
    apply_empty* tsub_weaken.
    apply* (@_sub_var_trans ([x~>v]e1) ([x~>v]A)).
    rewrite substenv_eq.
    destruct~ (binds_not_middle_inv b) as [K|[Fr K]]. rewrite* substenv_fresh.
  (* case: sub_abs *)
  apply_fresh* (@_sub_lam) as y; rewrite* substenv_eq.
   cross; auto. apply_ih_map_bind* H1.
  (* case: sub_app *)
  autos*.
  (* case: sub_prod *)
  apply_fresh* (@_sub_pi) as y; rewrite* substenv_eq.
   cross; auto. apply_ih_map_bind* H2. 
Qed.

Lemma typing_abs_inv : forall E e V t P,
  _typing E (trm_abs e V t) P -> exists T L,
     _typing E V trm_star
  /\ _typing E e V
  /\ (forall x, x \notin L -> _typing (E & x ~ bind_sub e V) (T ^ x) trm_star)
  /\ (_sub E (trm_prod e V T) P)
  /\ (forall x, x \notin L -> _typing (E & x ~ bind_sub e V) (t ^ x) (T ^ x)).
Proof.
  introv Typ. gen_eq u: (trm_abs e V t).
  induction Typ; intros; subst; tryfalse.
  inversions EQu. exists B L. splits*. apply* tsub_refl.
  destruct (IHTyp1 eq_refl) as [T0 [L ?]]. destructs H0.
  exists T0 L. splits*.
Qed.

Lemma typing_var_inv : forall G x A,
  _typing G (trm_var_f x) A ->
  exists e A', binds x (bind_sub e A') G /\ _sub G A' A.
Proof.
  intros.
  inductions H; tryfalse.
  destructs~ (typing_wf_from_context H0).
  exists* e A. splits*. apply* tsub_refl.
  destruct (IH_typing1 x eq_refl) as [e [A' [? ?]]].
  exists e A'. splits*.
Qed.

Lemma typing_wf_from_typing : forall E t T,
  _typing E t T ->
  _typing E T trm_star.
Proof.
  intros. inductions H; try solve [eauto 3].
  destruct* (typing_wf_from_context H0).
  destructs (typing_prod_inv IH_typing2).
  destruct H5 as [L ?].
  pick_fresh x. rewrite~ (@subst_intro x).
  unsimpl ([x ~> A](trm_star)).
  apply_empty* (@typing_substitution B e3).
Qed. 

Lemma typing_wf_from_sub : forall G e1 e2 A,
  _typing G e1 A ->
  _sub G e1 e2 ->
  _typing G e2 A.
Proof.
  introv Ty Su. gen A. inductions Su; intros; try solve [eauto 3].
  inductions Ty.
    lets: binds_func H0 H. inversions H2.
    lets: (typing_wf_from_context H H1). apply* IHSu.
    destructs~ (typing_wf_from_context H).
    apply~ (@_typing_sub A0). apply* IHTy1.
  apply* _typing_top. apply* typing_wf_from_typing.
  destruct (typing_abs_inv Ty) as [T0 [L1 ?]].
  destructs H3.
  apply~ (@_typing_sub (trm_prod e3 A T0)).
  apply_fresh* _typing_lam as y.
  apply* typing_wf_from_typing.
  inductions Ty.
    apply* (@_typing_app e3).
    apply* (@_typing_sub A0).
  destructs (typing_prod_inv Ty).
  destruct H6 as [L' ?].
  apply~ (@_typing_sub trm_star).
  apply_fresh _typing_pi as y.
    auto. auto.
    lets P1: H2 y __. auto. apply P1.
    apply_empty* (@typing_narrowing_typ e A C).
    apply* typing_wf_from_typing.
  inductions Ty; eauto 4.
  inductions Ty; eauto 4.
Qed.

Lemma _typing_sub' : forall A G e B,
  _typing G e A ->
  _sub G A B ->
  _typing G e B.
Proof.
  intros. apply* (@_typing_sub A).
  apply typing_wf_from_sub with (e1 := A).
  apply* typing_wf_from_typing.
  auto.
Qed.

Hint Resolve _typing_sub'.


Lemma typing_app_inv : forall G e A D,
  _typing G (trm_app e A) D ->
  exists e3 B C, _typing G A B /\
                 _sub G A e3 /\
                 _typing G e (trm_prod e3 B C) /\
                 _sub G (C ^^ A) D.
Proof.
  intros. gen_eq Q: (trm_app e A).
  induction H; intros; subst; tryfalse.
  inversions EQQ. exists* e3 B C. splits*.
  asserts* Typ2: (_typing G (trm_prod e3 B C) trm_star).
  apply* typing_wf_from_typing.
  destruct (typing_prod_inv Typ2) as [? [? [? [L P]]]].
  assert (_typing G (C ^^ A) trm_star).
  pick_fresh y. rewrite* (@subst_intro y).
  unsimpl([y ~> A] trm_star).
  asserts* Eq: (trm_star = trm_star ^ y).
  rewrite Eq.
  apply_empty* (@typing_substitution B e3).
  apply* tsub_refl.
  destruct~ IH_typing1 as [e3' [B' [C' [? [? ?]]]]].
  exists* e3' B' C'.
Qed.

Lemma sub_to' : forall G e1 e2 A,
  sub G e1 e2 A ->
  _typing G e1 A /\
  _sub G e1 e2.
Proof.
  apply sub_induct with
   (P0 := fun (G:env) (W:wf G) => _wf G);
   intros; subst; simpls subst.
  splits; autos*.
  splits; autos*.
  splits; autos*.
  splits; autos*.
  splits; autos*.
  (* lam *)
  splits.
  apply_fresh* _typing_lam as y.
  destructs~ (H2 y).
  destructs~ (H1 y).
  apply_fresh* _sub_lam as y.
  destructs~ (H1 y).
  (* app *)
  splits; autos*.
  (* pi *)
  splits.
  apply_fresh* _typing_pi as y.
  destructs~ (H2 y).
  apply_fresh* _sub_pi as y.
  destructs~ (H3 y).
  splits; autos*.
  splits; autos*.
  splits; autos*.
  autos*.
  autos*.
Qed.

Lemma sub_to : forall G e1 e2 A,
  sub G e1 e2 A ->
  _typing G e1 A /\ _typing G e2 A /\ _sub G e1 e2.
Proof.
  intros.
  destructs (sub_to' H).
  splits*.
  apply* typing_wf_from_sub.
Qed.

Lemma sub_wf_to : forall G,
  wf G -> _wf G.
Proof.
  intros. inductions H.
  auto. destruct (sub_to H0) as [? [? ?]].
  apply* _wf_cons.
  apply* sub_to'.
Qed.

Lemma sub_app_app_inv : forall E e1 e2 A A' T,
  sub E (trm_app e1 A) (trm_app e2 A') T ->
  exists e3 B C, A = A' /\ sub E A e3 B /\
                 sub E e1 e2 (trm_prod e3 B C) /\
                 sub E (C ^^ A) T trm_star.
Proof.
  intros. inductions H; autos*.
  exists e3 B C. splits*.
  lets: sub_wf_from_sub H.
  destruct (sub_prod_prod_inv H1) as [L T'].
  pick_fresh x. rewrite~ (@subst_intro x).
  unsimpl ([x ~> A'](trm_star)).
  apply_empty* (@sub_substitution B e3).
  destruct (IHsub1 _ _ _ _ eq_refl eq_refl) as [e3' [B' [C' ?]]].
  destructs H1.
  exists* e3' B' C'. splits*.
  apply* (@sub_trans A0).
Qed.

Lemma sub_from_aux : forall G e1 e2 A,
  sub G e1 e1 A ->
  _sub G e1 e2 ->
  sub G e1 e2 A.
Proof.
  intros. gen A.
  apply tsub_induct with
   (P := fun (G:env) e A (Typ: _typing G e A) => sub G e e A)
   (P0 := fun (G:env) (W:_wf G) => wf G)
   (P1 := fun (G:env) e1 e2 (W:_sub G e1 e2) =>
            forall A (S1: sub G e1 e1 A),
            sub G e1 e2 A);
    intros; eauto 4.

  (* case: typing sub *)
  apply* (@sub_sub' A).
  apply* H1. apply* sub_wf_from_sub.
  (* case: sub var *)
  destructs~ (sub_wf_from_context b).
  asserts* W: (sub G0 (trm_var_f x) (trm_var_f x) A).
  asserts* W2: (sub G0 (trm_var_f x) e3 A).
  apply* sub_typekeep.
  (* case: sub abs *)
  destruct (sub_abs_abs_inv S1) as [C' ?]. destructs H3.
  apply~ (@sub_sub' (trm_prod e4 A C')).
  destruct H6 as [L' ?].
  apply_fresh* sub_abs as y.
  apply* sub_wf_from_sub.
  (* case: sub app *)
  destruct (sub_app_app_inv S1) as [e3' [B' [C' ?]]].
  destructs H1.
  apply* (@sub_sub' (C' ^^ A)).
  (* case: sub prod *)
  destructs (sub_prod_prod_inv2 S1).
  destruct H8 as [L' ?].
  asserts*: (sub G0 trm_star A0 trm_star).
  destruct H4; subst; auto.
  apply~ (@sub_sub' trm_star).
  apply_fresh* sub_prod as y.
  lets P1: H8 y __. auto.
  lets P2: H3 y __. auto.
  apply~ P2. apply_empty* (@sub_narrowing_typ e C A).
  (* case: sub castup *)
  destruct (sub_castup_inv S1) as [A' ?].
  destructs H1.
  apply* (@sub_sub' A).
  (* case: sub castdn *)
  destruct (sub_castdn_inv S1) as [A' [B' ?]].
  destructs H1.
  apply* (@sub_sub' B').
Qed.

Lemma typing_to_sub_refl : forall G e A,
  _typing G e A ->
  sub G e e A.
Proof.
  intros.
  apply typing_induct with
   (P := fun (G:env) e A (Typ: _typing G e A) => sub G e e A)
   (P0 := fun (G:env) (W:_wf G) => wf G)
   (P1 := fun (G:env) e1 e2 (W:_sub G e1 e2) =>
            forall A (S1: sub G e1 e1 A),
            sub G e1 e2 A);
    intros; try solve [eauto 4 | apply* sub_from_aux].
  apply* (@sub_sub' A0).
  apply* H1. apply* sub_wf_from_sub.
Qed.

Lemma sub_from : forall G e1 e2 A,
  _typing G e1 A ->
  _sub G e1 e2 ->
  sub G e1 e2 A.
Proof.
  intros.
  apply* sub_from_aux.
  apply* typing_to_sub_refl.
Qed.

