Set Implicit Arguments.
Require Import LibLN Main_ott Main_Infra Main_Proofs.
Implicit Types x : var.
Implicit Types G : env.

Require Alg_Aux.
Module S := Alg_Aux.

Inductive _typing : env -> trm -> trm -> trm -> Prop :=
  | _typing_star : forall G,
      _wf G -> _typing G trm_star trm_star trm_star
  | _typing_var : forall e G x A,
      _wf G -> binds x (bind_sub e A) G -> _typing G (trm_var_f x) A (trm_var_f x)
  | _typing_top : forall G A MA,
      _typing G A trm_star MA -> _typing G trm_top A (trm_anno trm_top MA)
  | _typing_lam : forall MB L G e1 e2 A B Me1 Me2 MA,
      _typing G e1 A Me1 ->
      _typing G A trm_star MA ->
      (forall x, x \notin L ->
                 _typing (G & x ~ bind_sub e1 A) (B ^ x) trm_star (MB ^ x)) ->
      (forall x, x \notin L ->
                 _typing (G & x ~ bind_sub e1 A) (e2 ^ x) (B ^ x) (Me2 ^ x)) ->
      _typing G (trm_abs e1 A e2) (trm_prod e1 A B) (trm_abs Me1 MA Me2)
  | _typing_app : forall e3 G e A B C Me MA,
      _typing G A B MA ->
      _sub G A e3 ->
      _typing G e (trm_prod e3 B C) Me ->
      _typing G (trm_app e A) (C ^^ A) (trm_app Me MA)
  | _typing_pi : forall L G e A B Me MA MB,
      _typing G e A Me ->
      _typing G A trm_star MA ->
      (forall x, x \notin L ->
        _typing (G & x ~ bind_sub e A) (B ^ x) trm_star (MB ^ x)) ->
      _typing G (trm_prod e A B) trm_star (trm_prod Me MA MB)
  | _typing_castup : forall G e A B MB Me,
      _typing G B trm_star MB ->
      _typing G e A Me ->
      reduct B A ->
      _typing G (trm_castup B e) B (trm_castup MB Me)
  | _typing_castdn : forall G e A B MB Me,
      _typing G B trm_star MB ->
      _typing G e A Me ->
      reduct A B ->
      _typing G (trm_castdn e) B (trm_anno (trm_castdn Me) MB)
  | _typing_sub : forall A G e B Me MB,
      _typing G e A Me ->
      _sub G A B ->
      _typing G B trm_star MB ->
      _typing G e B (trm_anno Me MB)

with _wf : env -> Prop :=
  | _wf_nil : _wf empty
  | _wf_cons : forall G x e A Me MA,
      x # G ->
      _typing G e A Me ->
      _typing G A trm_star MA ->
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
  | _sub_lam : forall Me3 MA L G e1 e2 e3 A,
      _typing G e3 A Me3 ->
      _typing G A trm_star MA ->
      (forall x, x \notin L -> _sub (G & x ~ bind_sub e3 A) (e1 ^ x) (e2 ^ x)) ->
      _sub G (trm_abs e3 A e1) (trm_abs e3 A e2)
  | _sub_app : forall G e1 e2 A,
      lc_trm A ->
      _sub G e1 e2 -> _sub G (trm_app e1 A) (trm_app e2 A)
  | _sub_pi : forall Me MC L G e A B C D,
      _typing G e C Me ->
      _typing G C trm_star MC ->
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

Lemma regular_typing : forall E t T M, _typing E t T M ->
  (_wf E /\ ok E /\ contains_terms E /\ lc_trm t /\ lc_trm T /\ lc_trm M). 
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
  (P := fun E t1 t2 t3 (_: _typing E t1 t2 t3) => _wf E /\ ok E /\ contains_terms E /\ lc_trm t1 /\lc_trm t2 /\ lc_trm t3); 
   unfolds contains_terms; intros; splits*.
  destructs H. lets: H0 b. jauto.
  intros. false* (binds_empty_inv).
  intros. destruct (binds_push_inv H1) as [[? P]|[? ?]]; try (inversions P); subst*.
  destructs H. apply* H5.
Qed.

Hint Extern 1 (lc_trm ?t) => match goal with
  | H: _typing _ t _ _ |- _ => apply (proj31 (proj44 (regular_typing H)))
  | H: _typing _ _ t _ |- _ => apply (proj32 (proj44 (regular_typing H)))
  | H: _typing _ _ _ t |- _ => apply (proj33 (proj44 (regular_typing H)))
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
  | H: _typing E _ _ _ |- _ => apply (proj1 (regular_typing H))
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

Lemma typing_fresh : forall E T U M x,
  _typing E T U M -> x # E -> x \notin fv T.
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

Lemma tsub_weaken : forall G E F t T,
  _sub (E & G) t T ->
  _wf (E & F & G) ->
  _sub (E & F & G) t T.
Proof.
  introv Sub Wf.
  gen_eq Env: (E & G). gen E F G.
  apply tsub_induct with
   (P := fun Env t T M (Typt : _typing Env t T M) => 
      forall E F G, _wf (E & F & G) -> Env = E & G -> 
      _typing (E & F & G) t T M)
   (P0 := fun (Env:env) (W: _wf Env) => 
      forall E F G, _wf (E & F & G) -> Env = E & G -> 
      _wf (E & F & G))
   (P1 := fun (Env:env) t T (Subt : _sub Env t T) => 
      forall E F G, _wf (E & F & G) -> Env = E & G -> 
      _sub (E & F & G) t T);
   intros; subst; simpls subst; try solve [autos*].

  (* case: var *)
  apply* _typing_var. apply* binds_weaken.
  (* case: trm_abs *)
  apply_fresh* (@_typing_lam MB) as y.
  apply_ih_bind* H1. apply_ih_bind* H2.
  (* case: trm_prod *)
  apply_fresh* (@_typing_pi) as y. apply_ih_bind* H1.

  (* case: var *)
  apply* _sub_var_refl. apply* binds_weaken.
  (* case: trans *)
  apply* (@_sub_var_trans e1 A). apply* binds_weaken.
  (* case: trm_abs *)
  apply_fresh* (@_sub_lam Me3 MA) as y.
  apply_ih_bind* H1.
  (* case: trm_prod *)
  apply_fresh* (@_sub_pi Me MC) as y. 
  apply_ih_bind* H2.
Qed.

Lemma typing_weaken : forall G E F t T M,
  _typing (E & G) t T M ->
  _wf (E & F & G) -> 
  _typing (E & F & G) t T M.
Proof.
  introv Sub Wf.
  gen_eq Env: (E & G). gen E F G.
  apply typing_induct with
   (P := fun Env t T M (Typt : _typing Env t T M) => 
      forall E F G, _wf (E & F & G) -> Env = E & G -> 
      _typing (E & F & G) t T M)
   (P0 := fun (Env:env) (W: _wf Env) => 
      forall E F G, _wf (E & F & G) -> Env = E & G -> 
      _wf (E & F & G))
   (P1 := fun (Env:env) t T (Subt : _sub Env t T) => 
      forall E F G, _wf (E & F & G) -> Env = E & G -> 
      _sub (E & F & G) t T);
   intros; subst; simpls subst; try solve [autos* | apply* tsub_weaken].

  (* case: var *)
  apply* _typing_var. apply* binds_weaken.
  (* case: trm_abs *)
  apply_fresh* (@_typing_lam MB) as y.
  apply_ih_bind* H1. apply_ih_bind* H2.
  (* case: trm_prod *)
  apply_fresh* (@_typing_pi) as y. apply_ih_bind* H1.
Qed.

Lemma tsub_refl : forall G t T M,
  _typing G t T M -> _sub G t t.
Proof.
  intros. inductions H; eauto.
Qed.

Lemma typing_wf_from_context : forall x T U (E:env),
  binds x (bind_sub T U) E -> 
  _wf E -> exists M1 M2,
  _typing E T U M1 /\
  _typing E U trm_star M2.
Proof.
  introv B W. induction E using env_ind. 
  false* binds_empty_inv. 
  destruct (binds_push_inv B) as [[? ?]|[? ?]]. 
    subst. inversions W. false (empty_push_inv H0).
     destruct (eq_push_inv H) as [? [P ?]]. inversions P. subst.
     exists Me MA.
     split; apply_empty* typing_weaken.
    induction v.
    destruct (twf_push_inv W).
    destruct~ IHE as [M1 [M2 [? ?]]].
     exists M1 M2. split; apply_empty* typing_weaken.
Qed.

Lemma typing_wf_from_twf : forall G x e A,
  _wf (G & x ~ bind_sub e A) -> exists M1 M2, _typing G e A M1 /\ _typing G A (trm_star) M2.
Proof.
  intros. inversions H.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H0) as [? [? ?]]. inversion H4. exists Me MA. subst*.
Qed.

Lemma typing_substitution_var : forall V e (F:env) (y:var) (E:env) x t T M,
  binds y (bind_sub e V) E ->
  _typing (E & x ~ bind_sub e V & F) t T M ->
  _typing (E & (map (substenv x (trm_var_f y)) F)) (subst x (trm_var_f y) t) (subst x (trm_var_f y) T) (subst x (trm_var_f y) M).
Proof.
  introv Bnd Typt.
  gen_eq G: (E & x ~ bind_sub e V & F). gen F. 
  apply typing_induct with
   (P := fun (G:env) t T M (Typt : _typing G t T M) => 
      forall (F:env), G = E & x ~ bind_sub e V & F -> 
      _typing (E & map (substenv x (trm_var_f y)) F) ([x ~> trm_var_f y]t) ([x ~> trm_var_f y]T) ([x~>trm_var_f y] M))
   (P0 := fun (G:env) (W: _wf G) => 
      forall F, G = E & x ~ bind_sub e V & F -> 
      _wf (E & (map (substenv x (trm_var_f y)) F)))
   (P1 := fun (G:env) t T (Subt : _sub G t T) => 
      forall (F:env), G = E & x ~ bind_sub e V & F -> 
      _sub (E & map (substenv x (trm_var_f y)) F) ([x ~> trm_var_f y]t) ([x ~> trm_var_f y]T)); 
   intros; subst; simpls subst; try solve [eauto 4].
  (* case: var *)
  case_var.
    binds_mid~. inversions TEMP. rewrite* subst_fresh. apply_empty* typing_weaken.
    apply* (@_typing_var e). apply* twf_left.
    apply~ (@_typing_var ([x~>trm_var_f y]e0)). rewrite substenv_eq.
    destruct~ (binds_not_middle_inv b) as [K|[Fr K]]. rewrite* substenv_fresh.
  (* case: trm_abs *)
  apply_fresh* (@_typing_lam ([x ~> trm_var_f y]MB)) as y; rewrite* substenv_eq.
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
  apply* (@_typing_sub ([x ~> trm_var_f y] A)).
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
    binds_mid~. apply_empty* tsub_weaken. 
    asserts*: (_typing E (trm_var_f y) V (trm_var_f y)).
    apply* (@_typing_var e). apply* twf_left. apply* tsub_refl.
    apply _sub_var_refl with (A := [x ~> trm_var_f y] A) (e := [x ~> trm_var_f y] e0). auto.
    rewrite substenv_eq.
    destruct~ (binds_not_middle_inv b) as [K|[Fr K]]. rewrite* substenv_fresh.
  (* case sub_var trans *)
  asserts* W: (_wf (E & x ~ bind_sub e V & F)).
  case_var.
    binds_mid~. inversions TEMP.
    lets: (H _ eq_refl).
    apply (@_sub_var_trans e V).
    rewrite <- concat_empty_r.
    apply* binds_weaken. rewrite concat_empty_r. apply* ok_from_twf.
    rewrite* subst_fresh in H0.
    apply* (@_sub_var_trans ([x~>trm_var_f y]e1) ([x~>trm_var_f y]A)).
    rewrite substenv_eq.
    destruct~ (binds_not_middle_inv b) as [K|[Fr K]]. rewrite* substenv_fresh.
  (* case: sub_abs *)
  apply_fresh* (@_sub_lam ([x~>trm_var_f y]Me3) ([x~>trm_var_f y]MA)) as y;
    rewrite* substenv_eq.
   cross; auto. apply_ih_map_bind* H1.
  (* case: sub_app *)
  autos*.
  (* case: sub_prod *)
  apply_fresh* (@_sub_pi ([x~>trm_var_f y]Me) ([x~>trm_var_f y]MC)) as y; 
    rewrite* substenv_eq.
  cross; auto. apply_ih_map_bind* H2. 
Qed.

Lemma typing_rename : forall x y E e U1 T1 T2 M,
  x \notin (fv e \u fv T2 \u fv M) -> y \notin (dom E \u fv e) ->
  _typing (E & (x ~ bind_sub U1 T1)) (e ^ x) (T2 ^ x) (M ^ x) ->
  _typing (E & (y ~ bind_sub U1 T1)) (e ^ y) (T2 ^ y) (M ^ y).
Proof.
  intros.
  tests: (x = y). auto.
  lets W: (proj1 (regular_typing H1)).
  inductions W. false* (empty_push_inv).
  destruct (eq_push_inv x) as [Eq1 [Eq2 Eq3]].
  inversions Eq2.
  rewrite* (@subst_intro x1 e).
  rewrite* (@subst_intro x1 T2).
  rewrite* (@subst_intro x1 M).
  apply_empty* (@typing_substitution_var T1 U1).
  apply* typing_weaken.
  apply _wf_cons with (MA := MA) (Me := Me).
  auto.
  apply_empty* typing_weaken.
  apply_empty* typing_weaken.
Qed.

Lemma styping_to_typing : forall G t T,
  S._typing G t T -> exists M, _typing G t T M.
Proof.
  apply S.typing_induct with
   (P0 := fun (G:env) (W:S._wf G) => _wf G)
   (P1 := fun (G:env) e1 e2 (W:S._sub G e1 e2) =>
            _sub G e1 e2);
    intros; eauto 3.
  (* top *)
  destruct H as [MA ?]. exists* (trm_anno trm_top MA).
  (* abs *)
  destruct H as [Me1 ?].
  destruct H0 as [MA ?].
  pick_fresh y.
  lets P1: H1 y __. auto. destruct P1 as [MB ?].
  lets P2: H2 y __. auto. destruct P2 as [Me2 ?].
  exists (trm_abs Me1 MA (close_var y Me2)).
  apply_fresh* (@_typing_lam (close_var y MB)) as z.
  asserts* W: (trm_star = trm_star ^ z). rewrite W.
  apply* (@typing_rename y). notin_simpl; simpl; auto.
  apply* close_var_fresh. rewrite* <- (@close_var_open y).
  apply* (@typing_rename y). notin_simpl; simpl; auto.
  apply* close_var_fresh. rewrite* <- (@close_var_open y).
  (* app *)
  destruct H as [MA ?].
  destruct H1 as [Me ?].
  exists* (trm_app Me MA).
  (* prod *)
  destruct H as [Me ?].
  destruct H0 as [MA ?].
  pick_fresh y.
  lets P1: H1 y __. auto. destruct P1 as [MB ?].
  exists (trm_prod Me MA (close_var y MB)).
  apply_fresh* (@_typing_pi) as z.
  asserts* W: (trm_star = trm_star ^ z). rewrite W.
  apply* (@typing_rename y). notin_simpl; simpl; auto.
  apply* close_var_fresh. rewrite* <- (@close_var_open y).
  (* castup *)
  destruct H as [MB ?].
  destruct H0 as [Me ?].
  exists* (trm_castup MB Me).
  (* casedn *)
  destruct H as [MB ?].
  destruct H0 as [Me ?].
  exists* (trm_anno (trm_castdn Me) MB).
  (* sub *)
  destruct H as [Me ?].
  destruct H1 as [MB ?].
  exists* (trm_anno Me MB).
  (* wf cons *)
  destruct H as [Me ?].
  destruct H0 as [MA ?].
  apply* _wf_cons.
  (* sub abs *)
  destruct H as [Me3 ?].
  destruct H0 as [MA ?].
  apply_fresh* (@_sub_lam Me3 MA) as y.
  (* sub prod *)
  destruct H as [Me ?].
  destruct H0 as [MC ?].
  apply_fresh* (@_sub_pi Me MC) as y.
Qed.

Lemma stsub_to_tsub : forall G t T,
  S._sub G t T -> _sub G t T.
Proof.
  apply S.tsub_induct with
   (P := fun G t T (W:S._typing G t T) =>
     exists M, _typing G t T M)
   (P0 := fun (G:env) (W:S._wf G) => _wf G)
   (P1 := fun (G:env) e1 e2 (W:S._sub G e1 e2) =>
            _sub G e1 e2);
    intros; eauto 3.
  (* top *)
  destruct H as [MA ?]. exists* (trm_anno trm_top MA).
  (* abs *)
  destruct H as [Me1 ?].
  destruct H0 as [MA ?].
  pick_fresh y.
  lets P1: H1 y __. auto. destruct P1 as [MB ?].
  lets P2: H2 y __. auto. destruct P2 as [Me2 ?].
  exists (trm_abs Me1 MA (close_var y Me2)).
  apply_fresh* (@_typing_lam (close_var y MB)) as z.
  asserts* W: (trm_star = trm_star ^ z). rewrite W.
  apply* (@typing_rename y). notin_simpl; simpl; auto.
  apply* close_var_fresh. rewrite* <- (@close_var_open y).
  apply* (@typing_rename y). notin_simpl; simpl; auto.
  apply* close_var_fresh. rewrite* <- (@close_var_open y).
  (* app *)
  destruct H as [MA ?].
  destruct H1 as [Me ?].
  exists* (trm_app Me MA).
  (* prod *)
  destruct H as [Me ?].
  destruct H0 as [MA ?].
  pick_fresh y.
  lets P1: H1 y __. auto. destruct P1 as [MB ?].
  exists (trm_prod Me MA (close_var y MB)).
  apply_fresh* (@_typing_pi) as z.
  asserts* W: (trm_star = trm_star ^ z). rewrite W.
  apply* (@typing_rename y). notin_simpl; simpl; auto.
  apply* close_var_fresh. rewrite* <- (@close_var_open y).
  (* castup *)
  destruct H as [MB ?].
  destruct H0 as [Me ?].
  exists* (trm_castup MB Me).
  (* casedn *)
  destruct H as [MB ?].
  destruct H0 as [Me ?].
  exists* (trm_anno (trm_castdn Me) MB).
  (* sub *)
  destruct H as [Me ?].
  destruct H1 as [MB ?].
  exists* (trm_anno Me MB).
  (* wf cons *)
  destruct H as [Me ?].
  destruct H0 as [MA ?].
  apply* _wf_cons.
  (* sub abs *)
  destruct H as [Me3 ?].
  destruct H0 as [MA ?].
  apply_fresh* (@_sub_lam Me3 MA) as y.
  (* sub prod *)
  destruct H as [Me ?].
  destruct H0 as [MC ?].
  apply_fresh* (@_sub_pi Me MC) as y.
Qed.

Lemma stwf_to_twf : forall G,
  S._wf G -> _wf G.
Proof.
  intros. inductions H; auto.
  destruct (styping_to_typing H0) as [Me ?].
  destruct (styping_to_typing H1) as [MA ?].
  apply* _wf_cons.
Qed.
  
Lemma typing_to_styping : forall G t T M,
  _typing G t T M -> S._typing G t T.
Proof.
  apply typing_induct with
   (P0 := fun (G:env) (W:_wf G) => S._wf G)
   (P1 := fun (G:env) e1 e2 (W:_sub G e1 e2) =>
            S._sub G e1 e2);
    intros; eauto 3.
Qed.

Lemma tsub_to_stsub : forall G t T,
  _sub G t T -> S._sub G t T.
Proof.
  apply tsub_induct with
   (P := fun G t T M (W:_typing G t T M) => S._typing G t T)
   (P0 := fun (G:env) (W:_wf G) => S._wf G)
   (P1 := fun (G:env) e1 e2 (W:_sub G e1 e2) =>
            S._sub G e1 e2);
    intros; eauto 3.
Qed.

Lemma twf_to_stwf : forall G,
  _wf G -> S._wf G.
Proof.
  apply twf_induct with
   (P := fun G t T M (W:_typing G t T M) => S._typing G t T)
   (P0 := fun (G:env) (W:_wf G) => S._wf G)
   (P1 := fun (G:env) e1 e2 (W:_sub G e1 e2) =>
            S._sub G e1 e2);
    intros; eauto 3.
Qed.

Fixpoint remove_anno (e : trm) {struct e} : trm :=
  match e with
  | trm_var_b i        => trm_var_b i 
  | trm_var_f x        => trm_var_f x
  | trm_star          => trm_star
  | trm_top           => trm_top
  | trm_app t1 t2     => trm_app (remove_anno t1) (remove_anno t2)
  | trm_abs t0 t1 t2  => trm_abs (remove_anno t0) (remove_anno t1) (remove_anno t2)
  | trm_prod t0 t1 t2 => trm_prod (remove_anno t0) (remove_anno t1) (remove_anno t2)
  | trm_castup t1 t2  => trm_castup (remove_anno t1) (remove_anno t2)
  | trm_castdn t1     => trm_castdn (remove_anno t1)
  | trm_anno t1 t2    => remove_anno t1
  end.

Notation "[# e #]" := (remove_anno e) (at level 2).

Definition rem_anno_env (p:binding) :=
  match p with
  | bind_sub e A => bind_sub (remove_anno e) (remove_anno A)
  end.

Lemma rem_anno_env_eq : forall e1 e2,
  bind_sub [#e1#] [#e2#] = rem_anno_env (bind_sub e1 e2).
Proof.
  intros. simpls*.
Qed.

Notation "{# E #}" := (map rem_anno_env E) (at level 2).

Lemma open_rem_comm : forall A B,
  [# A ^^ B #] = [#A#] ^^ [#B#].
Proof.
  intros. unfolds open_trm_wrt_trm. generalize 0.
  induction A; intros; simpls; autos*.
  case_nat~.
  rewrite* (IHA1 n). rewrite* (IHA2 n).
  rewrite* (IHA1 n). rewrite* (IHA2 n). rewrite* (IHA3 (S n)).
  rewrite* (IHA1 n). rewrite* (IHA2 n). rewrite* (IHA3 (S n)).
  rewrite* (IHA1 n). rewrite* (IHA2 n).
  rewrite* (IHA n).
Qed.

Lemma subst_rem : forall x u e,
  [# [x ~> u]e #] = [x ~> [#u#] ] [#e#].
Proof.
  intros. induction e; simpl; f_equal*.
  case_var*.
Qed.

Lemma rem_not_fv : forall x e,
  x \notin fv e ->
  x \notin fv [#e#].
Proof.
  intros. inductions e; simpls; autos*.
Qed.

Lemma double_rem_eq : forall A,
  [# [#A#] #] = [#A#].
Proof.
  intros. inductions A; simpls; try solve [fequals | auto].
Qed.

Lemma dbinds_rem : forall x e A E,
  binds x (bind_sub e A) E ->
  binds x (bind_sub [#e#] [#A#]) {#E#}.
Proof.
  intros. induction E using env_ind.
  false* (binds_empty_inv).
  induction v.
  destruct (binds_push_inv H) as [[? ?]|[? ?]].
  inversions H1. rewrite* rem_anno_env_eq.
  lets: (IHE H1).
  rewrite* rem_anno_env_eq.
Qed.

Lemma double_rem_env_eq : forall E,
  {# {#E#} #} = {#E#}.
Proof.
  intros. induction E using env_ind.
  rewrite map_empty.
  rewrite* map_empty.
  rewrite map_push.
  rewrite map_push.
  rewrite IHE.
  induction v.
  rewrite <- rem_anno_env_eq.
  rewrite <- rem_anno_env_eq.
  rewrite* double_rem_eq.
  rewrite* double_rem_eq.
Qed.

Lemma typing_era : forall G t T M,
  _typing G t T M -> [#M#] = t /\ {#G#} = G /\ [#t#] = t /\ [#T#] = T.
Proof.
  apply typing_induct with
   (P0 := fun (G:env) (W:_wf G) => {#G#} = G)
   (P1 := fun (G:env) e1 e2 (W:_sub G e1 e2) =>
            {#G#} = G);
    intros; simpls; try (splits*); fequals*.
  (* var *)
  lets: dbinds_rem b.
  rewrite <- H in b.
  lets: binds_func b H0.
  injection H1; intros. auto.
  (* abs *)
  pick_fresh y. destructs~ (H2 y).
  rewrite open_rem_comm in *. simpl in *.
  apply* open_var_inj. apply* rem_not_fv. auto.
  pick_fresh y. destructs~ (H2 y).
  rewrite open_rem_comm in *. simpl in *.
  apply* open_var_inj. apply* rem_not_fv. auto.
  pick_fresh y. destructs~ (H2 y).
  rewrite open_rem_comm in *. simpl in *.
  apply* open_var_inj. apply* rem_not_fv. auto.
  (* app *)
  rewrite* open_rem_comm.
  fequals*.
  destructs H1. injection H4; intros; auto.
  (* prod *)
  pick_fresh y. destructs~ (H1 y).
  rewrite open_rem_comm in *. simpl in *.
  apply* open_var_inj. apply* rem_not_fv. auto.
  pick_fresh y. destructs~ (H1 y).
  rewrite open_rem_comm in *. simpl in *.
  apply* open_var_inj. apply* rem_not_fv. auto.
  (* env nil *)
  rewrite* map_empty.
  (* env push *)
  rewrite* map_push.
  simpls.
  destructs H. rewrite H1. rewrite H2. rewrite~ H3.
Qed.

Inductive dsub : env -> trm -> trm -> Prop :=
  | dsub_star : forall G, ok G -> dsub G trm_star trm_star
  | dsub_var_refl : forall G x e A,
      ok G -> binds x (bind_sub e A) G -> dsub G (trm_var_f x) (trm_var_f x)
  | dsub_var_trans : forall e1 A G x e2,
      binds x (bind_sub e1 A) G -> dsub G e1 e2 ->
      dsub G (trm_var_f x) e2
  | dsub_top : forall G e,
      ok G -> lc_trm e -> dsub G e trm_top
  | dsub_lam : forall L G e1 e2 e3 A,
      ok G ->
      (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e3#] [#A#]) (e1 ^ x) (e2 ^ x)) ->
      dsub G (trm_abs e3 A e1) (trm_abs e3 A e2)
  | dsub_app : forall G e1 e2 A,
      lc_trm A ->
      dsub G e1 e2 -> dsub G (trm_app e1 A) (trm_app e2 A)
  | dsub_pi : forall L G e A B C D,
      dsub G C A ->
      (forall x, x \notin L -> dsub (G & x ~ bind_sub [#e#] [#C#]) (B ^ x) (D ^ x)) ->
      dsub G (trm_prod e A B) (trm_prod e C D)
  | dsub_castup : forall G A e1 e2,
      lc_trm A -> dsub G e1 e2 -> dsub G (trm_castup A e1) (trm_castup A e2)
  | dsub_castdn : forall G e1 e2,
      dsub G e1 e2 -> dsub G (trm_castdn e1) (trm_castdn e2).

Inductive dir := inf | chk.

Inductive dtyping : dir -> env -> trm -> trm -> Prop :=
  | dtyping_star : forall G,
      dwf G -> dtyping inf G trm_star trm_star
  | dtyping_var : forall e G x A,
      dwf G -> binds x (bind_sub e A) G -> dtyping inf G (trm_var_f x) A
  | dtyping_top : forall G A,
      dtyping chk G A trm_star -> dtyping chk G trm_top A
  | dtyping_lam : forall L G e1 e2 A B,
      dtyping chk G e1 [#A#] ->
      dtyping chk G A trm_star ->
      (forall x, x \notin L ->
                 dtyping inf (G & x ~ bind_sub [#e1#] [#A#]) (e2 ^ x) (B ^ x)) ->
      dtyping inf G (trm_abs e1 A e2) (trm_prod [#e1#] [#A#] B)
  | dtyping_app : forall e3 G e A B C,
      dtyping chk G A B ->
      dsub G [#A#] e3 ->
      dtyping inf G e (trm_prod e3 B C) ->
      dtyping inf G (trm_app e A) (C ^^ [#A#])
  | dtyping_pi : forall L G e A B,
      dtyping chk G e [#A#] ->
      dtyping chk G A trm_star ->
      (forall x, x \notin L ->
        dtyping chk (G & x ~ bind_sub [#e#] [#A#]) (B ^ x) trm_star) ->
      dtyping inf G (trm_prod e A B) trm_star
  | dtyping_castup : forall G e A B,
      dtyping chk G B trm_star ->
      dtyping inf G e A ->
      reduct [#B#] [#A#] ->
      dtyping inf G (trm_castup B e) [#B#]
  | dtyping_castdn : forall G e A B,
      dtyping chk G B trm_star ->
      dtyping inf G e A ->
      reduct [#A#] [#B#] ->
      dtyping chk G (trm_castdn e) B
  | dtyping_anno : forall G e A,
      dtyping chk G e A ->
      dtyping chk G A trm_star ->
      dtyping inf G (trm_anno e A) [#A#]
  | dtyping_sub : forall A G e B,
      dtyping inf G e A ->
      dsub G A [#B#] ->
      dtyping chk G B trm_star ->
      dtyping chk G e B
  | dtyping_chk : forall G e A,
      dtyping inf G e A ->
      dtyping chk G e A

with dwf : env -> Prop :=
  | dwf_nil : dwf empty
  | dwf_cons : forall G x e A,
      x # G ->
      dtyping chk G e [#A#] ->
      dtyping chk G A trm_star ->
      dwf (G & x ~ bind_sub [#e#] [#A#]).

Hint Constructors dtyping dsub dwf.

Scheme dtyping_induct := Induction for dtyping Sort Prop
  with dwf_induct := Induction for dwf Sort Prop.

Lemma typing_to_dtyping : forall G t T M,
  _typing G t T M ->
  dtyping inf G M T.
Proof.
  intros.
  apply typing_induct with
   (P := fun G t T M (Ty:_typing G t T M) =>
           dtyping inf G M T)
   (P0 := fun (G:env) (W:_wf G) => dwf G)
   (P1 := fun (G:env) e1 e2 (S:_sub G e1 e2) => dsub G e1 e2)
   (e := G) (t := t) (t0 := T) (t1 := M);
    intros; eauto 4.
  (* top *)
  asserts* P1: (_typing G0 A trm_star MA).
  destructs (typing_era P1).
  rewrite <- H1.
  apply* dtyping_anno.
  (* abs *)
  asserts* P1: (_typing G0 e1 A Me1).
  destructs (typing_era P1). destructs (typing_era _0).
  rewrite <- H4. rewrite <- H8.
  pick_fresh z. lets: _1 z __. auto.
  destructs (typing_era H12).
  rewrite open_rem_comm in *. simpl in *.
  assert ([#B#] = B).
  apply* open_var_inj. apply* rem_not_fv. auto.
  rewrite <- H17.
  apply_fresh* dtyping_lam as y. rewrite~ H8.
  rewrite H4. rewrite H8. rewrite~ H17.
  (* app *)
  asserts* P1: (_typing G0 A B MA).
  destructs (typing_era P1). destructs (typing_era _1).
  simpl in H10. injection H10; intros.
  rewrite <- H3. apply* dtyping_app.
  rewrite~ H3.
  (* prod *)
  asserts* P1: (_typing G0 e A Me).
  destructs (typing_era P1). destructs (typing_era _0).
  apply_fresh* dtyping_pi as y.
  rewrite~ H7.
  rewrite H3. rewrite~ H7.
  (* castup *)
  asserts* P1: (_typing G0 B trm_star MB).
  destructs (typing_era P1).  destructs (typing_era _0).
  rewrite <- H2. apply* dtyping_castup.
  rewrite H2. rewrite~ H9.
  (* castdn *)
  asserts* P1: (_typing G0 B trm_star MB).
  destructs (typing_era P1).  destructs (typing_era _0).
  rewrite <- H2. apply* dtyping_anno.
  apply* dtyping_castdn.
  rewrite H9. rewrite~ H2.
  (* sub *)
  asserts* P1: (_typing G0 e A Me).
  destructs (typing_era P1). destructs (typing_era _1).
  rewrite <- H7. apply* dtyping_anno.
  apply* dtyping_sub. rewrite~ H7.
  (* dwf cons *)
  asserts* P1: (_typing G0 e A Me).
  destructs (typing_era P1). destructs (typing_era _0).
  rewrite <- H2. rewrite <- H6.
  apply* dwf_cons. rewrite~ H6.
  (* sub abs *)
  apply_fresh* dsub_lam as y.
  apply* ok_from_twf.
  asserts* P1: (_typing G0 e3 A Me3).
  destructs (typing_era P1). destructs (typing_era _0).
  rewrite H5. rewrite~ H9.
  (* sub prod *)
  apply_fresh* dsub_pi as y.
  asserts* P1: (_typing G0 e C Me).
  destructs (typing_era P1). destructs (typing_era _0).
  rewrite H6. rewrite~ H7.
Qed.

Lemma tsub_to_dsub : forall G e1 e2,
  _sub G e1 e2 -> dsub G e1 e2.
Proof.
  intros.
  apply tsub_induct with
   (P := fun G t T M (Ty:_typing G t T M) =>
           dtyping inf G M T)
   (P0 := fun (G:env) (W:_wf G) => dwf G)
   (P1 := fun (G:env) e1 e2 (S:_sub G e1 e2) => dsub G e1 e2);
    intros; try solve [apply* typing_to_dtyping | eauto 4].
  (* dwf cons *)
  asserts* P1: (_typing G0 e A Me).
  destructs (typing_era P1). destructs (typing_era _0).
  rewrite <- H2. rewrite <- H6.
  apply* dwf_cons. rewrite~ H6.
  (* sub abs *)
  apply_fresh* dsub_lam as y.
  apply* ok_from_twf.
  asserts* P1: (_typing G0 e4 A Me3).
  destructs (typing_era P1). destructs (typing_era _0).
  rewrite H5. rewrite~ H9.
  (* sub prod *)
  apply_fresh* dsub_pi as y.
  asserts* P1: (_typing G0 e C Me).
  destructs (typing_era P1). destructs (typing_era _0).
  rewrite H6. rewrite~ H7.
Qed.

Lemma twf_to_wt : forall G x e A,
  S._wf (G & x ~ bind_sub e A) -> S._typing G e A /\ S._typing G A (trm_star).
Proof.
  intros. inversions H.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H0) as [? [? ?]]. inversion H4. subst*.
Qed.

Lemma open_var_rem : forall x e,
  [#e ^ x#] = [#e#] ^ x.
Proof.
  intros. rewrite* open_rem_comm.
Qed.

Lemma styping_castup_inv : forall G A e T,
  S._typing G (trm_castup A e) T ->
  exists B, S._typing G e B.
Proof.
  intros. inductions H; eauto.
Qed.

Lemma styping_castdn_inv : forall G e T,
  S._typing G (trm_castdn e) T ->
  exists B, S._typing G e B.
Proof.
  intros. inductions H; eauto.
Qed.

Lemma dsub_to_stsub : forall G e1 e2,
  dsub G e1 e2 ->
  forall A B, S._typing {#G#} [#e1#] A -> 
              S._typing {#G#} [#e2#] B ->
              S._sub {#G#} [#e1#] [#e2#].
Proof.
  intros. gen A B.
  inductions H; intros; simpls; eauto 2.
  (* case: sub var *)
  lets: dbinds_rem H0.
  apply* S._sub_var_refl.
  (* case: sub var trans *)
  lets: dbinds_rem H.
  destructs~ (S.typing_wf_from_context H3).
  apply S._sub_var_trans with (e1 := [#e1#])(A:=[#A#]).
    auto. apply* IHdsub.
  (* case: sub lam *)
  destruct (S.typing_abs_inv H2) as [TT [LL ?]].
  destructs H4.
  destruct (S.typing_abs_inv H3) as [TT2 [LL2 ?]].
  destructs H9.
  apply_fresh S._sub_lam as y.
    auto. auto. rewrite <- open_var_rem.
    rewrite <- open_var_rem. 
    rewrite <- double_rem_eq.
    asserts W2: ([#A#] = [#[#A#]#]).
    rewrite* double_rem_eq.
    rewrite W2.
    rewrite rem_anno_env_eq.
    rewrite <- map_push.
    lets M1: H1 y __. auto. lets M2: H8 y __. auto.
    lets M3: H13 y __. auto.
    rewrite map_push in *. rewrite <- rem_anno_env_eq in *.
    rewrite double_rem_eq in *.
    rewrite double_rem_eq in *.
    rewrite open_var_rem in *.
    rewrite open_var_rem in *.
    apply* M1.
  (* case: sub app *)
  destruct (S.typing_app_inv H1) as [e3' [B' [C' ?]]].
  destructs H3.
  destruct (S.typing_app_inv H2) as [e3'' [B'' [C'' ?]]].
  destructs H7.
  apply S._sub_app. auto. apply* IHdsub.
  (* case: sub prod *)
  destructs (S.typing_prod_inv H2).
  destruct H7 as [L' ?].
  destructs (S.typing_prod_inv H3).
  destruct H11 as [L'' ?].
  apply_fresh S._sub_pi as y.
    auto. auto. apply* IHdsub.
    rewrite <- open_var_rem.
    rewrite <- open_var_rem. 
    rewrite <- double_rem_eq.
    asserts W2: ([#C#] = [#[#C#]#]).
    rewrite* double_rem_eq.
    rewrite W2.
    rewrite rem_anno_env_eq.
    rewrite <- map_push.
    lets M1: H1 y __. auto. lets M2: H7 y __. auto.
    lets M3: H11 y __. auto.
    rewrite map_push in *. rewrite <- rem_anno_env_eq in *.
    rewrite double_rem_eq in *.
    rewrite double_rem_eq in *.
    rewrite open_var_rem in *.
    rewrite open_var_rem in *.
    apply (M1 trm_star) with (B0 := trm_star).
      apply_empty~ (@S.typing_narrowing_typ [#e#] [#A#] [#C#]).
      apply* IHdsub.
      auto.
  (* case: sub castup *)
  destruct (styping_castup_inv H1) as [T1 ?].
  destruct (styping_castup_inv H2) as [T2 ?].
  asserts* TM1: (lc_trm (trm_castup [#A#] [#e2#])).
  inversions TM1.
  apply S._sub_castup. auto. apply* IHdsub.
  (* case: sub castdn *)
  destruct (styping_castdn_inv H0) as [T1 ?].
  destruct (styping_castdn_inv H1) as [T2 ?].
  apply S._sub_castdn. apply* IHdsub.
Qed.

Lemma dtyping_to_styping : forall d G t T,
  dtyping d G t T ->
  S._typing {#G#} [#t#] [#T#].
Proof.
  apply dtyping_induct with
    (P := fun d G t T (Ty: dtyping d G t T) =>
      S._typing {#G#} [#t#] [#T#])
    (P0 := fun G (W: dwf G) => S._wf {#G#});
  intros; simpls; eauto 2.
  (* case: var *)
  lets: dbinds_rem b.
  apply* S._typing_var.
  (* case: abs *)
  rewrite double_rem_eq.
  rewrite double_rem_eq.
  rewrite double_rem_eq in *.
  apply_fresh S._typing_lam as y.
    auto. auto. rewrite <- open_var_rem.
    lets: H1 y __. auto.
    lets: (S.typing_wf_from_typing H2).
    rewrite map_push in *. rewrite <- rem_anno_env_eq in *.
    rewrite double_rem_eq in *. rewrite double_rem_eq in *.
    auto.
    lets: H1 y __. auto.
    rewrite map_push in *. rewrite <- rem_anno_env_eq in *.
    rewrite double_rem_eq in *. rewrite double_rem_eq in *.
    rewrite <- open_var_rem. rewrite~ <- open_var_rem.
  (* case: app *)
  rewrite open_rem_comm.
  rewrite double_rem_eq.
  lets: S.typing_wf_from_typing H0.
  destructs (S.typing_prod_inv H1).
  apply S._typing_app with (e3 := [#e3#])(B := [#B#]).
    auto. assert ([#A#] = [#[#A#]#]). rewrite *double_rem_eq.
    rewrite H6. rewrite H6 in H.
    apply* dsub_to_stsub. auto.
  (* case: prod *)
  rewrite double_rem_eq in *.
  apply_fresh S._typing_pi as y.
    auto. auto. rewrite <- open_var_rem.
    lets: H1 y __. auto.
    rewrite map_push in *. rewrite <- rem_anno_env_eq in *.
    rewrite double_rem_eq in *. rewrite double_rem_eq in *.
    auto.
  (* case: castup *)
  rewrite double_rem_eq.
  apply* S._typing_castup.
  (* case: anno *)
  rewrite* double_rem_eq.
  (* case: sub *)
  lets: S.typing_wf_from_typing H.
  apply (@S._typing_sub [#A#]).
    auto. assert ([#B#] = [#[#B#]#]). rewrite *double_rem_eq.
    rewrite H2. rewrite H2 in H0.
    apply* dsub_to_stsub. auto.
  (* case: empty *)
  rewrite~ map_empty.
  (* case: cons *)
  rewrite map_push.
  rewrite <- rem_anno_env_eq.
  rewrite double_rem_eq in *.
  rewrite double_rem_eq in *.
  apply* S._wf_cons.
Qed.

Lemma sub_to_bidir : forall G e1 e2 A,
  sub G e1 e2 A ->
  dsub G e1 e2 /\
  exists e1' e2',
    dtyping inf G e1' A /\ dtyping inf G e2' A /\
    [#e1'#] = e1 /\ [#e2'#] = e2.
Proof.
  intros. destructs (S.sub_to H).
  split.
  apply tsub_to_dsub.
  apply~ stsub_to_tsub.
  destruct (styping_to_typing H0) as [Me1 P1].
  destruct (styping_to_typing H1) as [Me2 P2].
  destructs (typing_era P1).
  destructs (typing_era P2).
  exists Me1 Me2. splits*; apply* typing_to_dtyping.
Qed.

Lemma bidir_to_sub : forall G d e1 e2 A,
  dtyping d G e1 A -> 
  dtyping d G e2 A ->
  dsub G e1 e2 ->
  sub {#G#} [#e1#] [#e2#] [#A#].
Proof.
  intros.
  lets P1: dtyping_to_styping H.
  lets P2: dtyping_to_styping H0.
  lets P3: dsub_to_stsub H1 P1 P2.
  apply* S.sub_from.
Qed.

