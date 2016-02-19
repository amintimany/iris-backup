Require Import program_logic.language program_logic.hoare.
Require Import Autosubst.Autosubst.
Require Import algebra.upred_big_op.

Module lang.
Inductive expr :=
  | Var (x : var)
  | Lam (e : {bind 1 of expr})
  | App (e1 e2 : expr)
  (* Unit *)
  | Unit
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr}).

Instance Ids_expr : Ids expr. derive. Defined.
Instance Rename_expr : Rename expr. derive. Defined.
Instance Subst_expr : Subst expr. derive. Defined.
Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

Inductive val :=
  | LamV (e : {bind 1 of expr}) (* These are recursive lambdas.
                                   The *inner* binder is the recursive call! *)
  | UnitV
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Fixpoint of_val (v : val) : expr :=
  match v with
  | LamV e => Lam e
  | UnitV => Unit
  | PairV v1 v2 => Pair (of_val v1) (of_val v2)
  | InjLV v => InjL (of_val v)
  | InjRV v => InjR (of_val v)
  end.
Fixpoint to_val (e : expr) : option val :=
  match e with
  | Lam e => Some (LamV e)
  | Unit => Some UnitV
  | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
  | InjL e => InjLV <$> to_val e
  | InjR e => InjRV <$> to_val e
  | _ => None
  end.

(** Evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr}).

Notation ectx := (list ectx_item).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx e2 => App e e2
  | AppRCtx v1 => App (of_val v1) e
  | PairLCtx e2 => Pair e e2
  | PairRCtx v1 => Pair (of_val v1) e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  end.
Definition fill (K : ectx) (e : expr) : expr := fold_right fill_item e K.

Definition state : Type := ().

Inductive head_step : expr -> state -> expr -> state -> option expr -> Prop :=
  | BetaS e1 e2 v2 σ :
     to_val e2 = Some v2 →
     head_step (App (Lam e1) e2) σ e1.[e2/] σ None
  | FstS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Fst (Pair e1 e2)) σ e1 σ None
  | SndS e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     head_step (Snd (Pair e1 e2)) σ e2 σ None
  | CaseLS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjL e0) e1 e2) σ e1.[e0/] σ None
  | CaseRS e0 v0 e1 e2 σ :
     to_val e0 = Some v0 →
     head_step (Case (InjR e0) e1 e2) σ e2.[e0/] σ None.

(** Atomic expressions *)
Definition atomic (e: expr) := False.

(** Close reduction under evaluation contexts.
We could potentially make this a generic construction. *)
Inductive prim_step
    (e1 : expr) (σ1 : state) (e2 : expr) (σ2: state) (ef: option expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    head_step e1' σ1 e2' σ2 ef → prim_step e1 σ1 e2 σ2 ef.

(** Basic properties about the language *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by induction v; simplify_option_eq. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros; simplify_option_eq; auto with f_equal.
Qed.

Instance: Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

Instance ectx_fill_inj K : Inj (=) (=) (fill K).
Proof. red; induction K as [|Ki K IH]; naive_solver. Qed.

Lemma fill_app K1 K2 e : fill (K1 ++ K2) e = fill K1 (fill K2 e).
Proof. revert e; induction K1; simpl; auto with f_equal. Qed.

Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
Proof.
  intros [v' Hv']; revert v' Hv'.
  induction K as [|[]]; intros; simplify_option_eq; eauto.
Qed.

Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
Proof. rewrite !eq_None_not_Some; eauto using fill_val. Qed.

Lemma values_head_stuck e1 σ1 e2 σ2 ef :
  head_step e1 σ1 e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma values_stuck e1 σ1 e2 σ2 ef : prim_step e1 σ1 e2 σ2 ef → to_val e1 = None.
Proof. intros [??? -> -> ?]; eauto using fill_not_val, values_head_stuck. Qed.

Lemma atomic_not_val e : atomic e → to_val e = None.
Proof. done. Qed.

Lemma atomic_fill K e : atomic (fill K e) → to_val e = None → K = [].
Proof. done. Qed.

Lemma atomic_head_step e1 σ1 e2 σ2 ef :
  atomic e1 → head_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
Proof. done. Qed.

Lemma atomic_step e1 σ1 e2 σ2 ef :
  atomic e1 → prim_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
Proof.
  intros Hatomic [K e1' e2' -> -> Hstep].
  assert (K = []) as -> by eauto 10 using atomic_fill, values_head_stuck.
  naive_solver eauto using atomic_head_step.
Qed.

Lemma head_ctx_step_val Ki e σ1 e2 σ2 ef :
  head_step (fill_item Ki e) σ1 e2 σ2 ef → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
    | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
    end; auto.
Qed.

(* When something does a step, and another decomposition of the same expression
has a non-val [e] in the hole, then [K] is a left sub-context of [K'] - in
other words, [e] also contains the reducible expression *)
Lemma step_by_val K K' e1 e1' σ1 e2 σ2 ef :
  fill K e1 = fill K' e1' → to_val e1 = None → head_step e1' σ1 e2 σ2 ef →
  K `prefix_of` K'.
Proof.
  intros Hfill Hred Hnval; revert K' Hfill.
  induction K as [|Ki K IH]; simpl; intros K' Hfill; auto using prefix_of_nil.
  destruct K' as [|Ki' K']; simplify_eq.
  { exfalso; apply (eq_None_not_Some (to_val (fill K e1)));
    [apply fill_not_val | eapply head_ctx_step_val; rewrite Hfill];
    eauto using fill_not_val, head_ctx_step_val.
    Unshelve.
    assumption.
  }
  cut (Ki = Ki'); [naive_solver eauto using prefix_of_cons|].
  eauto using fill_item_no_val_inj, values_head_stuck, fill_not_val.
Qed.

End lang.

(** Language *)
Program Canonical Structure lang : language := {|
  expr := lang.expr; val := lang.val; state := lang.state;
  of_val := lang.of_val; to_val := lang.to_val;
  atomic := lang.atomic; prim_step := lang.prim_step;
|}.
Solve Obligations with eauto using lang.to_of_val, lang.of_to_val,
  lang.values_stuck, lang.atomic_not_val, lang.atomic_step.

Global Instance lang_ctx K : LanguageCtx lang (lang.fill K).
Proof.
  split.
  * eauto using lang.fill_not_val.
  * intros ????? [K' e1' e2' Heq1 Heq2 Hstep].
    by exists (K ++ K') e1' e2'; rewrite ?lang.fill_app ?Heq1 ?Heq2.
  * intros e1 σ1 e2 σ2 ? Hnval [K'' e1'' e2'' Heq1 -> Hstep].
    destruct (lang.step_by_val
      K K'' e1 e1'' σ1 e2'' σ2 ef) as [K' ->]; eauto.
    rewrite lang.fill_app in Heq1; apply (inj _) in Heq1.
    exists (lang.fill K' e2''); rewrite lang.fill_app; split; auto.
    econstructor; eauto.
Qed.

Global Instance lang_ctx_item Ki :
  LanguageCtx lang (lang.fill_item Ki).
Proof. change (LanguageCtx lang (lang.fill [Ki])). by apply _. Qed.

Import lang.

Section lang_rules.
Require Import program_logic.lifting.

Context {Σ : iFunctor}.
Implicit Types P : iProp lang Σ.
Implicit Types Q : val → iProp lang Σ.

Lemma wp_bind {E e} K Q :
  wp E e (λ v, wp E (fill K (of_val v)) Q) ⊑ wp E (fill K e) Q.
Proof. apply weakestpre.wp_bind. Qed.

Lemma wp_bindi {E e} Ki Q :
  wp E e (λ v, wp E (fill_item Ki (of_val v)) Q) ⊑ wp E (fill_item Ki e) Q.
Proof. apply weakestpre.wp_bind. Qed.

Lemma wp_lam E e1 e2 v Q :
  to_val e2 = Some v → ▷ wp E e1.[e2 /] Q ⊑ wp E (App (Lam e1) e2) Q.
Proof.
  intros <-%of_to_val.
  rewrite -(wp_lift_pure_det_step (App _ _) e1.[of_val v /] None) //=.
  * by rewrite right_id.
  * admit.
  * admit.
Admitted.

Lemma wp_fst E e1 v1 e2 v2 Q :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  ▷Q v1 ⊑ wp E (Fst (Pair e1 e2)) Q.
Proof. Admitted.

Lemma wp_snd E e1 v1 e2 v2 Q :
  to_val e1 = Some v1 → to_val e2 = Some v2 →
  ▷ Q v2 ⊑ wp E (Snd (Pair e1 e2)) Q.
Proof. Admitted.

Lemma wp_case_inl E e0 v0 e1 e2 Q :
  to_val e0 = Some v0 →
  ▷ wp E e1.[e0/] Q ⊑ wp E (Case (InjL e0) e1 e2) Q.
Proof. Admitted.

Lemma wp_case_inr E e0 v0 e1 e2 Q :
  to_val e0 = Some v0 →
  ▷ wp E e2.[e0/] Q ⊑ wp E (Case (InjR e0) e1 e2) Q.
Proof. Admitted.

End lang_rules.

Inductive type :=
  | TUnit : type
  | TProd : type → type → type
  | TSum : type → type → type
  | TArrow : type → type → type.

Inductive typed (Γ : list type) : expr → type → Prop :=
  | Var_typed x τ : Γ !! x = Some τ → typed Γ (Var x) τ
  | Unit_typed : typed Γ Unit TUnit
  | Pair_typed e1 e2 τ1 τ2 :
     typed Γ e1 τ1 → typed Γ e2 τ2 → typed Γ (Pair e1 e2) (TProd τ1 τ2)
  | Fst_typed e τ1 τ2 : typed Γ e (TProd τ1 τ2) → typed Γ (Fst e) τ1
  | Snd_typed e τ1 τ2 : typed Γ e (TProd τ1 τ2) → typed Γ (Snd e) τ2
  | InjL_typed e τ1 τ2 : typed Γ e τ1 → typed Γ (InjL e) (TSum τ1 τ2)
  | InjR_typed e τ1 τ2 : typed Γ e τ2 → typed Γ (InjR e) (TSum τ1 τ2)
  | Case_typed e0 e1 e2 τ1 τ2 ρ :
     typed Γ e0 (TSum τ1 τ2) →
     typed (τ1 :: Γ) e1 ρ → typed (τ2 :: Γ) e2 ρ →
     typed Γ (Case e0 e1 e2) ρ
  | Lam_typed e τ1 τ2 :
     typed (τ1 :: Γ) e τ2 → typed Γ (Lam e) (TArrow τ1 τ2)
  | App_typed e1 e2 τ1 τ2 :
     typed Γ e1 (TArrow τ1 τ2) → typed Γ e2 τ1 → typed Γ (App e1 e2) τ2.

Import uPred.

Section foo.
Context {Σ : iFunctor}.
Implicit Types P Q R : iProp lang Σ.
Notation "# v" := (of_val v) (at level 20).
Notation "⊤" := coPset_top.

Fixpoint interp (τ : type) (w : val) : iProp lang Σ :=
  match τ with
  | TUnit => w = UnitV
  | TProd τ1 τ2 => ∃ w1 w2, w = PairV w1 w2 ∧ ▷ interp τ1 w1 ∧ ▷ interp τ2 w2
  | TSum τ1 τ2 =>
     (∃ w1, w = InjLV w1 ∧ ▷ interp τ1 w1) ∨ (∃ w2, w = InjLV w2 ∧ ▷ interp τ1 w2)
  | TArrow τ1 τ2 =>
     □ ∀ v, ▷ interp τ1 v → wp ⊤ (App (of_val w) (of_val v)) (interp τ2)
  end%I.

Instance interp_always_stable τ v : AlwaysStable (interp τ v).
Proof. revert v; induction τ=> v /=; apply _. Qed.

Lemma typed_subst_invariant Γ e τ s1 s2 :
  typed Γ e τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ s1 s2 x, (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { rewrite /up=> s1 s2 [|x] //=; auto with f_equal omega. }
  induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with omega.
Qed.

Definition env_subst (vs : list val) (x : var) : expr :=
  from_option (Var x) (of_val <$> vs !! x).

Lemma typed_interp Γ vs e τ :
  typed Γ e τ → length Γ = length vs →
  Π∧ zip_with interp Γ vs ⊑ wp ⊤ (e.[env_subst vs]) (interp τ).
Proof.
  intros Htyped; revert vs; induction Htyped=> vs Hlen /=.
  * (* var *) destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
    { by rewrite -Hlen; apply lookup_lt_Some with τ. }
    rewrite /env_subst Hv /= -wp_value; eauto using to_of_val.
    apply big_and_elem_of, elem_of_list_lookup_2 with x.
    by rewrite lookup_zip_with; simplify_option_eq.
  * (* unit *) by rewrite -wp_value/=.
  * (* pair *) admit.
  * (* fst *) admit.
  * (* snd *) admit.
  * (* injl *) admit.
  * (* injr *) admit.
  * (* case *) admit.
  * (* lam *) rewrite -wp_value/= //=.
    apply (always_intro _ _), forall_intro=> v /=; apply impl_intro_l.
    rewrite -wp_lam ?to_of_val //=.
    assert (e.[# v .: env_subst vs] = e.[env_subst (v :: vs)]) as Hsubst.
    { rewrite /env_subst. eapply typed_subst_invariant; eauto=> /= -[|x] ? //=.
      destruct (lookup_lt_is_Some_2 vs x) as [v' Hv]; first omega; simpl.
      by rewrite Hv. }
    asimpl; rewrite Hsubst.
    rewrite (later_intro (Π∧ _)) -later_and; apply later_mono.
    apply (IHHtyped (v :: vs)); simpl; auto with f_equal.
  * admit.
Admitted.

End foo.