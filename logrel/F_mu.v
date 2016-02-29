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
  | Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
  (* Recursive Types *)
  | Fold (e : expr)
  | Unfold (e : expr)
  (* Polymorphic Types *)
  | TLam (e : {bind 1 of expr})
  | TApp (e : expr).

  Instance Ids_expr : Ids expr. derive. Defined.
  Instance Rename_expr : Rename expr. derive. Defined.
  Instance Subst_expr : Subst expr. derive. Defined.
  Instance SubstLemmas_expr : SubstLemmas expr. derive. Qed.

  Inductive val :=
  | LamV (e : {bind 1 of expr})
  | TLamV (e : {bind 1 of expr})
  | UnitV
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val)
  | FoldV (e : expr).

  Fixpoint of_val (v : val) : expr :=
    match v with
    | LamV e => Lam e
    | TLamV e => TLam e
    | UnitV => Unit
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    | InjLV v => InjL (of_val v)
    | InjRV v => InjR (of_val v)
    | FoldV e => Fold e
    end.
  Fixpoint to_val (e : expr) : option val :=
    match e with
    | Lam e => Some (LamV e)
    | TLam e => Some (TLamV e)
    | Unit => Some UnitV
    | Pair e1 e2 => v1 ← to_val e1; v2 ← to_val e2; Some (PairV v1 v2)
    | InjL e => InjLV <$> to_val e
    | InjR e => InjRV <$> to_val e
    | Fold e => Some (FoldV e)
    | _ => None
    end.

  (** Evaluation contexts *)
  Inductive ectx_item :=
  | AppLCtx (e2 : expr)
  | AppRCtx (v1 : val)
  | TAppCtx
  | PairLCtx (e2 : expr)
  | PairRCtx (v1 : val)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : {bind expr}) (e2 : {bind expr})
  | UnfoldCtx.

  Notation ectx := (list ectx_item).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | AppLCtx e2 => App e e2
    | AppRCtx v1 => App (of_val v1) e
    | TAppCtx => TApp e
    | PairLCtx e2 => Pair e e2
    | PairRCtx v1 => Pair (of_val v1) e
    | FstCtx => Fst e
    | SndCtx => Snd e
    | InjLCtx => InjL e
    | InjRCtx => InjR e
    | CaseCtx e1 e2 => Case e e1 e2
    | UnfoldCtx => Unfold e
    end.
  Definition fill (K : ectx) (e : expr) : expr := fold_right fill_item e K.

  Definition state : Type := ().

  Inductive head_step : expr -> state -> expr -> state -> option expr -> Prop :=
  (* β *)
  | BetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      head_step (App (Lam e1) e2) σ e1.[e2/] σ None
  (* Products *)
  | FstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Fst (Pair e1 e2)) σ e1 σ None
  | SndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      head_step (Snd (Pair e1 e2)) σ e2 σ None
  (* Sums *)
  | CaseLS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjL e0) e1 e2) σ e1.[e0/] σ None
  | CaseRS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      head_step (Case (InjR e0) e1 e2) σ e2.[e0/] σ None
  (* Recursive Types *)
  | Unfold_Fold e σ :
      head_step (Unfold (Fold e)) σ e σ None
  (* Polymorphic Types *)
  | TBeta e σ :
      head_step (TApp (TLam e)) σ e σ None.

  (** Atomic expressions: we don't consider any atomic operations. *)
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

  Ltac inv_step :=
    repeat match goal with
           | _ => progress simplify_map_eq/= (* simplify memory stuff *)
           | H : to_val _ = Some _ |- _ => apply of_to_val in H
           | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
           | H : prim_step _ _ _ _ _ |- _ => destruct H; subst
           | H : _ = fill ?K ?e |- _ =>
             destruct K as [|[]];
               simpl in H; first [subst e|discriminate H|injection H as H]
           (* ensure that we make progress for each subgoal *)
           | H : head_step ?e _ _ _ _, Hv : of_val ?v = fill ?K ?e |- _ =>
             apply values_head_stuck, (fill_not_val K) in H;
               by rewrite -Hv to_of_val in H (* maybe use a helper lemma here? *)
           | H : head_step ?e _ _ _ _ |- _ =>
             try (is_var e; fail 1); (* inversion yields many goals if e is a variable
     and can thus better be avoided. *)
               inversion H; subst; clear H
           end.

  Ltac reshape_val e tac :=
    let rec go e :=
        match e with
        | of_val ?v => v
        | Pair ?e1 ?e2 =>
          let v1 := reshape_val e1 in let v2 := reshape_val e2 in constr:(PairV v1 v2)
        | InjL ?e => let v := reshape_val e in constr:(InjLV v)
        | InjR ?e => let v := reshape_val e in constr:(InjRV v)
        end in let v := go e in first [tac v | fail 2].

  Ltac reshape_expr e tac :=
    let rec go K e :=
        match e with
        | _ => tac (reverse K) e
        | App ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (AppRCtx v1 :: K) e2)
        | App ?e1 ?e2 => go (AppLCtx e2 :: K) e1
        | Pair ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (PairRCtx v1 :: K) e2)
        | Pair ?e1 ?e2 => go (PairLCtx e2 :: K) e1
        | Fst ?e => go (FstCtx :: K) e
        | Snd ?e => go (SndCtx :: K) e
        | InjL ?e => go (InjLCtx :: K) e
        | InjR ?e => go (InjRCtx :: K) e
        | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0
        end in go (@nil ectx_item) e.

  Ltac do_step tac :=
    try match goal with |- language.reducible _ _ => eexists _, _, _ end;
    simpl;
    match goal with
    | |- prim_step ?e1 ?σ1 ?e2 ?σ2 ?ef =>
      reshape_expr e1 ltac:(fun K e1' =>
                              eapply Ectx_step with K e1' _; [reflexivity|reflexivity|];
                              econstructor;
                              rewrite ?to_of_val; tac; fail)
    | |- head_step ?e1 ?σ1 ?e2 ?σ2 ?ef =>
      econstructor;
        rewrite ?to_of_val; tac; fail
    end.

  Local Hint Extern 1 => do_step auto.
  Local Hint Extern 1 => inv_step.

  (** Helper Lemmas for weakestpre. *)

  Lemma wp_lam E e1 e2 v Q :
    to_val e2 = Some v → ▷ wp E e1.[e2 /] Q ⊑ wp E (App (Lam e1) e2) Q.
  Proof.
    intros <-%of_to_val.
    rewrite -(wp_lift_pure_det_step (App _ _) e1.[of_val v /] None) //=; auto.
    - by rewrite right_id.
  Qed.

  Lemma wp_fst E e1 v1 e2 v2 Q :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ▷Q v1 ⊑ wp E (Fst (Pair e1 e2)) Q.
  Proof.
    intros <-%of_to_val <-%of_to_val.
    rewrite -(wp_lift_pure_det_step (Fst (Pair _ _)) (of_val v1) None) //=; auto.
    - rewrite right_id; auto using uPred.later_mono, wp_value'.
  Qed.

  Lemma wp_snd E e1 v1 e2 v2 Q :
    to_val e1 = Some v1 → to_val e2 = Some v2 →
    ▷ Q v2 ⊑ wp E (Snd (Pair e1 e2)) Q.
  Proof.
    intros <-%of_to_val <-%of_to_val.
    rewrite -(wp_lift_pure_det_step (Snd (Pair _ _)) (of_val v2) None) //=; auto.
    - rewrite right_id; auto using uPred.later_mono, wp_value'.
  Qed.

  Lemma wp_case_inl E e0 v0 e1 e2 Q :
    to_val e0 = Some v0 →
    ▷ wp E e1.[e0/] Q ⊑ wp E (Case (InjL e0) e1 e2) Q.
  Proof.
    intros <-%of_to_val.
    rewrite -(wp_lift_pure_det_step (Case (InjL _) _ _) (e1.[of_val v0/]) None) //=; auto.
    - rewrite right_id; auto using uPred.later_mono, wp_value'.
  Qed.  

  Lemma wp_case_inr E e0 v0 e1 e2 Q :
    to_val e0 = Some v0 →
    ▷ wp E e2.[e0/] Q ⊑ wp E (Case (InjR e0) e1 e2) Q.
  Proof.
    intros <-%of_to_val.
    rewrite -(wp_lift_pure_det_step (Case (InjR _) _ _) (e2.[of_val v0/]) None) //=; auto.
    - rewrite right_id; auto using uPred.later_mono, wp_value'.
  Qed.
  
End lang_rules.

Inductive type :=
| TUnit : type
| TProd : type → type → type
| TSum : type → type → type
| TArrow : type → type → type
| TRec : type → type
| TVar (x : var)
| TForall (τ : {bind 1 of type}).

Instance Ids_type : Ids type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.
Instance SubstLemmas_typer : SubstLemmas type. derive. Qed.

Inductive closed_type (k : nat) : type → Prop :=
| CLT_TUnit : closed_type k TUnit
| CLT_TProd t t' : closed_type k t → closed_type k t' → closed_type k (TProd t t')
| CLT_TSum t t' : closed_type k t → closed_type k t' → closed_type k (TSum t t')
| CLT_TArrow t t' : closed_type k t → closed_type k t' → closed_type k (TArrow t t')
| CLT_TRec t : closed_type (S k) t → closed_type k (TRec t)
| CLT_TVar n : n < k → closed_type k (TVar n)
| CLT_TForall t : closed_type (S k) t → closed_type k (TForall t).

Hint Constructors closed_type.

Lemma closed_type_prod_1 {k : nat} {τ1 τ2 : type} :
  closed_type k (TProd τ1 τ2) → closed_type k τ1.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_prod_2 {k : nat} {τ1 τ2 : type} :
  closed_type k (TProd τ1 τ2) → closed_type k τ2.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_sum_1 {k : nat} {τ1 τ2 : type} :
  closed_type k (TSum τ1 τ2) → closed_type k τ1.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_sum_2 {k : nat} {τ1 τ2 : type} :
  closed_type k (TSum τ1 τ2) → closed_type k τ2.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_arrow_1 {k : nat} {τ1 τ2 : type} :
  closed_type k (TArrow τ1 τ2) → closed_type k τ1.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_arrow_2 {k : nat} {τ1 τ2 : type} :
  closed_type k (TArrow τ1 τ2) → closed_type k τ2.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_rec {k : nat} {τ : type} :
  closed_type k (TRec τ) → closed_type (S k) τ.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_var {k : nat} {v : var} :
  closed_type k (TVar v) → v < k.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_forall {k : nat} {τ : type} :
  closed_type k (TForall τ) → closed_type (S k) τ.
Proof. intros H; inversion H; subst; trivial. Qed.

Lemma closed_type_S (k : nat) (τ : type) : closed_type k τ → closed_type (S k) τ.
Proof. intros H; induction H; auto using closed_type with omega. Qed.

Definition closed_ctx (k : nat) (Γ : list type) := Forall (closed_type k) Γ.

Inductive typed (k : nat) (Γ : list type) : expr → type → Prop :=
| Var_typed x τ : (closed_ctx k Γ) → Γ !! x = Some τ → typed k Γ (Var x) τ
| Unit_typed : typed k Γ Unit TUnit
| Pair_typed e1 e2 τ1 τ2 :
    typed k Γ e1 τ1 → typed k Γ e2 τ2 → typed k Γ (Pair e1 e2) (TProd τ1 τ2)
| Fst_typed e τ1 τ2 : typed k Γ e (TProd τ1 τ2) → typed k Γ (Fst e) τ1
| Snd_typed e τ1 τ2 : typed k Γ e (TProd τ1 τ2) → typed k Γ (Snd e) τ2
| InjL_typed e τ1 τ2 : typed k Γ e τ1 → typed k Γ (InjL e) (TSum τ1 τ2)
| InjR_typed e τ1 τ2 : typed k Γ e τ2 → typed k Γ (InjR e) (TSum τ1 τ2)
| Case_typed e0 e1 e2 τ1 τ2 ρ :
    typed k Γ e0 (TSum τ1 τ2) →
    typed k (τ1 :: Γ) e1 ρ → typed k (τ2 :: Γ) e2 ρ →
    typed k Γ (Case e0 e1 e2) ρ
| Lam_typed e τ1 τ2 :
    typed k (τ1 :: Γ) e τ2 → typed k Γ (Lam e) (TArrow τ1 τ2)
| App_typed e1 e2 τ1 τ2 :
    typed k Γ e1 (TArrow τ1 τ2) → typed k Γ e2 τ1 → typed k Γ (App e1 e2) τ2
| TLam_typed e τ :
    typed (S k) (map (λ t, t.[ren (lift 1)]) Γ) e τ →
    typed k Γ (TLam e) (TForall τ)
| TApp_typed e τ τ':
    typed k Γ e (TForall τ) → closed_type k τ' → typed k Γ (TApp e) (τ.[τ'/])
| TFold e τ :
    typed (S k) (map (λ t, t.[ren (lift 1)]) Γ) e τ →
    typed k Γ (Fold e) (TRec τ)
| TUnfold e τ : typed k Γ e (TRec τ) → typed k Γ (Unfold e) (τ.[(TRec τ)/])
.

Import uPred.

Lemma Forall2_inside_forall {A B C} (x : C) (P : C → A → B → Prop) (l : list A) (l' : list B) :
  (∀ (x : C), Forall2 (P x) l l') → Forall2 (λ a b, ∀ x, P x a b) l l'.
Proof.
  revert l'.
  induction l; intros l' H.
  - specialize (H x); inversion H; subst; auto.
  - destruct l'; [specialize (H x); inversion H|].
    constructor; [|apply IHl]; intros z; specialize (H z); inversion H; trivial.
Qed.
    

    
(** interp : is a unary logical relation. *)
Section typed_interp.
  Context {Σ : iFunctor}.
  Implicit Types P Q R : iProp lang Σ.
  Notation "# v" := (of_val v) (at level 20).
  Notation "⊤" := coPset_top.

  Definition Vlist (A : Type) (n : nat) := {l : list A| length l = n}.

  Program Definition force_lookup {A : Type} {n : nat} (l : Vlist A n) (i : nat) (Hlt :  i < n) : A :=
    match (l : list _) !! i as u return is_Some u → A with
    | None => fun H => False_rect _ (is_Some_None H)
    | Some x => fun _ => x
    end _.
  Next Obligation.
  Proof.
    intros A n l i Hlt.
    apply lookup_lt_is_Some_2.
    destruct l; subst; trivial.
  Qed.

  Lemma length_shrink {A n x} {l : list A} : length (x :: l) = S n → length l = n.
  Proof.
    cbn; congruence.
  Qed.
  
  Program Definition Vlist_cons {A n} (x : A) (v : Vlist A n) : Vlist A (S n) :=
    ((x :: `v) ↾ _).
  Next Obligation.
  Proof.
    intros A n x [l Hv]; cbn; auto.
  Qed.
    
  Program Definition Vlist_tail {A n} (v : Vlist A (S n)) : Vlist A n :=
    match `v as u return length u = (S n) → Vlist A n with
    | nil => _
    | _ :: l' => λ H, (l' ↾ length_shrink H)
    end (proj2_sig v).
  Next Obligation.
  Proof. intros A n v H; inversion H. Qed.

  Program Definition Vlist_head {A n} (v : Vlist A (S n)) : A := force_lookup v O _.
  Solve Obligations with auto with omega.

  Definition Vlist_map {A B n} (f : A → B) (v : Vlist A n) : Vlist B n :=
    (fix fx n :=
       match n as m return Vlist A m → Vlist B m with
       | O => λ _, ([] ↾ (Logic.eq_refl))
       | S n' => λ v, Vlist_cons (f (Vlist_head v)) (fx n' (Vlist_tail v))
       end) n v.

  Lemma Vlist_map_Forall2 {A B C n} (f : A → B) (v : Vlist A n) (l : list C)
        (P : B → C → Prop) : Forall2 P (` (Vlist_map f v)) l ↔ Forall2 (λ u, P (f u)) (` v) l.
  Proof.  
    destruct v as [v Hv].
    revert n Hv l.
    induction v; intros n Hv l.
    - destruct n; cbn in *; auto; destruct l; intuition auto with omega; try inversion H.
    - destruct n; try (cbn in *; auto with omega; fail).
      destruct l; [split; intros H; inversion H|].
      split; (constructor; [inversion H; auto|]);
      inversion H; subst; cbn in *;
      eapply IHv; eauto.
  Qed.
      
  Canonical Structure leibniz_val := leibnizC val.

  Canonical Structure leibniz_le n m := leibnizC (n ≤ m).

  Section Vlist_cofe.
    Context `{A : cofeT}.
    
    Instance Vlist_equiv {n : nat} : Equiv (Vlist A n) := λ l l', Forall2 (λ x y, x ≡ y) (`l) (`l').
    Instance Vlist_dist {n : nat} : Dist (Vlist A n) := λ n l l', Forall2 (λ x y, x ≡{n}≡ y) (`l) (`l').

    Lemma force_lookup_ne {n m v v' i H} :
      v ≡{n}≡ v' → (@force_lookup _ m v i H) ≡{n}≡ (force_lookup v' i H).
    Proof.
      intros H1; unfold dist in H1; unfold Vlist_dist in *.
      destruct v as [l Hv]; destruct v' as [l' Hv']; unfold force_lookup;
      try (try inversion Hv; try inversion Hv'; fail); subst; cbn in *.
      set (H2 := λ x, @Forall2_lookup_l _ _ _ _ _ i x H1); clearbody H2.
      generalize (force_lookup_obligation_1 A (length l) (l ↾ Logic.eq_refl) i H) as H4.
      generalize (force_lookup_obligation_1 A (length l) (l' ↾ Hv') i H) as H3.
      intros [y1 H3] [y2 H4]; cbn in *. destruct (l !! i); [| congruence]. 
      edestruct H2 as [z [H21 H22]]; eauto.
      generalize (ex_intro (λ y : A, l' !! i = Some y) y1 H3) as H5.
      rewrite H21; congruence.
    Qed.
    
    Lemma force_lookup_proper {m v v' i H} :
      v ≡ v' → (@force_lookup _ m v i H) ≡ (force_lookup v' i H).
    Proof.
      intros H1; unfold dist in H1; unfold Vlist_dist in *.
      destruct v as [l Hv]; destruct v' as [l' Hv']; unfold force_lookup;
      try (try inversion Hv; try inversion Hv'; fail); subst; cbn in *.
      set (H2 := λ x, @Forall2_lookup_l _ _ _ _ _ i x H1); clearbody H2.
      generalize (force_lookup_obligation_1 A (length l) (l ↾ Logic.eq_refl) i H) as H4.
      generalize (force_lookup_obligation_1 A (length l) (l' ↾ Hv') i H) as H3.
      intros [y1 H3] [y2 H4]; cbn in *. destruct (l !! i); [| congruence]. 
      edestruct H2 as [z [H21 H22]]; eauto.
      generalize (ex_intro (λ y : A, l' !! i = Some y) y1 H3) as H5.
      rewrite H21; congruence.
    Qed.
    
    Instance Vlist_tail_ne {m n} : Proper (dist n ==> dist n) (@Vlist_tail A m).
    Proof.
      intros [v Hv] [v' Hv'] H.
      destruct v; destruct v'; try (try inversion Hv; try inversion Hv'; fail).
      inversion H; trivial.
    Qed.
    
    Instance Vlist_tail_proper {m} : Proper ((≡) ==> (≡)) (@Vlist_tail A m).
    Proof.
      intros [v Hv] [v' Hv'] H.
      destruct v; destruct v'; try (try inversion Hv; try inversion Hv'; fail).
      inversion H; trivial.
    Qed.
    
    Program Definition Vlist_chain_tail {n : nat} `(c : chain (Vlist A (S n))) : chain (Vlist A n)
      :=
        {|
          chain_car n := Vlist_tail (c n)
        |}.
    Next Obligation.
    Proof.
      intros n c m i H; cbn.
      apply Vlist_tail_ne, chain_cauchy; trivial.
    Qed.
    
    Program Definition Vlist_chain_head {n : nat} `(c : chain (Vlist A (S n))) : chain A
      :=
        {|
          chain_car n := Vlist_head (c n)
        |}.
    Next Obligation.
    Proof.
      intros n c m i H; cbn.
      apply force_lookup_ne, chain_cauchy; trivial.
    Qed.

    Definition Vlist_chain {n : nat} `(c : chain (Vlist A n)) : Vlist (chain A) n :=
      (fix fx n :=
         match n as m return chain (Vlist A m) → Vlist (chain A) m with
         | O => λ _, ([] ↾ (Logic.eq_refl))
         | S n' => λ c, Vlist_cons (Vlist_chain_head c) (fx n' (Vlist_chain_tail c))
         end) n c.
    
    Program Instance cofe_Vlist_compl {n} : Compl (Vlist A n) :=
      λ c, Vlist_map compl (Vlist_chain c).
    
    Definition cofe_Vlist_cofe_mixin {l} : CofeMixin (Vlist A l).
    Proof.
      split.
      - intros x y; split; [intros H n| intros H].
        + eapply Forall2_impl; eauto; intros; apply equiv_dist; trivial.
        + unfold dist, Vlist_dist in *.
          eapply Forall2_impl; [|intros x' y' H'; apply equiv_dist; apply H'].
          apply (Forall2_inside_forall 0); trivial.
      - intros n; split.
        + intros x. apply Reflexive_instance_0; auto.
        + intros x y. apply Symmetric_instance_0; auto.
        + intros x y z. apply Transitive_instance_0; intros x1 y1 z1 H1 H2; etransitivity; eauto.
      - intros n x y H. eapply Forall2_impl; eauto; eapply mixin_dist_S; apply cofe_mixin.        
      - intros n c; simpl.
        unfold compl, cofe_Vlist_compl.
        apply Vlist_map_Forall2.
        induction l.
        destruct (c (S n)) as [[] Hv]; [|inversion Hv]; cbn; auto.
        specialize (IHl (Vlist_chain_tail c)).
        unfold Vlist_chain_tail in IHl; cbn in *.
        destruct (c (S n)) as [[|c' l'] Hv] eqn:Heq; [inversion Hv|]; cbn in *.
        constructor; auto.
        change (c') with (Vlist_head ((c' :: l') ↾ Hv)).
        rewrite -Heq.
        change (Vlist_head (c (S n))) with (Vlist_chain_head c (S n)).
        eapply mixin_conv_compl; eauto using cofe_mixin.
    Qed.        

    Canonical Structure cofe_Vlist {l} : cofeT := CofeT (@cofe_Vlist_cofe_mixin l).
    
  End Vlist_cofe.

  Arguments cofe_Vlist _ _ : clear implicits.

  Program Definition force_lookup_morph (k : nat) (x : var) (H : x < k)
    : (cofe_Vlist (leibniz_val -n> iProp lang Σ) k) -n> leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car := λ Δ, force_lookup Δ x H
    |}.
  Next Obligation.
  Proof.
    repeat intros ?; rewrite force_lookup_ne; trivial.
  Qed.

  Program Definition Vlist_cons_morph {A : cofeT} {n : nat} :
    A -n> cofe_Vlist A n -n> cofe_Vlist A (S n) :=
    {|
      cofe_mor_car :=
        λ x,
        {|
          cofe_mor_car := λ v, Vlist_cons x v
        |}
    |}.
  Next Obligation.
  Proof. repeat intros ?; constructor; trivial. Qed.
  Next Obligation.
  Proof.
    repeat intros?; constructor; trivial; apply Forall2_Forall, Forall_forall; trivial.
  Qed.    
  
  Program Definition Vlist_cons_apply {k} (Δ : Vlist (leibniz_val -n> iProp lang Σ) k)
             (f : (cofe_Vlist (leibniz_val -n> iProp lang Σ) (S k)) -n> leibniz_val -n> iProp lang Σ)
    : (leibniz_val -n> iProp lang Σ) -n> leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car := λ g, f (Vlist_cons_morph g Δ)
    |}.
  Next Obligation.
  Proof.
    intros k Δ f n g g' H; rewrite H; trivial.
  Qed.

  Instance Vlist_cons_apply_proper {k} : Proper ((≡) ==> (≡) ==> (≡)) (@Vlist_cons_apply k).
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 f.
    unfold Vlist_cons_apply.
    cbn -[Vlist_cons_morph].
    apply cofe_mor_car_proper; trivial.
    rewrite H1; trivial.
  Qed.
  
  Instance Vlist_cons_apply_ne {k} n : Proper (dist n ==> dist n ==> dist n) (@Vlist_cons_apply k).
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 f.
    unfold Vlist_cons_apply.
    cbn -[Vlist_cons_morph].
    apply cofe_mor_car_ne; trivial.
    rewrite H1; trivial.
  Qed.
  
  Definition interp_unit : leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car := λ w, (w = UnitV)%I
    |}.

  Definition interp_prod (τ1i τ2i : leibniz_val -n> iProp lang Σ) : leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car := λ w, (∃ w1 w2, w = PairV w1 w2 ∧ ▷ τ1i w1 ∧ ▷ τ2i w2)%I
    |}.

  Instance interp_prod_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_prod.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply exist_proper =>v. apply exist_proper=> v'.
    repeat apply and_proper; trivial; first [rewrite H1|rewrite H2]; trivial.
  Qed.
  
  Instance interp_prod_ne n : Proper (dist n ==> dist n ==> dist n) interp_prod.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply exist_ne =>v. apply exist_ne=> v'.
    repeat apply and_ne; trivial; first [rewrite H1|rewrite H2]; trivial.
  Qed.
  
  Definition interp_sum (τ1i τ2i : leibniz_val -n> iProp lang Σ) : leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car := λ w, ((∃ w1, w = InjLV w1 ∧ ▷ τ1i w1) ∨
                            (∃ w2, w = InjRV w2 ∧ ▷ τ2i w2))%I
    |}.

  Instance interp_sum_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_sum.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply or_proper; apply exist_proper =>v;
      apply and_proper; try rewrite H1; try rewrite H2; auto.
  Qed.
  
  Instance interp_sum_ne n : Proper (dist n ==> dist n ==> dist n) interp_sum.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply or_ne; apply exist_ne =>v;
      apply and_ne; try rewrite H1; try rewrite H2; auto.
  Qed.

  Definition interp_arrow (τ1i τ2i : leibniz_val -n> iProp lang Σ) : leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car := λ w, (□ ∀ v, ▷ τ1i v → || (App (# w) (# v)) @ ⊤ {{τ2i}})%I
    |}.

  Instance interp_arrow_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_arrow.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_proper, forall_proper=> v;
      apply impl_proper;
      [rewrite H1; auto| apply wp_proper; auto].
  Qed.
  
  Instance interp_arrow_ne n : Proper (dist n ==> dist n ==> dist n) interp_arrow.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_ne, forall_ne=> v;
      apply impl_ne;
      [rewrite H1; auto| apply wp_ne; auto].
  Qed.
  
  Definition interp_var (k : nat) (x : var) (H : x < k)
    : (@cofe_Vlist (leibniz_val -n> iProp lang Σ) k) -n> leibniz_val -n> iProp lang Σ :=
    force_lookup_morph k x H.

  Definition interp_forall (τi : (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ))
    : leibniz_val -n> iProp lang Σ :=
    {|
      cofe_mor_car :=
        λ w,
        (∃ e, w = TLamV e ∧
              || e @ ⊤ {{λ v, ∀ (τ'i : (leibniz_val -n> iProp lang Σ)), ▷ (τi τ'i v)}})%I
    |}.

  Instance interp_forall_proper : Proper ((≡) ==> (≡)) interp_forall.
  Proof.
    intros τ τ' H1 v; cbn.
    apply exist_proper=>e; apply and_proper; trivial.
    apply wp_proper=>v'; apply forall_proper=>τi.
    rewrite H1; trivial.
  Qed.
    
  Instance interp_forall_ne n : Proper (dist n ==> dist n) interp_forall.
  Proof.
    intros τ τ' H1 v; cbn.
    apply exist_ne=>e; apply and_ne; trivial.
    apply wp_ne=>v'; apply forall_ne=>τi.
    rewrite H1; trivial.
  Qed.

  Definition interp_rec_pre
             (τi : (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ))
             (rec_apr : (leibniz_val -n> iProp lang Σ))
    : (leibniz_val -n> iProp lang Σ) :=
    {|
      cofe_mor_car := λ w, (∃ e, w = FoldV e ∧ || e @ ⊤ {{ λ v, ▷ τi rec_apr v}})%I
    |}.

  Instance interp_rec_pre_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_rec_pre.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply exist_proper=>e; apply and_proper; trivial.
    apply wp_proper=>v.
    rewrite H1 H2; trivial.
  Qed.
  
  Instance interp_rec_pre_ne n : Proper (dist n ==> dist n ==> dist n) interp_rec_pre.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply exist_ne=>e; apply and_ne; trivial.
    apply wp_ne=>v.
    rewrite H1 H2; trivial.
  Qed.
  
  Instance interp_rec_pre_contr
           (τi : (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ))
    :
      Contractive (interp_rec_pre τi).
  Proof.
    intros n f g H w; cbn.
    apply exist_ne; intros e; apply and_ne; trivial.
    apply wp_ne; intros v.
    apply later_contractive.
      intros. rewrite (cofe_mor_ne _ _ τi); eauto.
  Qed.
  
  Definition interp_rec (τi : (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ))
    := fixpoint (interp_rec_pre τi).

  Instance interp_rec_proper : Proper ((≡) ==> (≡)) interp_rec.
  Proof.
    intros τ τ' H1.
    unfold interp_rec.
    rewrite fixpoint_proper; eauto=>f.
    rewrite H1; trivial.
  Qed.
    
  Instance interp_rec_ne n : Proper (dist n ==> dist n) interp_rec.
  Proof.
    intros τ τ' H1.
    unfold interp_rec.
    rewrite fixpoint_ne; eauto=>f.
    rewrite H1; trivial.
  Qed.

  Program Fixpoint interp
           (k : nat) (τ : type) {struct τ}
    : closed_type k τ → (@cofe_Vlist (leibniz_val -n> iProp lang Σ) k) -n> leibniz_val -n> iProp lang Σ
    :=
        match τ as t return closed_type k t → _ with
        | TUnit => λ _, {| cofe_mor_car := λ Δ,interp_unit |}
        | TProd τ1 τ2 =>
          λ HC',
          {| cofe_mor_car :=
               λ Δ,interp_prod
                     (interp k τ1 (closed_type_prod_1 HC') Δ)
                     (interp k τ2 (closed_type_prod_2 HC') Δ)|}
        | TSum τ1 τ2 =>
          λ HC',
          {| cofe_mor_car :=
               λ Δ,interp_sum
                     (interp k τ1 (closed_type_sum_1 HC') Δ)
                     (interp k τ2 (closed_type_sum_2 HC') Δ)|}
        | TArrow τ1 τ2 =>
          λ HC',
          {|cofe_mor_car :=
              λ Δ, interp_arrow
                     (interp k τ1 (closed_type_arrow_1 HC') Δ)
                     (interp k τ2 (closed_type_arrow_2 HC') Δ)|}
        | TVar v => λ HC', {| cofe_mor_car := λ Δ,interp_var k v (closed_type_var HC') Δ |}
        | TForall τ' =>
          λ HC',
          {| cofe_mor_car :=
               λ Δ,
               interp_forall
                 (Vlist_cons_apply Δ (interp (S k) τ' (closed_type_forall HC'))) |}
        | TRec τ' =>
          λ HC',
          {| cofe_mor_car :=
               λ Δ, interp_rec
                      (Vlist_cons_apply Δ (interp (S k) τ' (closed_type_rec HC'))) |}
        end%I.
  Solve Obligations with repeat intros ?; match goal with [H : _ ≡{_}≡ _|- _] => rewrite H end; trivial.


End typed_interp.