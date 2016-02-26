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
  | FoldV (v : expr).

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
| CLT_TRec t : closed_type k t → closed_type k (TRec t)
| CLT_TVar n : n < k → closed_type k (TVar n)
| CLT_TForall t : closed_type (S k) t → closed_type k (TForall t).

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