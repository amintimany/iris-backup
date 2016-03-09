Require Import program_logic.language program_logic.hoare.
Require Import Autosubst.Autosubst.
Require Import algebra.upred_big_op.
Require Import logrel.Vlist.

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
  | TLam (e : expr)
  | TApp (e : expr)
  (* Reference Types *)
  | Loc (l : nat)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr).

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
  | FoldV (e : expr)
  | LocV (l : nat).

  Fixpoint of_val (v : val) : expr :=
    match v with
    | LamV e => Lam e
    | TLamV e => TLam e
    | UnitV => Unit
    | PairV v1 v2 => Pair (of_val v1) (of_val v2)
    | InjLV v => InjL (of_val v)
    | InjRV v => InjR (of_val v)
    | FoldV e => Fold e
    | LocV l => Loc l
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
    | Loc l => Some (LocV l)
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
  | UnfoldCtx
  | AllocCtx
  | LoadCtx
  | StoreLCtx (e2 : expr)
  | StoreRCtx (v1 : val).

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
    | AllocCtx => Alloc e
    | LoadCtx => Load e
    | StoreLCtx e2 => Store e e2
    | StoreRCtx v1 => Store (of_val v1) e
    end.
  
  Definition fill (K : ectx) (e : expr) : expr := fold_right fill_item e K.

  Definition state : Type := gmap nat val.

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
      head_step (TApp (TLam e)) σ e σ None
  (* Reference Types *)
  | AllocS e v σ l :
     to_val e = Some v → σ !! l = None →
     head_step (Alloc e) σ (Loc l) (<[l:=v]>σ) None
  | LoadS l v σ :
     σ !! l = Some v →
     head_step (Load (Loc l)) σ (of_val v) σ None
  | StoreS l e v σ :
     to_val e = Some v → is_Some (σ !! l) →
     head_step (Store (Loc l) e) σ (Unit) (<[l:=v]>σ) None.

  (** Atomic expressions: we don't consider any atomic operations. *)
  Definition atomic (e: expr) :=
    match e with
    | Alloc e => is_Some (to_val e)
    | Load e => is_Some (to_val e)
    | Store e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
    | _ => False
    end.

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
  Proof. destruct e; cbn; intuition auto. Qed.

  Lemma atomic_fill_item Ki e : atomic (fill_item Ki e) → is_Some (to_val e).
  Proof. destruct Ki; cbn; intuition. Qed.
  
  Lemma atomic_fill K e : atomic (fill K e) → to_val e = None → K = [].
  Proof.
    destruct K as [|k K]; cbn; trivial.
    rewrite eq_None_not_Some.
    intros H; apply atomic_fill_item, fill_val in H;
    intuition.
  Qed.

  Lemma atomic_head_step e1 σ1 e2 σ2 ef :
    atomic e1 → head_step e1 σ1 e2 σ2 ef → is_Some (to_val e2).
  Proof.
    intros H1 H2.
    destruct e1; inversion H1; inversion H2; subst;
    try rewrite to_of_val; eauto using mk_is_Some.
  Qed.

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
  From heap_lang Require Export lifting.
  From algebra Require Import upred_big_op excl dec_agree.
  From program_logic Require Export invariants ghost_ownership.
  From program_logic Require Import ownership auth.
  Import uPred.
  (* TODO: The entire construction could be generalized to arbitrary languages that have
   a finmap as their state. Or maybe even beyond "as their state", i.e. arbitrary
   predicates over finmaps instead of just ownP. *)

  Definition heapR : cmraT := mapR loc (exclR (dec_agreeR val)).

  (** The CMRA we need. *)
  Class heapG Σ := HeapG {
                       heap_inG :> authG heap_lang Σ heapR;
                       heap_name : gname
                     }.
  (** The Functor we need. *)
  Definition heapGF : gFunctor := authGF heapR.

  Definition to_heap : state → heapR := fmap (λ v, Excl (DecAgree v)).
  Definition of_heap : heapR → state :=
    omap (mbind (maybe DecAgree) ∘ maybe Excl).

  Section definitions.
    Context `{i : heapG Σ}.

    Definition heap_mapsto (l : loc) (v: val) : iPropG heap_lang Σ :=
      auth_own heap_name {[ l := Excl (DecAgree v) ]}.
    Definition heap_inv (h : heapR) : iPropG heap_lang Σ :=
      ownP (of_heap h).
    Definition heap_ctx (N : namespace) : iPropG heap_lang Σ :=
      auth_ctx heap_name N heap_inv.

    Global Instance heap_inv_proper : Proper ((≡) ==> (≡)) heap_inv.
    Proof. solve_proper. Qed.
    Global Instance heap_ctx_always_stable N : AlwaysStable (heap_ctx N).
    Proof. apply _. Qed.
  End definitions.
  Typeclasses Opaque heap_ctx heap_mapsto.

  Notation "l ↦ v" := (heap_mapsto l v) (at level 20) : uPred_scope.

  Section heap.
    Context {Σ : gFunctors}.
    Implicit Types N : namespace.
    Implicit Types P Q : iPropG heap_lang Σ.
    Implicit Types Φ : val → iPropG heap_lang Σ.
    Implicit Types σ : state.
    Implicit Types h g : heapR.

    (** Conversion to heaps and back *)
    Global Instance of_heap_proper : Proper ((≡) ==> (=)) of_heap.
    Proof. solve_proper. Qed.
    Lemma from_to_heap σ : of_heap (to_heap σ) = σ.
    Proof.
      apply map_eq=>l. rewrite lookup_omap lookup_fmap. by case (σ !! l).
    Qed.
    Lemma to_heap_valid σ : ✓ to_heap σ.
    Proof. intros l. rewrite lookup_fmap. by case (σ !! l). Qed.
    Lemma of_heap_insert l v h :
      of_heap (<[l:=Excl (DecAgree v)]> h) = <[l:=v]> (of_heap h).
    Proof. by rewrite /of_heap -(omap_insert _ _ _ (Excl (DecAgree v))). Qed.
    Lemma of_heap_singleton_op l v h :
      ✓ ({[l := Excl (DecAgree v)]} ⋅ h) →
      of_heap ({[l := Excl (DecAgree v)]} ⋅ h) = <[l:=v]> (of_heap h).
    Proof.
      intros Hv. apply map_eq=> l'; destruct (decide (l' = l)) as [->|].
      - move: (Hv l). rewrite /of_heap lookup_insert
                              lookup_omap (lookup_op _ h) lookup_singleton.
        case _:(h !! l)=>[[[v'|]||]|] //=.
      - rewrite /of_heap lookup_insert_ne // !lookup_omap.
          by rewrite (lookup_op _ h) lookup_singleton_ne // left_id.
    Qed.
    Lemma to_heap_insert l v σ :
      to_heap (<[l:=v]> σ) = <[l:=Excl (DecAgree v)]> (to_heap σ).
    Proof. by rewrite /to_heap -fmap_insert. Qed.
    Lemma of_heap_None h l :
      ✓ h → of_heap h !! l = None → h !! l = None ∨ h !! l ≡ Some (Excl DecAgreeBot)
                                    ∨ h !! l ≡ Some ExclUnit.
    Proof.
      move=> /(_ l). rewrite /of_heap lookup_omap.
        case: (h !! l)=>[[[v|]||]|] //=; destruct 1; auto.
    Qed.
    Lemma heap_store_valid l h v1 v2 :
      ✓ ({[l := Excl (DecAgree v1)]} ⋅ h) →
      ✓ ({[l := Excl (DecAgree v2)]} ⋅ h).
    Proof.
      intros Hv l'; move: (Hv l'). destruct (decide (l' = l)) as [->|].
      - rewrite !lookup_op !lookup_singleton.
        case: (h !! l)=>[x|]; [|done]=> /excl_validN_inv_l=>-> //; auto using nat.
      - by rewrite !lookup_op !lookup_singleton_ne.
    Qed.
    Hint Resolve heap_store_valid.

    (** Allocation *)
    Lemma heap_alloc N E σ :
      authG heap_lang Σ heapR → nclose N ⊆ E →
      ownP σ ⊑ (|={E}=> ∃ _ : heapG Σ, heap_ctx N ∧ Π★{map σ} (λ l v, l ↦ v)).
    Proof.
      intros. rewrite -{1}(from_to_heap σ). etrans.
      { rewrite [ownP _]later_intro.
        apply (auth_alloc (ownP ∘ of_heap) N E (to_heap σ)); last done.
        apply to_heap_valid. }
      apply pvs_mono, exist_elim=> γ.
      rewrite -(exist_intro (HeapG _ _ γ)) /heap_ctx; apply and_mono_r.
      rewrite /heap_mapsto /heap_name.
      induction σ as [|l v σ Hl IH] using map_ind.
      { rewrite big_sepM_empty; apply True_intro. }
      rewrite to_heap_insert big_sepM_insert //.
      rewrite (map_insert_singleton_op (to_heap σ));
        last rewrite lookup_fmap Hl; auto.
        (* FIXME: investigate why we have to unfold auth_own here. *)
        by rewrite auth_own_op IH. 
    Qed.

    Context `{heapG Σ}.

    (** General properties of mapsto *)

    Lemma heap_mapsto_op l v1 v2 :
      (l ↦ v1 ★ l ↦ v2)%I ≡ (False)%I.
    Proof.
      rewrite -auth_own_op map_op_singleton //.
      
      
      apply (anti_symm (⊑)).
        rewrite auth_own_valid map_validI (forall_elim l) lookup_singleton.
        rewrite option_validI excl_validI.
      unfold cmra_op; cbn; trivial.
      rewrite auth_own_valid map_validI (forall_elim l) lookup_singleton.
      rewrite option_validI excl_validI.
      unfold cmra_op; cbn; trivial.
      
      apply excl_validN_inv_l.
      excl_validI discrete_valid. by apply const_elim_r.
    Qed.

    Lemma heap_mapsto_op_split l q v :
      (l ↦{q} v)%I ≡ (l ↦{q/2} v ★ l ↦{q/2} v)%I.
    Proof. by rewrite heap_mapsto_op_eq Qp_div_2. Qed.

    (** Weakest precondition *)
    Lemma wp_alloc N E e v P Φ :
      to_val e = Some v →
      P ⊑ heap_ctx N → nclose N ⊆ E →
      P ⊑ (▷ ∀ l, l ↦ v -★ Φ (LocV l)) →
      P ⊑ #> Alloc e @ E {{ Φ }}.
    Proof.
      rewrite /heap_ctx /heap_inv=> ??? HP.
      trans (|={E}=> auth_own heap_name ∅ ★ P)%I.
      { by rewrite -pvs_frame_r -(auth_empty _ E) left_id. }
      apply wp_strip_pvs, (auth_fsa heap_inv (wp_fsa (Alloc e)))
      with N heap_name ∅; simpl; eauto with I.
      rewrite -later_intro. apply sep_mono_r,forall_intro=> h; apply wand_intro_l.
      rewrite -assoc left_id; apply const_elim_sep_l=> ?.
      rewrite -(wp_alloc_pst _ (of_heap h)) //.
      apply sep_mono_r; rewrite HP; apply later_mono.
      apply forall_mono=> l; apply wand_intro_l.
      rewrite always_and_sep_l -assoc; apply const_elim_sep_l=> ?.
      rewrite -(exist_intro (op {[ l := Frac 1 (DecAgree v) ]})).
      repeat erewrite <-exist_intro by apply _; simpl.
      rewrite -of_heap_insert left_id right_id.
      rewrite /heap_mapsto. ecancel [_ -★ Φ _]%I.
      rewrite -(map_insert_singleton_op h); last by apply of_heap_None.
      rewrite const_equiv; last by apply (map_insert_valid h).
        by rewrite left_id -later_intro.
    Qed.

    Lemma wp_load N E l q v P Φ :
      P ⊑ heap_ctx N → nclose N ⊆ E →
      P ⊑ (▷ l ↦{q} v ★ ▷ (l ↦{q} v -★ Φ v)) →
      P ⊑ #> Load (Loc l) @ E {{ Φ }}.
    Proof.
      rewrite /heap_ctx /heap_inv=> ?? HPΦ.
      apply (auth_fsa' heap_inv (wp_fsa _) id)
      with N heap_name {[ l := Frac q (DecAgree v) ]}; simpl; eauto with I.
      rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
      rewrite -assoc; apply const_elim_sep_l=> ?.
      rewrite -(wp_load_pst _ (<[l:=v]>(of_heap h))) ?lookup_insert //.
      rewrite const_equiv // left_id.
      rewrite /heap_inv of_heap_singleton_op //.
      apply sep_mono_r, later_mono, wand_intro_l. by rewrite -later_intro.
    Qed.

    Lemma wp_store N E l v' e v P Φ :
      to_val e = Some v →
      P ⊑ heap_ctx N → nclose N ⊆ E →
      P ⊑ (▷ l ↦ v' ★ ▷ (l ↦ v -★ Φ (LitV LitUnit))) →
      P ⊑ #> Store (Loc l) e @ E {{ Φ }}.
    Proof.
      rewrite /heap_ctx /heap_inv=> ??? HPΦ.
      apply (auth_fsa' heap_inv (wp_fsa _) (alter (λ _, Frac 1 (DecAgree v)) l))
      with N heap_name {[ l := Frac 1 (DecAgree v') ]}; simpl; eauto with I.
      rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
      rewrite -assoc; apply const_elim_sep_l=> ?.
      rewrite -(wp_store_pst _ (<[l:=v']>(of_heap h))) ?lookup_insert //.
      rewrite /heap_inv alter_singleton insert_insert !of_heap_singleton_op; eauto.
      rewrite const_equiv; last naive_solver.
      apply sep_mono_r, later_mono, wand_intro_l. by rewrite left_id -later_intro.
    Qed.

    Lemma wp_cas_fail N E l q v' e1 v1 e2 v2 P Φ :
      to_val e1 = Some v1 → to_val e2 = Some v2 → v' ≠ v1 →
      P ⊑ heap_ctx N → nclose N ⊆ E →
      P ⊑ (▷ l ↦{q} v' ★ ▷ (l ↦{q} v' -★ Φ (LitV (LitBool false)))) →
      P ⊑ #> CAS (Loc l) e1 e2 @ E {{ Φ }}.
    Proof.
      rewrite /heap_ctx /heap_inv=>????? HPΦ.
      apply (auth_fsa' heap_inv (wp_fsa _) id)
      with N heap_name {[ l := Frac q (DecAgree v') ]}; simpl; eauto 10 with I.
      rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
      rewrite -assoc; apply const_elim_sep_l=> ?.
      rewrite -(wp_cas_fail_pst _ (<[l:=v']>(of_heap h))) ?lookup_insert //.
      rewrite const_equiv // left_id.
      rewrite /heap_inv !of_heap_singleton_op //.
      apply sep_mono_r, later_mono, wand_intro_l. by rewrite -later_intro.
    Qed.

    Lemma wp_cas_suc N E l e1 v1 e2 v2 P Φ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      P ⊑ heap_ctx N → nclose N ⊆ E →
      P ⊑ (▷ l ↦ v1 ★ ▷ (l ↦ v2 -★ Φ (LitV (LitBool true)))) →
      P ⊑ #> CAS (Loc l) e1 e2 @ E {{ Φ }}.
    Proof.
      rewrite /heap_ctx /heap_inv=> ???? HPΦ.
      apply (auth_fsa' heap_inv (wp_fsa _) (alter (λ _, Frac 1 (DecAgree v2)) l))
      with N heap_name {[ l := Frac 1 (DecAgree v1) ]}; simpl; eauto 10 with I.
      rewrite HPΦ{HPΦ}; apply sep_mono_r, forall_intro=> h; apply wand_intro_l.
      rewrite -assoc; apply const_elim_sep_l=> ?.
      rewrite -(wp_cas_suc_pst _ (<[l:=v1]>(of_heap h))) //;
                                                         last by rewrite lookup_insert.
      rewrite /heap_inv alter_singleton insert_insert !of_heap_singleton_op; eauto.
      rewrite lookup_insert const_equiv; last naive_solver.
      apply sep_mono_r, later_mono, wand_intro_l. by rewrite left_id -later_intro.
    Qed.
  End heap.





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

  Lemma wp_TLam E e Q :
    ▷ wp E e Q ⊑ wp E (TApp (TLam e)) Q.
  Proof.
    rewrite -(wp_lift_pure_det_step (TApp _) e None) //=; auto.
    - by rewrite right_id.
  Qed.

  Lemma wp_Fold E e Q :
    ▷ wp E e Q ⊑ wp E (Unfold (Fold e)) Q.
  Proof.
    rewrite -(wp_lift_pure_det_step (Unfold _) e None) //=; auto.
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
| TRec (τ : {bind 1 of type})
| TVar (x : var)
| TForall (τ : {bind 1 of type})
| Tref (τ : type)
.

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
| CLT_TForall t : closed_type (S k) t → closed_type k (TForall t)
| CLT_Tref t : closed_type k t → closed_type k (Tref t)
.

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

Lemma closed_type_ref {k : nat} {τ : type} :
  closed_type k (Tref τ) → closed_type k τ.
Proof. intros H; inversion H; subst; trivial. Qed.

Local Hint Resolve closed_type_prod_1 closed_type_prod_2 closed_type_sum_1
      closed_type_sum_2 closed_type_arrow_1 closed_type_arrow_2
      closed_type_rec closed_type_var closed_type_forall closed_type_ref.

Lemma closed_type_S (k : nat) (τ : type) : closed_type k τ → closed_type (S k) τ.
Proof. intros H; induction H; auto using closed_type with omega. Qed.

Lemma closed_type_le (k k' : nat) (τ : type) : k ≤ k' → closed_type k τ → closed_type k' τ.
Proof. intros H; induction H; auto using closed_type, closed_type_S with omega. Qed.

Definition closed_ctx (k : nat) (Γ : list type) := Forall (closed_type k) Γ.

Lemma closed_ctx_S (k : nat) (Γ : list type) : closed_ctx k Γ → closed_ctx (S k) Γ.
Proof. intros H. eapply Forall_impl; [| apply closed_type_S]; trivial. Qed.

Lemma closed_ctx_le (k k' : nat) (Γ : list type) : k ≤ k' → closed_ctx k Γ → closed_ctx k' Γ.
Proof. intros H; induction H; auto using closed_type, closed_ctx_S with omega. Qed.

Lemma closed_ctx_closed_type (k : nat) (Γ : list type) (x : var) (τ : type) :
  closed_ctx k Γ → Γ !! x = Some τ → closed_type k τ.
Proof. intros; eapply Forall_lookup; eauto. Qed.

Lemma closed_ctx_map (k k' : nat) (Γ : list type) (f : type → type) :
  closed_ctx k Γ →
  (∀ τ, closed_type k τ → closed_type k' (f τ)) →
  closed_ctx k' (map f Γ).
Proof.
  revert k k' f.
  induction Γ; intros k k' f H1 H2; cbn; constructor;
  inversion H1; subst; auto.
  eapply IHΓ; eauto.
Qed.

Program Fixpoint zipwith_Forall {A : Type} {P : A → Prop} (l : list A) (H : Forall P l) :
  list ({x : A | P x}) :=
  match l as u return Forall P u → _ with
  | [] => λ _, []
  | a :: l' => λ H, (a ↾ _) :: (zipwith_Forall l' _)
  end H.
Solve Obligations with repeat intros ?; match goal with [H : Forall _ _ |- _] => inversion H; trivial end.

Lemma zipwith_Forall_lookup {A : Type} {P : A → Prop} (l : list A) (Hf : Forall P l) (x : A) (n : nat) :
  l !! n = Some x → {Hx : P x| (zipwith_Forall l Hf) !! n = Some (x ↾ Hx)}.
Proof.
  revert n.
  induction l; intros n H1; cbn in *; [inversion H1|].
  destruct n; [cbn in *; inversion H1; subst|]; eauto.
Qed.
  
Definition closed_ctx_list (k : nat) (Γ : list type) (H : closed_ctx k Γ) :
  list ({τ : type | closed_type k τ}) := zipwith_Forall Γ H.

Inductive typed (k : nat) (Γ : list type) : expr → type → Prop :=
| Var_typed x τ : (closed_ctx k Γ) → Γ !! x = Some τ → typed k Γ (Var x) τ
| Unit_typed : closed_ctx k Γ → typed k Γ Unit TUnit
| Pair_typed e1 e2 τ1 τ2 :
    typed k Γ e1 τ1 → typed k Γ e2 τ2 → typed k Γ (Pair e1 e2) (TProd τ1 τ2)
| Fst_typed e τ1 τ2 : typed k Γ e (TProd τ1 τ2) → typed k Γ (Fst e) τ1
| Snd_typed e τ1 τ2 : typed k Γ e (TProd τ1 τ2) → typed k Γ (Snd e) τ2
| InjL_typed e τ1 τ2 : typed k Γ e τ1 → closed_type k τ2 → typed k Γ (InjL e) (TSum τ1 τ2)
| InjR_typed e τ1 τ2 : typed k Γ e τ2 → closed_type k τ1 → typed k Γ (InjR e) (TSum τ1 τ2)
| Case_typed e0 e1 e2 τ1 τ2 ρ :
    typed k Γ e0 (TSum τ1 τ2) →
    typed k (τ1 :: Γ) e1 ρ → typed k (τ2 :: Γ) e2 ρ →
    typed k Γ (Case e0 e1 e2) ρ
| Lam_typed e τ1 τ2 :
    typed k (τ1 :: Γ) e τ2 → typed k Γ (Lam e) (TArrow τ1 τ2)
| App_typed e1 e2 τ1 τ2 :
    typed k Γ e1 (TArrow τ1 τ2) → typed k Γ e2 τ1 → typed k Γ (App e1 e2) τ2
| TLam_typed e τ :
    typed (S k) (map (λ t, t.[ren (+1)]) Γ) e τ →
    typed k Γ (TLam e) (TForall τ)
| TApp_typed e τ τ':
    typed k Γ e (TForall τ) → closed_type k τ' → typed k Γ (TApp e) (τ.[τ'/])
| TFold e τ :
    typed (S k) (map (λ t, t.[ren (+1)]) Γ) e τ →
    typed k Γ (Fold e) (TRec τ)
| TUnfold e τ : typed k Γ e (TRec τ) → typed k Γ (Unfold e) (τ.[(TRec τ)/])
| TAlloc e τ : typed k Γ e τ → typed k Γ (Alloc e) (Tref τ)
| TLoad e τ : typed k Γ e (Tref τ) → typed k Γ (Load e) τ
| TStore e e' τ :
    typed k Γ e (Tref τ) → typed k Γ e' τ → typed k Γ (Store e e') TUnit
.

Lemma closed_type_subst_invariant k τ s1 s2 :
  closed_type k τ → (∀ x, x < k → s1 x = s2 x) → τ.[s1] = τ.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ {A} `{Ids A} `{Rename A}
            (s1 s2 : nat → A) x, (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { intros A H1 H2. rewrite /up=> s1 s2 [|x] //=; auto with f_equal omega. }
  induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with omega.
Qed.

Fixpoint iter (n : nat) `(f : A → A) :=
  match n with
  | O => λ x, x
  | S n' => λ x, f (iter n' f x)
  end.

Lemma iter_S (n : nat) `(f : A → A) (x : A) : iter (S n) f x = iter n f (f x).
Proof.
  induction n; cbn; trivial.
  rewrite -IHn; trivial.
Qed.
  
Lemma iter_upren (m x : nat) f : iter m upren f x = if lt_dec x m then x else m + (f (x - m)).
Proof.
  revert x; induction m; cbn; auto with omega.
  intros x; destruct x; cbn; trivial.
  rewrite IHm; repeat destruct lt_dec; auto with omega.  
Qed.
  
Lemma iter_up (m x : nat) (f : var → type) : iter m up f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
Proof.
  revert x; induction m; cbn; auto with omega.
  intros x; destruct x; cbn; asimpl; trivial.
  intros x; destruct x; cbn; asimpl; trivial.
  rewrite IHm; repeat destruct lt_dec; auto with omega.
  asimpl; trivial.
Qed.

Lemma closed_type_S_ren1:
  ∀ (τ : type) (n m : nat) (k : nat) (Hle : m ≤ k),
    (closed_type (n + k) τ.[ren ((iter m upren) (+n))] → closed_type k τ).
Proof.
  induction τ; intros n m k Hle H; inversion H; subst; constructor; eauto 2 with omega;
  try eapply (IHτ n (S m)); asimpl in *; auto with omega.
  rewrite iter_upren in H1; destruct lt_dec; cbn in *; omega.
Qed.

Lemma closed_type_S_ren2:
  ∀ (τ : type) (n m : nat) (k : nat),
    (closed_type k τ → closed_type (n + k) τ.[ren ((iter m upren) (+n))]).
Proof.
  induction τ; intros n m k H; inversion H; subst; constructor; eauto 2 with omega;
  try (replace (up (ren (iter m upren (+n)))) with
    (ren (iter (S m) upren (+n))) by (asimpl; trivial);
    replace (S (n + k)) with (n + (S k)) by omega; auto with omega).
  rewrite iter_upren; destruct lt_dec; cbn in *; omega.
Qed.

Lemma closed_type_pred_ren1:
  ∀ (τ : type) (n m : nat) (k : nat),
    (closed_type k τ.[ren ((iter m upren) (λ x, x - n))] → closed_type (n + k) τ).
Proof.
  induction τ; intros n m k H; inversion H; subst; constructor; eauto 2 with omega;  
  try (replace (S (n + k)) with (n + (S k)) by omega;
  apply IHτ with (S m);
  replace (up (ren (iter m upren (λ x, x - n)))) with
  (ren (iter (S m) upren (λ x, x - n))) in H1 by (asimpl; trivial); trivial).
  rewrite iter_upren in H1; destruct lt_dec; omega.
Qed.

Lemma closed_type_pred_ren2:
  ∀ (τ : type) (n m : nat) (k : nat) (Hle : m < k),
    closed_type (n + k) τ → closed_type k τ.[ren ((iter m upren) (λ x, x - n))].
Proof.
  induction τ; intros n m k Hle H; inversion H; subst; constructor; eauto 2 with omega;
  try (replace (up (ren (iter m upren (λ x, x - n)))) with
    (ren (iter (S m) upren (λ x, x - n))) by (asimpl; trivial); trivial;
    eapply (IHτ n (S m)); asimpl in *; auto with omega).
  rewrite iter_upren; destruct lt_dec; omega.
Qed.

Lemma closed_ctx_map_S:
  ∀ (k : nat) (Γ : list type), closed_ctx (S k) (map (λ t : type, t.[ren (+1)]) Γ) → closed_ctx k Γ.
Proof.
  intros k Γ H.
  induction Γ; constructor; inversion H; subst.
  eapply closed_type_S_ren1 with 1 0; cbn; auto with omega.
  apply IHΓ; trivial.
Qed.

Lemma closed_type_subst_up_subst (m : nat) (k : nat) (τ : {bind type}) (τ' : type) :
  closed_type k τ' → closed_type (m + k) τ → closed_type (m + k) τ.[iter m up (τ' .: ids)].
Proof.
  revert m k τ'.
  induction τ; intros m k τ' H1 H2; try constructor; inversion H2; subst; auto;
  try (change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids));
        change (S (m + k)) with (S m + k);
        apply IHτ; cbn; auto using closed_type_S).
  cbn; rewrite iter_up; destruct lt_dec.
  constructor; auto.
  asimpl; apply (closed_type_S_ren2 _ m 0).
  remember (x - m) as u; destruct u; try constructor; auto with omega.
Qed.

Lemma closed_type_all_closed_subst (m k : nat) (τ : type) (f : var → type) :
  (∀ x, closed_type k (f x)) → closed_type (m + k) τ.[iter m up f].
Proof.
  revert m k.
  induction τ; intros m k H; try constructor; auto;
  try (change (up (iter m up f)) with (iter (S m) up f);
        change (S (m + k)) with (S m + k);
        apply IHτ; cbn; auto using closed_type_S).
  cbn; rewrite iter_up; destruct lt_dec.
  constructor; auto with omega.
  asimpl; apply (closed_type_S_ren2 _ m 0); trivial.
Qed.

Lemma closed_type_rel_closed_subst (n k : nat) (τ : type) (f : var → type) :
  (∀ x, x < n → closed_type k (f x)) → closed_type n τ → closed_type k τ.[f].
Proof.
  revert f n k.
  induction τ; intros f n k H1 H2; inversion H2; subst; try constructor; cbn; auto;
  try ((eapply IHτ + eapply IHτ1 + eapply IHτ2); cbn; eauto 2 using closed_type_S; fail);
  try (eapply IHτ; eauto 2;
       intros x Hx; destruct x; asimpl;
       try constructor; auto using (closed_type_S_ren2 _ 1 0) with omega).
Qed.

Lemma closed_type_subst_wiht_up (k m : nat) (τ : type) (τ' : type) :
  m ≤ k → closed_type (k - m) τ' → closed_type (S k) τ →
  closed_type k τ.[iter m up (τ' .: ids)].
Proof.
  revert k m τ'.
  induction τ; intros k m τ' Hlt H1 H2; inversion H2; subst; try constructor; auto.
  - change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids));
    apply IHτ; auto with omega.
  - cbn.
    rewrite iter_up.
    destruct lt_dec.
    + auto with omega.
    + asimpl.
      remember (x - m) as u.
      destruct u; cbn in *.
      * replace k with (m + (k - m)) by omega.
        apply (closed_type_S_ren2 _ m 0); trivial.
      * asimpl; constructor; omega.
  - change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids));
    apply IHτ; auto with omega.
Qed.

Lemma closed_type_subst (k : nat) (τ : type) (τ' : type) :
  closed_type k τ' → closed_type (S k) τ → closed_type k τ.[τ'/].
Proof.
  intros H1 H2.
  apply (closed_type_subst_wiht_up _ 0);
    try replace (k - 0) with k; auto with omega.
Qed.

Lemma typed_closed_ctx_closed_type (k : nat) (Γ : list type) (e : expr) (τ : type) :
  typed k Γ e τ → closed_ctx k Γ ∧ closed_type k τ.
Proof.
  intros H; induction H; intuition; eauto 3 using closed_ctx_closed_type;
  match goal with
  | [H : closed_ctx _ (_ :: _) |- _] =>
    inversion H; clear H; subst;
    auto
  | [H : closed_type _ _ |- _] =>
    inversion H; clear H; subst;
    auto using closed_ctx_map_S, closed_type_subst
  end.
Qed.

Lemma typed_closed_ctx (k : nat) (Γ : list type) (e : expr) (τ : type) :
  typed k Γ e τ → closed_ctx k Γ.
Proof. apply typed_closed_ctx_closed_type. Qed.

Lemma typed_closed_type (k : nat) (Γ : list type) (e : expr) (τ : type) :
  typed k Γ e τ → closed_type k τ.
Proof. apply typed_closed_ctx_closed_type. Qed.

Local Hint Extern 1 =>
match goal with [H : context [length (map _ _)] |- _] => rewrite map_length in H end
: typed_subst_invariant.

Lemma typed_subst_invariant k Γ e τ s1 s2 :
  typed k Γ e τ → (∀ x, x < length Γ → s1 x = s2 x) → e.[s1] = e.[s2].
Proof.
  intros Htyped; revert s1 s2.
  assert (∀ {A} `{Ids A} `{Rename A}
            (s1 s2 : nat → A) x, (x ≠ 0 → s1 (pred x) = s2 (pred x)) → up s1 x = up s2 x).
  { intros A H1 H2. rewrite /up=> s1 s2 [|x] //=; auto with f_equal omega. }
  induction Htyped => s1 s2 Hs; f_equal/=; eauto using lookup_lt_Some with omega typed_subst_invariant.
Qed.
    
Import uPred.

(** interp : is a unary logical relation. *)
Section typed_interp.
  Context {Σ : iFunctor}.
  Implicit Types P Q R : iProp lang Σ.
  Notation "# v" := (of_val v) (at level 20).
  Notation "⊤" := coPset_top.

  Canonical Structure leibniz_val := leibnizC val.

  Canonical Structure leibniz_le n m := leibnizC (n ≤ m).
  
  Class Val_to_IProp_AlwaysStable (f : leibniz_val -n> iProp lang Σ) :=
    val_to_iprop_always_stable : ∀ v : val, AlwaysStable ((cofe_mor_car _ _ f) v).

  Arguments val_to_iprop_always_stable /.
  
  
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
      cofe_mor_car := λ w, (□ ∀ v, ▷ τ1i v → #> (App (# w) (# v)) @ ⊤ {{τ2i}})%I
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
        ∀ (τ'i : {f : (leibniz_val -n> iProp lang Σ) | Val_to_IProp_AlwaysStable f}),
            □ (▷ #> e @ ⊤ {{λ v, (τi (`τ'i) v)}}))%I
    |}.

  Instance interp_forall_proper : Proper ((≡) ==> (≡)) interp_forall.
  Proof.
    intros τ τ' H1 v; cbn.
    apply exist_proper => e; apply and_proper; auto.
    apply forall_proper => τ'i.
    apply always_proper, later_proper, wp_proper =>v'.
    rewrite H1; trivial.
  Qed.
    
  Instance interp_forall_ne n : Proper (dist n ==> dist n) interp_forall.
  Proof.
    intros τ τ' H1 v; cbn.
    apply exist_ne => e; apply and_ne; auto.
    apply forall_ne => τ'i.
    apply always_ne, later_contractive =>i Hi.
    apply wp_ne=>w. eapply dist_le.
    rewrite H1; trivial. auto with omega.
  Qed.

  Definition interp_rec_pre
             (τi : (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ))
             (rec_apr : (leibniz_val -n> iProp lang Σ))
    : (leibniz_val -n> iProp lang Σ) :=
    {|
      cofe_mor_car := λ w, (□ (∃ e, w = FoldV e ∧ ▷ #> e @ ⊤ {{ λ v, τi rec_apr v}}))%I
    |}.

  Instance interp_rec_pre_proper : Proper ((≡) ==> (≡) ==> (≡)) interp_rec_pre.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_proper; apply exist_proper=>e; apply and_proper; trivial.
    apply later_proper, wp_proper=>v.
    rewrite H1 H2; trivial.
  Qed.
  
  Instance interp_rec_pre_ne n : Proper (dist n ==> dist n ==> dist n) interp_rec_pre.
  Proof.
    intros τ1 τ1' H1 τ2 τ2' H2 w.
    apply always_ne; apply exist_ne=>e; apply and_ne; trivial.
    apply later_contractive =>i Hi.
    apply wp_ne=>v.
    eapply dist_le.
    rewrite H1 H2; trivial.
    auto with omega.
  Qed.
  
  Instance interp_rec_pre_contr
           (τi : (leibniz_val -n> iProp lang Σ) -n> (leibniz_val -n> iProp lang Σ))
    :
      Contractive (interp_rec_pre τi).
  Proof.
    intros n f g H w; cbn.
    apply always_ne;apply exist_ne; intros e; apply and_ne; trivial.
    apply later_contractive =>i Hi.
    apply wp_ne; intros v; rewrite H; trivial.
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

  Lemma interp_closed_irrel
        (k : nat) (τ : type) (HC HC': closed_type k τ)
        (Δ : Vlist (leibniz_val -n> iProp lang Σ) k)
        (v : val)
    : interp k τ HC Δ v ≡ interp k τ HC' Δ v.
  Proof.
    revert k HC HC' Δ v.
    induction τ; intros k HC HC' Δ v; cbn;
    let rec tac :=
        match goal with
        | _ => progress repeat let w := fresh "w" in apply exist_proper => w; tac
        | _ => progress repeat apply and_proper; tac
        | _ => progress repeat apply or_proper; tac
        | _ => progress repeat apply later_proper; tac
        | _ => progress repeat let w := fresh "w" in apply forall_proper => w; tac
        | _ => progress repeat apply always_proper; tac
        | _ => progress repeat apply impl_proper; tac
        | _ => progress repeat apply wp_proper; try intros ?; tac
        | _ => unfold interp_rec; rewrite fixpoint_proper; eauto;
              intros ? ?; unfold interp_rec_pre; cbn; tac
        | _ => auto
        end
    in tac.
    - unfold force_lookup.
      match goal with
        [|- _ (match ?A with |Some _ => _ |None => _ end ?B) _ ≡ _ (match ?A with |Some _ => _ |None => _ end ?C) _] => 
        generalize B; generalize C; destruct A; auto;
        let H := fresh "H" in intros H; inversion H; congruence
      end.
  Qed.
    
  Definition env_subst (vs : list val) (x : var) : expr :=
    from_option (Var x) (of_val <$> vs !! x).
  
  Lemma typed_subst_head_simpl k Δ τ e w ws :
    typed k Δ e τ -> length Δ = S (length ws) →
    e.[# w .: env_subst ws] = e.[env_subst (w :: ws)]
  .
  Proof.
    intros H1 H2.
    rewrite /env_subst. eapply typed_subst_invariant; eauto=> /= -[|x] ? //=.
    destruct (lookup_lt_is_Some_2 ws x) as [v' Hv]; first omega; simpl.
      by rewrite Hv.
  Qed.

  Class VlistAlwaysStable {k} (Δ : Vlist (leibniz_val -n> iProp lang Σ) k) :=
    vlistalwaysstable : Forall Val_to_IProp_AlwaysStable (` Δ).

  Instance Val_to_IProp_AlwaysStable_Always_Stable
           (f : leibniz_val -n> iProp lang Σ)
           {Hf : Val_to_IProp_AlwaysStable f}
           (v : val)
    : AlwaysStable (f v).
  Proof. apply Hf. Qed.
    
  Instance interp_always_stable
           k τ H (Δ : Vlist (leibniz_val -n> iProp lang Σ) k)
           {HΔ : VlistAlwaysStable Δ}
    : Val_to_IProp_AlwaysStable (interp k τ H Δ).
  Proof.
    induction τ; cbn; intros v; try apply _.
  - rewrite /interp_rec /AlwaysStable fixpoint_unfold /interp_rec_pre.
    apply always_intro'; trivial.
  - apply (@force_lookup_Forall
             _ _
             (λ f : leibniz_val -n> iProp lang Σ, AlwaysStable (f v))).
    apply Forall_forall => f H1.
    eapply Forall_forall in HΔ; [apply HΔ|trivial].
  Qed.

  Instance alwyas_stable_Δ k Δ Γ vs
           (Hctx : closed_ctx k Γ)
           {HΔ : VlistAlwaysStable Δ}
    : AlwaysStable (Π∧ zip_with (λ τ v, interp k (` τ) (proj2_sig τ) Δ v) (closed_ctx_list _ Γ Hctx) vs)%I.
  Proof. typeclasses eauto. Qed.

  Instance alwyas_stable_Vlist_cons k f Δ
           (Hf : Val_to_IProp_AlwaysStable f)
           {HΔ : VlistAlwaysStable Δ}
    : VlistAlwaysStable (@Vlist_cons _ k f Δ).
  Proof. constructor; auto. Qed.

  Lemma type_context_closed_irrel
        (k : nat) (Δ : Vlist (leibniz_val -n> iProp lang Σ) k) (Γ : list type)
        (vs : list leibniz_val)
        (Hctx Hctx' : closed_ctx k Γ) :
    (Π∧ zip_with
          (λ (τ : {τ : type | closed_type k τ}) (v0 : leibniz_val),
           ((interp k (` τ) (proj2_sig τ)) Δ) v0)
          (closed_ctx_list k Γ Hctx)
          vs)%I
      ≡
      (Π∧ zip_with
           (λ (τ : {τ : type | closed_type k τ}) (v : leibniz_val),
            ((interp k (` τ) (proj2_sig τ)) Δ) v)
           (closed_ctx_list k Γ Hctx')
           vs)%I.
  Proof.
    revert vs.
    induction Γ; cbn; auto.
    destruct vs; cbn; auto.
    apply and_proper.
    - apply interp_closed_irrel.
    - apply IHΓ.
  Qed.    

  Ltac ipropsimpl :=
    repeat
      match goal with
      | [|- (_ ⊑ (_ ∧ _))%I] => eapply and_intro
      | [|- (▷ _ ⊑ ▷ _)%I] => apply later_mono
      | [|- (_ ⊑ ∃ _, _)%I] => rewrite -exist_intro
      | [|- ((∃ _, _) ⊑ _)%I] => let v := fresh "v" in rewrite exist_elim; [|intros v]
      end.

  Local Hint Extern 1 => progress ipropsimpl.

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) uconstr(t) ident(v) :=
    rewrite -(@wp_bind _ _ _ [ctx]) /= -wp_impl_l; apply and_intro; [
    apply (@always_intro _ _ _ t), forall_intro=> v /=; apply impl_intro_l| eauto with itauto].

  Local Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) :=
    rewrite -(@wp_bind _ _ _ [ctx]) /= -wp_mono; eauto; intros v; cbn.

  Create HintDb itauto.

  Local Hint Extern 3 ((_ ∧ _) ⊑ _)%I => rewrite and_elim_r : itauto.
  Local Hint Extern 3 ((_ ∧ _) ⊑ _)%I => rewrite and_elim_l : itauto.
  Local Hint Extern 3 (_ ⊑ (_ ∨ _))%I => rewrite -or_intro_l : itauto.
  Local Hint Extern 3 (_ ⊑ (_ ∨ _))%I => rewrite -or_intro_r : itauto.
  Local Hint Extern 2 (_ ⊑ ▷ _)%I => etransitivity; [|rewrite -later_intro] : itauto.
  
  Local Ltac value_case := rewrite -wp_value/= ?to_of_val //; auto 2.


  Lemma interp_subst_weaken
        (k m n : nat)
        (Δ : Vlist (leibniz_val -n> iProp lang Σ) k)
        (Ξ : Vlist (leibniz_val -n> iProp lang Σ) m)
        (ξ : Vlist (leibniz_val -n> iProp lang Σ) n)
        (τ : type)
        (HC : closed_type (m + k) τ)
        (HC' : closed_type (m + (n + k)) τ.[iter m up (ren (+n))])
    : interp (m + k) τ HC (Vlist_app Ξ Δ)
             ≡ interp (m + (n + k))
             τ.[iter m up (ren (+n))] HC' (Vlist_app Ξ (Vlist_app ξ Δ)).
  Proof.
    revert k m n Δ Ξ ξ HC HC'.
    induction τ; intros k m n Δ Ξ ξ HC HC' w; cbn; auto.
    - apply exist_proper =>w1; apply exist_proper =>w2;
        repeat apply and_proper; try apply later_proper;
        solve [trivial|apply IHτ1|apply IHτ2].
    - apply or_proper; apply exist_proper =>w1;
        repeat apply and_proper; try apply later_proper;
        solve [trivial|apply IHτ1|apply IHτ2].
    - apply always_proper, forall_proper => w1;
        apply impl_proper; try apply later_proper; try apply wp_proper;
        solve [apply IHτ1|apply IHτ2].
    - apply interp_rec_proper =>f; cbn.
      change (S (m + k)) with (S m + k).
      change (S (m + (n + k))) with (S m + (n + k)).
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      rewrite !Vlist_app_cons.
      apply IHτ.
    - asimpl in *.          
      revert HC'; rewrite iter_up; intros HC'.
      destruct lt_dec; asimpl; unfold ids, Ids_type; cbn.
      + rewrite !force_lookup_l; trivial.
      + inversion HC'; subst.
        rewrite force_lookup_r; try lia; intros Hlt.
        rewrite force_lookup_r; try lia; intros Hlt'.
        rewrite force_lookup_r; try lia; intros Hlt''.
        revert Hlt''.
        match goal with
          [|- ∀ _, _ (force_lookup _ ?A _) _ ≡ _ (force_lookup _ ?B _) _] =>
          replace B with A by lia; intros Hlt''
        end.
        rewrite force_lookup_proper; eauto.
    - apply exist_proper =>w1; apply and_proper; auto.
      apply forall_proper; intros [f Hf].
      apply always_proper, later_proper, wp_proper => w2.
      cbn.
      change (S (m + k)) with (S m + k).
      change (S (m + (n + k))) with (S m + (n + k)).
      change (up (iter m up (ren (+n)))) with (iter (S m) up (ren (+n))).
      rewrite !Vlist_app_cons.
      apply IHτ.
  Qed.

  Lemma interp_ren_S (k : nat) (τ : type)
        (Δ : Vlist (leibniz_val -n> iProp lang Σ) k)
        (τi : leibniz_val -n> iProp lang Σ)
        (HC : closed_type k τ) (HC' : closed_type (S k) τ.[ren (+1)])
        (v : leibniz_val)
    : interp k τ HC Δ v ≡ interp (S k) τ.[ren (+1)] HC' (Vlist_cons τi Δ) v.
  Proof.
    rewrite -(Vlist_nil_app Δ).
    rewrite (Vlist_app_cons τi Vlist_nil Δ).
    rewrite -(Vlist_nil_app (Vlist_app (Vlist_cons τi Vlist_nil) Δ)).
    apply (interp_subst_weaken k 0 1).
  Qed.

  Lemma interp_subst_iter_up
        (k m : nat)
        (Δ : Vlist (leibniz_val -n> iProp lang Σ) k)
        (Ξ : Vlist (leibniz_val -n> iProp lang Σ) m)
        (τ : type)
        (τ' : type) (HC' : closed_type k τ')
        (HC : closed_type (m + S k) τ)
        (HC'' : closed_type (m + k) τ.[iter m up (τ' .: ids)])
    : interp (m + S k) τ HC (Vlist_app Ξ (Vlist_cons (interp k τ' HC' Δ) Δ))
             ≡ interp (m + k) τ.[iter m up (τ' .: ids)] HC'' (Vlist_app Ξ Δ).
  Proof.
    revert k m Δ Ξ τ' HC' HC HC''.
    induction τ; intros k m Δ Ξ τ' HC' HC HC'' w; cbn; auto.
    - apply exist_proper =>w1; apply exist_proper =>w2;
        repeat apply and_proper; try apply later_proper;
        solve [trivial|apply IHτ1|apply IHτ2].
    - apply or_proper; apply exist_proper =>w1;
        repeat apply and_proper; try apply later_proper;
        solve [trivial|apply IHτ1|apply IHτ2].
    - apply always_proper, forall_proper => w1;
        apply impl_proper; try apply later_proper; try apply wp_proper;
        solve [apply IHτ1|apply IHτ2].
    - apply interp_rec_proper =>f; cbn.
      change (S (m + S k)) with (S m + S k).
      change (S (m + k)) with (S m + k).
      change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids)).
      rewrite !Vlist_app_cons.
      apply IHτ.
    - asimpl in *.
      revert HC''; rewrite iter_up; intros HC''.
      destruct lt_dec.
      + unfold ids, Ids_type; cbn.
        rewrite !force_lookup_l; trivial.
      + remember (x - m) as u.
        destruct (nat_eq_dec x m); try lia.
        * revert HC''; replace u with 0 by lia; asimpl; intros HC''.
          rewrite force_lookup_r; try lia; rewrite -Hequ; intros HC3.
          destruct u; try lia; cbn.
          rewrite -(Vlist_nil_app (Vlist_app Ξ Δ)).
          rewrite -(interp_subst_weaken _ 0 m).
          rewrite Vlist_nil_app; trivial.
        * destruct u; try lia; destruct x; try lia.
          revert HC''; asimpl; intros HC''; inversion HC''.
          unfold ids, Ids_type; cbn.
          rewrite !force_lookup_r; try lia; rewrite -Hequ; intros HC3 HC4.
          rewrite force_lookup_Vlist_cons; try lia; intros HC5.
          revert HC3.
          match goal with
            [|- ∀ _, _ (force_lookup _ ?A _) _ ≡ _ (force_lookup _ ?B _) _] =>
            replace B with A by lia; intros HC3
          end.
          rewrite force_lookup_proper; eauto.
    - apply exist_proper =>w1; apply and_proper; auto.
      apply forall_proper; intros [f Hf].
      apply always_proper, later_proper, wp_proper => w2.
      cbn.
      change (S (m + S k)) with (S m + S k).
      change (S (m + k)) with (S m + k).
      change (up (iter m up (τ' .: ids))) with (iter (S m) up (τ' .: ids)).
      rewrite !Vlist_app_cons.
      apply IHτ.
  Qed.

  Lemma interp_subst
    (k : nat)
    (Δ : Vlist (leibniz_val -n> iProp lang Σ) k)
    (τ : type)
    (τ' : type) (HC' : closed_type k τ')
    (HC : closed_type (S k) τ)
    (HC'' : closed_type k τ.[τ'/])
    : interp (S k) τ HC (Vlist_cons (interp k τ' HC' Δ) Δ)
             ≡ interp k τ.[τ'/] HC'' Δ.
  Proof.
    rewrite <- (Vlist_nil_app Δ) at 3.
    rewrite <- (Vlist_nil_app (Vlist_cons ((interp k τ' HC') Δ) Δ)).
    apply (interp_subst_iter_up k 0 Δ Vlist_nil τ τ' HC' HC HC'').
  Qed.

  Lemma zip_with_closed_ctx_list_subst
        (k : nat) (Δ : Vlist (leibniz_val -n> iProp lang Σ) k) (Γ : list type) 
        (Hctx : closed_ctx k Γ)
        (Hctx' : closed_ctx (S k) (map (λ t : type, t.[ren (+1)]) Γ))
        (vs : list leibniz_val) (τi : leibniz_val -n> iProp lang Σ)
    : ((Π∧ zip_with
             (λ (τ : {τ : type | closed_type k τ}) (v : leibniz_val),
              ((interp k (` τ) (proj2_sig τ)) Δ) v)
             (closed_ctx_list k Γ Hctx) vs)%I)
        ≡ (Π∧ zip_with
                (λ (τ : {τ : type | closed_type (S k) τ}) (v : leibniz_val),
                 ((interp (S k) (` τ) (proj2_sig τ)) (Vlist_cons τi Δ)) v)
                (closed_ctx_list (S k) (map (λ t : type, t.[ren (+1)]) Γ) Hctx') vs)%I.
  Proof.
    revert k Δ Hctx Hctx' vs τi.
    induction Γ as [|τ Γ]; intros k Δ Hctx Hctx' vs τi; cbn; trivial.
    destruct vs; cbn; trivial.
    apply and_proper.
    - apply interp_ren_S.
    - apply IHΓ.
  Qed.
  
  Lemma typed_interp k Δ Γ vs e τ
        (Htyped : typed k Γ e τ)
        (Hctx : closed_ctx k Γ)
        (HC : closed_type k τ)
        (HΔ : VlistAlwaysStable Δ)
    : length Γ = length vs →
      Π∧ zip_with (λ τ v, interp k (` τ) (proj2_sig τ) Δ v) (closed_ctx_list _ Γ Hctx) vs ⊑
                  #> (e.[env_subst vs]) @ ⊤ {{ λ v, interp k τ HC Δ v }}.
  Proof.
    revert Hctx HC HΔ vs.
    induction Htyped; intros Hctx HC HΔ vs Hlen; cbn.
    - (* var *)
      destruct (lookup_lt_is_Some_2 vs x) as [v Hv].
      { by rewrite -Hlen; apply lookup_lt_Some with τ. }
      rewrite /env_subst Hv /= -wp_value; eauto using to_of_val.
      edestruct (zipwith_Forall_lookup _ Hctx) as [Hτ' Hτ'eq]; eauto.
      etransitivity.
      apply big_and_elem_of, elem_of_list_lookup_2 with x.
      rewrite lookup_zip_with; simplify_option_eq; trivial.
      rewrite interp_closed_irrel; trivial.
    - (* unit *) value_case.
    - (* pair *)
      smart_wp_bind (PairLCtx e2.[env_subst vs]) _ v; eauto.
      (* weird!: and_alwaysstable is an instance but is not resolved! *)
      smart_wp_bind (PairRCtx v) (and_always_stable _ _ _ _) v'.
      value_case; eauto 10 with itauto.
    - (* fst *)
      smart_wp_bind (FstCtx) v. ipropsimpl; eauto.
      apply const_elim_l; intros H; rewrite H.
      rewrite -wp_fst; eauto using to_of_val, and_elim_l.
      rewrite and_elim_l; rewrite interp_closed_irrel; eauto.
    - (* snd *)
      smart_wp_bind SndCtx v. ipropsimpl; eauto.
      apply const_elim_l; intros H; rewrite H.
      rewrite -wp_snd; eauto using to_of_val, and_elim_l.
      rewrite and_elim_r; rewrite interp_closed_irrel; eauto.
    - (* injl *) smart_wp_bind InjLCtx v; value_case; eauto 7 with itauto.
    - (* injr *) smart_wp_bind InjRCtx v; value_case; eauto 7 with itauto.
    - (* case *)
      smart_wp_bind (CaseCtx _ _) _ v. cbn.
      rewrite (later_intro (Π∧ zip_with
           (λ (τ : {τ : type | closed_type k τ}) (v0 : leibniz_val),
            ((interp k (` τ) (proj2_sig τ)) Δ) v0) (closed_ctx_list k Γ Hctx) vs));
        rewrite or_elim; [apply impl_elim_l| |].
      + rewrite exist_elim; eauto; intros v'.
        apply const_elim_l; intros H; rewrite H.
        rewrite -impl_intro_r // -later_and later_mono; eauto.
        rewrite -wp_case_inl; eauto using to_of_val.
        asimpl.
        specialize (IHHtyped2 Δ (typed_closed_ctx _ _ _ _ Htyped2) HC HΔ (v'::vs)).
        erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto).
        rewrite -IHHtyped2; cbn; auto.
        rewrite interp_closed_irrel type_context_closed_irrel /closed_ctx_list.
        apply later_mono, and_intro; eauto 3 with itauto.
      + rewrite exist_elim; eauto; intros v'.
        apply const_elim_l; intros H; rewrite H.
        rewrite -impl_intro_r // -later_and later_mono; eauto.
        rewrite -wp_case_inr; eauto using to_of_val.
        asimpl.
        specialize (IHHtyped3 Δ (typed_closed_ctx _ _ _ _ Htyped3) HC HΔ (v'::vs)).
        erewrite <- ?typed_subst_head_simpl in * by (cbn; eauto).
        rewrite -IHHtyped3; cbn; auto.
        rewrite interp_closed_irrel type_context_closed_irrel /closed_ctx_list.
        apply later_mono, and_intro; eauto 3 with itauto.    
    - (* lam *)
      value_case; apply (always_intro _ _), forall_intro=> v /=; apply impl_intro_l.
      rewrite -wp_lam ?to_of_val //=.
      asimpl. erewrite typed_subst_head_simpl; [|eauto|cbn]; eauto.
      rewrite (later_intro (Π∧ _)) -later_and; apply later_mono.
      rewrite interp_closed_irrel type_context_closed_irrel /closed_ctx_list.
      rewrite -(IHHtyped Δ (typed_closed_ctx _ _ _ _ Htyped) (closed_type_arrow_2 HC) HΔ (v :: vs));
        simpl; auto with f_equal.
    - (* app *)
      smart_wp_bind (AppLCtx (e2.[env_subst vs])) _ v.
      rewrite -(@wp_bind _ _ _ [AppRCtx v]) /=.
      rewrite -wp_impl_l /=; apply and_intro.
      2: etransitivity; [|apply IHHtyped2]; eauto using and_elim_r.
      rewrite and_elim_l. apply always_mono.
      apply forall_intro =>v'.
      rewrite forall_elim.
      apply impl_intro_l.
      rewrite -(later_intro).
      etransitivity; [apply impl_elim_r|].
      apply wp_mono => w.
      rewrite interp_closed_irrel; trivial.
    - (* TLam *)
      value_case; rewrite -exist_intro; apply and_intro; auto.
      apply forall_intro =>τi;
        apply (always_intro _ _).
      rewrite map_length in IHHtyped.
      destruct τi as [τi τiAS].
      specialize (IHHtyped
                    (Vlist_cons τi Δ)
                    (closed_ctx_map
                       _ _ _ _
                       Hctx (λ τ, closed_type_S_ren2 τ 1 0 _))
                    (closed_type_forall HC)
                    (alwyas_stable_Vlist_cons _ _ _ τiAS)
                    _
                    Hlen
                 ).
      rewrite -wp_impl_l -later_intro. apply and_intro;
        [ apply (always_intro _ _), forall_intro=> v /=; apply impl_intro_l|].
      2: etransitivity; [|apply IHHtyped].
      + rewrite and_elim_l; trivial.
      + rewrite zip_with_closed_ctx_list_subst; trivial.
    - (* TApp *)
      smart_wp_bind TAppCtx _ v; cbn.
      rewrite and_elim_l.
      rewrite exist_elim; eauto => e'.
      apply const_elim_l; intros H'; rewrite H'.
      rewrite (forall_elim ((interp k τ' H Δ) ↾ _)).
      rewrite always_elim.
      rewrite -wp_TLam; apply later_mono.
      apply wp_mono=> w.
      rewrite interp_subst; trivial.
    - (* Fold *)
      value_case. unfold interp_rec.
      rewrite fixpoint_unfold.
      cbn.
      rewrite -exist_intro.
      apply (always_intro _ _).
      apply and_intro; auto.
      rewrite map_length in IHHtyped.
      specialize (IHHtyped
                    (Vlist_cons (interp k (TRec τ) HC Δ) Δ)
                    (closed_ctx_map
                       _ _ _ _
                       Hctx (λ τ, closed_type_S_ren2 τ 1 0 _))
                    (closed_type_rec HC)
                    (alwyas_stable_Vlist_cons _ _ _ _)
                   _
                    Hlen
                 ).      
      rewrite -wp_impl_l -later_intro. apply and_intro;
        [ apply (always_intro _ _), forall_intro=> v /=; apply impl_intro_l|].
      2: etransitivity; [|apply IHHtyped].
      + rewrite and_elim_l; trivial.
      + rewrite zip_with_closed_ctx_list_subst; trivial.
    - (* Unfold *)
      smart_wp_bind UnfoldCtx _ v; cbn.
      rewrite and_elim_l.
      unfold interp_rec. rewrite fixpoint_unfold /interp_rec_pre; cbn.
      replace (fixpoint
                 (λ rec_apr : leibniz_val -n> iProp lang Σ,
                              CofeMor
                                (λ w : leibniz_val,
                                       □ (∃ e1 : expr,
                                             w = FoldV e1
                                             ∧ ▷ #> e1 @ ⊤ {{ λ v1 : val,
                                                        ((interp (S k) τ (closed_type_rec ?HC4))
                                                           (Vlist_cons rec_apr Δ)) v1 }}))%I))
      with
      (interp k (TRec τ) (typed_closed_type _ _ _ _ Htyped) Δ) by (cbn; unfold interp_rec; trivial).
      rewrite always_elim.
      rewrite exist_elim; eauto => e'.
      apply const_elim_l; intros H'; rewrite H'.
      rewrite -wp_Fold.
      apply later_mono, wp_mono => w.
      rewrite -interp_subst; eauto.
      (* unshelving *)
      Unshelve.
      all: solve [eauto 2 using typed_closed_type | try typeclasses eauto].
  Qed.
  
End typed_interp.