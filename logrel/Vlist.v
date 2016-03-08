Require Import algebra.cofe prelude.prelude.
Set Universe Polymorphism.

Lemma Forall2_inside_forall {A B C} (x : C) (P : C → A → B → Prop) (l : list A) (l' : list B) :
  (∀ (x : C), Forall2 (P x) l l') → Forall2 (λ a b, ∀ x, P x a b) l l'.
Proof.
  revert l'.
  induction l; intros l' H.
  - specialize (H x); inversion H; subst; auto.
  - destruct l'; [specialize (H x); inversion H|].
    constructor; [|apply IHl]; intros z; specialize (H z); inversion H; trivial.
Qed.

Definition Vlist (A : Type) (n : nat) := {l : list A| length l = n}.

Program Definition force_lookup {A : Type} {n : nat} (v : Vlist A n) (i : nat) (Hlt :  i < n) : A :=
  match (v : list _) !! i as u return is_Some u → A with
  | None => fun H => False_rect _ (is_Some_None H)
  | Some x => fun _ => x
  end _.
Next Obligation.
Proof.
  intros A n v i Hlt.
  apply lookup_lt_is_Some_2.
  destruct v; subst; trivial.
Qed.

Theorem force_lookup_Forall {A : Type} {n : nat} {P : A → Prop}
        (v : Vlist A n) `{Forall P (`v)}
        (i : nat) (Hlt :  i < n) :
  P (force_lookup v i Hlt).
Proof.
  destruct v as [l Hv]; unfold force_lookup; cbn in *.
  eapply Forall_forall; eauto.
  match goal with
    [|- (match ?A with |Some _ => _ |None => _ end ?B) ∈ _] =>
    generalize B; cbn; intros [x H]
  end.
  apply elem_of_list_lookup_2 with i.
  match goal with
    [|- _ = _ (match ?A with |Some _ => _ |None => _ end ?B)] =>
    destruct A; [trivial|inversion H]
  end.
Qed.  

Lemma length_shrink {A n x} {l : list A} : length (x :: l) = S n → length l = n.
Proof. cbn; congruence. Qed.

Program Definition Vlist_nil {A : Type} : Vlist A 0 := ([] ↾ Logic.eq_refl).
  
Program Definition Vlist_cons {A n} (x : A) (v : Vlist A n) : Vlist A (S n) :=
  ((x :: `v) ↾ _).
Next Obligation.
Proof.
  intros A n x [l Hv]; cbn; auto.
Qed.

Program Definition Vlist_app {A n m} (v : Vlist A n) (v' : Vlist A m) : Vlist A (n + m) :=
  ((`v ++ `v') ↾ _).
Next Obligation.
Proof.
  intros A n m [l Hl] [l' Hl']; cbn.
  rewrite app_length; rewrite Hl Hl'; trivial.
Qed.

Lemma force_lookup_l
      {A : Type} {m n : nat} (v : Vlist A m) (v' : Vlist A n)
      (i : nat) (Hlt :  i < m + n) (Hlt' : i < m)
  : force_lookup (Vlist_app v v') i Hlt = force_lookup v i Hlt'.
Proof.
  destruct v as [l Hl]; destruct v' as [l' Hl']; unfold force_lookup; cbn in *.
  match goal with
    [|- match ?A with |Some _ => _ |None => _ end ?B =
       match ?C with |Some _ => _ |None => _ end ?D] =>
    generalize B; generalize D; cbn
  end.
  rewrite lookup_app_l; auto with omega.
  intros HB HC.
  match goal with
    [|- match ?A with |Some _ => _ |None => _ end ?B =
       match ?A with |Some _ => _ |None => _ end ?D] =>
    destruct A; trivial; inversion HB; congruence
  end.
Qed.

Lemma force_lookup_r
      {A : Type} {m n : nat} (v : Vlist A m) (v' : Vlist A n)
      (i : nat) (Hlt :  i < m + n) (Hge : i ≥ m) (Hlt' : (i - m) < n)
  : force_lookup (Vlist_app v v') i Hlt = force_lookup v' (i - m) Hlt'.
Proof.
  destruct v as [l Hl]; destruct v' as [l' Hl']; unfold force_lookup; cbn in *.
  match goal with
    [|- match ?A with |Some _ => _ |None => _ end ?B =
       match ?C with |Some _ => _ |None => _ end ?D] =>
    generalize B; generalize D; cbn
  end.
  rewrite lookup_app_r; auto with omega.
  rewrite Hl.
  intros HB HC.
  match goal with
    [|- match ?A with |Some _ => _ |None => _ end ?B =
       match ?A with |Some _ => _ |None => _ end ?D] =>
    destruct A; trivial; inversion HB; congruence
  end.
Qed.

Lemma force_lookup_Vlist_cons
      {A : Type} {n : nat} (x : A) (v : Vlist A n)
      (i : nat) (Hlt :  S i < (S n)) (Hlt' : i < n)
  : force_lookup (Vlist_cons x v) (S i) Hlt = force_lookup v i Hlt'.
Proof.
  destruct v as [l Hl]; unfold force_lookup; cbn in *.
  match goal with
    [|- match ?A with |Some _ => _ |None => _ end ?B =
       match ?C with |Some _ => _ |None => _ end ?D] =>
    generalize B; generalize D; cbn
  end.
  intros HB HC.
  match goal with
    [|- match ?A with |Some _ => _ |None => _ end ?B =
       match ?C with |Some _ => _ |None => _ end ?D] =>
    change C with A in *; destruct A;
    trivial; inversion HB; congruence
  end.
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
  
  Lemma force_lookup_proper {m v v' i H H'} :
    v ≡ v' → (@force_lookup _ m v i H) ≡ (force_lookup v' i H').
  Proof.
    intros H1; unfold dist in H1; unfold Vlist_dist in *.
    destruct v as [l Hv]; destruct v' as [l' Hv']; unfold force_lookup;
    try (try inversion Hv; try inversion Hv'; fail); subst; cbn in *.
    set (H2 := λ x, @Forall2_lookup_l _ _ _ _ _ i x H1); clearbody H2.
    generalize (force_lookup_obligation_1 A (length l) (l ↾ Logic.eq_refl) i H) as H4.
    generalize (force_lookup_obligation_1 A (length l) (l' ↾ Hv') i H') as H3.
    intros [y1 H3] [y2 H4]; cbn in *. destruct (l !! i); [| congruence]. 
    edestruct H2 as [z [H21 H22]]; eauto.
    generalize (ex_intro (λ y : A, l' !! i = Some y) y1 H3) as H5.
    rewrite H21; congruence.
  Qed.
  
  Instance Vlist_head_ne {m n} : Proper (dist n ==> dist n) (@Vlist_head A m).
  Proof.
    intros [v Hv] [v' Hv'] H.
    destruct v; destruct v'; try (try inversion Hv; try inversion Hv'; fail).
    inversion H; trivial.
  Qed.
  
  Instance Vlist_head_proper {m} : Proper ((≡) ==> (≡)) (@Vlist_head A m).
  Proof.
    intros [v Hv] [v' Hv'] H.
    destruct v; destruct v'; try (try inversion Hv; try inversion Hv'; fail).
    inversion H; trivial.
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
    apply Vlist_head_ne, chain_cauchy; trivial.
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

Instance Vlist_cons_proper {A : cofeT} {n : nat} :
  Proper ((≡) ==> (≡) ==> (≡)) (@Vlist_cons A n).
Proof.
  intros x y Hxy x' y' Hx'y'.
  destruct x' as [l Hl]; destruct y' as [l' Hl'].
  unfold equiv, cofe_equiv; cbn; unfold Vlist_equiv; cbn.
  constructor; trivial.
Qed.

Theorem Vlist_app_cons {A : cofeT} {n m} (x : A) (v : Vlist A n) (v' : Vlist A m) :
  Vlist_cons x (Vlist_app v v') ≡ Vlist_app (Vlist_cons x v) v'.
Proof.
  destruct v as [l Hl]; destruct v' as [l' Hl'].
  unfold equiv, cofe_equiv; cbn; unfold Vlist_equiv; cbn.
  rewrite app_comm_cons. apply Reflexive_instance_0; auto.
Qed.

Theorem Vlist_nil_app {A : cofeT} {n} (v : Vlist A n) :
  (Vlist_app Vlist_nil v) ≡ v.
Proof.
  destruct v as [l Hl].
  unfold equiv, cofe_equiv; cbn; unfold Vlist_equiv; cbn.
  apply Reflexive_instance_0; auto.
Qed.

Arguments cofe_Vlist _ _ : clear implicits.

Program Definition force_lookup_morph {A : cofeT} (k : nat) (x : nat) (H : x < k)
  : (cofe_Vlist A k) -n> A :=
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

Program Definition Vlist_cons_apply {A : cofeT} {k}
        (Δ : Vlist A k)
        (f : (cofe_Vlist A (S k)) -n> A)
  : A -n> A :=
  {|
    cofe_mor_car := λ g, f (Vlist_cons_morph g Δ)
  |}.
Next Obligation.
Proof.
  intros A k Δ f n g g' H; rewrite H; trivial.
Qed.

Instance Vlist_cons_apply_proper {A : cofeT} {k} :
  Proper ((≡) ==> (≡) ==> (≡)) (@Vlist_cons_apply A k).
Proof.
  intros τ1 τ1' H1 τ2 τ2' H2 f.
  unfold Vlist_cons_apply.
  cbn -[Vlist_cons_morph].
  apply cofe_mor_car_proper; trivial.
  rewrite H1; trivial.
Qed.

Instance Vlist_cons_apply_ne {A : cofeT} {k} n :
  Proper (dist n ==> dist n ==> dist n) (@Vlist_cons_apply A k).
Proof.
  intros τ1 τ1' H1 τ2 τ2' H2 f.
  unfold Vlist_cons_apply.
  cbn -[Vlist_cons_morph].
  apply cofe_mor_car_ne; trivial.
  rewrite H1; trivial.
Qed.