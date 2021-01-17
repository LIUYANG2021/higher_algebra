Require Export H1_2.

Set Implicit Arguments.

(* 1.3 数学归纳法 *)
Module H13.

Definition Φn := Φ nat.
Theorem Not_Empty: forall x, x ∉ Φn.
Proof.
  intros. unfold NotIn; intro.
  apply -> AxiomII in H; simpl in H; destruct H; auto.
Qed.

Definition N : Ensemble nat := \{λ n, n = n \}.

(* 最小数原理 *)
Axiom MiniMember : forall (X: Ensemble nat),
  X ≠ Φn -> X ⊂ N -> exists a, a ∈ X /\ (forall c, c ∈ X -> a <= c).

(* 数学归纳法 *)
Definition En_S (P: nat -> Prop) := \{ λ x: nat, ~ (P x) \}.

Theorem Mathematical_Induction : forall(P: nat -> Prop)(n: nat),
  P 0 -> (Ɐ k, P k -> P(S k)) -> (Ɐ n, P n).
Proof.
  intros.
  generalize(classic ((En_S P) = Φn)); intros; destruct H1.
  - generalize(classic (P n0)); intros; destruct H2; auto.
    assert(n0 ∈ (En_S P)). { apply AxiomII; auto. }
    rewrite H1 in H3. generalize(Not_Empty H3); contradiction.
  - apply MiniMember in H1.
    + destruct H1 as [h [H1 H2]]. double H1.
      apply -> AxiomII in H1; simpl in H1.
      assert(h ≠ 0). { intro. rewrite H4 in H1; contradiction. }
      assert ( (pred h) ∉ (En_S P) ).
      { assert (0 < h).
        { generalize (Gt.gt_0_eq h). intros. destruct H5; auto.
          symmetry in H5; contradiction. }
        apply Lt.lt_pred_n_n in H5. intro. eapply H2 in H6.
        apply Lt.le_not_lt in H6. contradiction. }
      assert ( P (pred h)).
      { apply NNPP. intro. apply H5. apply AxiomII. auto. }
      apply H0 in H6. apply PeanoNat.Nat.succ_pred in H4. rewrite H4 in H6.
      contradiction.
    + unfold Included; intros. apply -> AxiomII in H2; simpl in H2.
      apply AxiomII; auto.
Qed.

Theorem The_Second_Mathematical_Induction : forall (P: nat -> Prop),
  P 0 -> (Ɐ k, (Ɐ m, m < k -> P m) -> P k) -> (Ɐ n, P n).
Proof.
  intros.
  generalize(classic ((En_S P) = Φn)); intros; destruct H1.
  - generalize(classic (P n)); intros; destruct H2; auto.
    assert(n ∈ (En_S P)). { apply AxiomII; auto. }
    rewrite H1 in H3. generalize(Not_Empty H3); contradiction.
  - apply MiniMember in H1.
    + destruct H1 as [h [H1 H2]]. double H1.
      apply -> AxiomII in H1; simpl in H1.
      assert(Ɐ m, m < h -> P m).
      { intros. apply NNPP. intro.
        assert ( m ∉ (En_S P) ).
        { assert(m ≠ 0). { intro. rewrite H6 in H5; contradiction. }
          assert(0 < m). { generalize (Gt.gt_0_eq m). intros.
          destruct H7; auto. symmetry in H7. contradiction. }
          apply Lt.lt_pred_n_n in H7. intro. eapply H2 in H8.
          apply Lt.le_not_lt in H8. contradiction. }
        apply H6. apply AxiomII. auto. }
      apply H0 in H4. contradiction.
    + unfold Included; intros; apply AxiomII; auto.
Qed.

End H13.
Export H13.






















