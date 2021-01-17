Require Export H1_4.
Require Export Reals.

Module Section1_5.

Open Scope R_scope.

(* 数环 *)
Definition Ring (S : Ensemble R) := forall (a b : R),
  S ≠ Φ R -> a ∈ S -> b ∈ S -> 
  ((a+b) ∈ S /\ (a-b) ∈ S /\ (a*b) ∈ S).

(* 数域 *)
Definition Field (F : Ensemble R) := Ring F /\ 
  (exists c, c ≠ 0 /\ c ∈ F) /\ 
  (forall a b, a ∈ F -> b ∈ F -> b ≠ 0 -> (a/b) ∈ F).

(* 实数下的有理数域 *)
Definition Q2R := \{ λ u, exists (c1 c2 : Z), 
  (IZR c2) ≠ 0/\u = (IZR c1)/(IZR c2) \}.

(* 定理1.5.1 *)
Theorem Theorem1_5_1 : forall (F : Ensemble R), Field F -> Q2R ⊂ F.
Proof.
  intros. red in H. destruct H, H0. destruct H0 as [a H0]. destruct H0.
  generalize (H1 a a); intros. apply H3 in H2; auto.
  assert (a / a = 1). { field; auto. } rewrite H4 in H2; clear H4.
  assert (F ≠ Φ R). { intro. rewrite H4 in H2. 
  apply -> AxiomII in H2; simpl in H2. apply H2; auto. } red in H.
  (* 所有的正整数属于F *)
  assert (forall x : Z, (0 <= x)%Z -> (IZR x) ∈ F). {
  apply Z_of_nat_prop. intros. rewrite <- INR_IZR_INZ.
   induction n.
  - simpl. generalize (H 1 1); intros. apply H5 in H4; auto. clear H5.
    destruct H4, H5. assert (1-1 = 0). { field. } rewrite H7 in H5; auto.
  - rewrite S_INR. generalize (H (INR n) 1); intros. apply H5 in H4; auto.
    clear H5. destruct H4, H5. auto. }
  (* 所有的整数属于F *)
  assert (forall x : Z, (IZR x) ∈ F).
  { intros. 
    generalize (classic (0 <= x)%Z); intros; destruct H6.
    - apply H5 in H6; auto.
    - apply Znot_le_gt in H6. assert (0 <= -x)%Z. {
      Z.swap_greater. lia. } apply H5 in H7.
      generalize (H 0 (IZR (- x))); intros. apply H8 in H4; auto.
      + clear H8. destruct H4, H8. rewrite Z_R_minus in H8. simpl in H8.
        assert (- - x = x)%Z. { ring. } rewrite H10 in H8; auto. 
      + generalize (H 1 1); intros. apply H9 in H4; clear H9; auto.
        destruct H4, H9. assert (1-1=0). { field. } rewrite <- H11; auto. }
  red; intros. apply -> AxiomII in H7; simpl in H7. destruct H7, H7.
  assert (IZR x ∈ F /\ IZR x0 ∈ F). { 
  generalize (H6 x); generalize (H6 x0); intros. split; auto. }
  destruct H7. rewrite H9. eapply H1; eauto.
Qed.

End Section1_5.
Export Section1_5.



















