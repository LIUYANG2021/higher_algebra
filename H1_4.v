Require Export H1_3.
Require Export ZArith.


Module H14.
Open Scope Z_scope.

Theorem x_fx : forall (X Y : Type) (f : Ensemble(prod X Y))(x : X),
  Function f-> x ∈ dom[f] -> [x, f[x]] ∈ f.
Proof.
  intros X Y f x H0 H1. apply -> AxiomII in H1; simpl in H1.
  destruct H1 as [y H1].
  apply f_x' in H1 as H2; auto. rewrite H2; auto.
Qed.

(* 整数的一些整除性质 *)

Definition Z_POS : Ensemble Z := \{λ n, n > 0 \}.
Axiom MiniMember_Z' : Ɐ (X: Ensemble Z),
  X ≠ Φ Z /\ X ⊂ Z_POS -> ∃ a, a ∈ X /\ (Ɐ c, c ∈ X -> a <= c).
Definition Z_NotNeg : Ensemble Z := \{λ n, n >= 0 \}.
Axiom MiniMember_Z : Ɐ (X: Ensemble Z),
  X ≠ Φ Z /\ X ⊂ Z_NotNeg -> ∃ a, a ∈ X /\ (Ɐ c, c ∈ X -> a <= c).

Theorem Not_Empty_Z: forall x, x ∉ (Φ Z).
Proof.
  intros. unfold NotIn; intro.
  apply -> AxiomII in H; simpl in H; destruct H; auto.
Qed.

(* 带余除法 *)

Theorem Theorem1_4_1 : forall a b, a ≠ 0 -> 
  (exists q r, b = a * q + r /\ 0 <= r <Z.abs(a)).
Proof.
  intros a b H0.
  assert(H1 : exists S, S=\{λ r, exists x, r = b - a * x /\ r >= 0 \}).
  { exists \{λ r, exists x, r = b - a * x /\ r >= 0 \}. auto. }
  destruct H1 as [S H1].
  assert (S ≠ Φ Z /\ S ⊂ Z_NotNeg).
  { split.
    - intro. generalize (Ztrichotomy a 0); 
      generalize (Ztrichotomy b 0); intros.
      destruct H2 as [H2 | [H2 | H2]]; destruct H3 as [H3 | [H3 | H3]].
      + assert ((b*(1+a)) ∈ S). 
        { rewrite H1. apply AxiomII. exists (-b). split.
          * generalize (Z.mul_opp_opp a b); intros.
            generalize (Z.mul_add_distr_l b 1 a).
            intros. rewrite H5. generalize (Z.mul_comm a b); intros.
            rewrite <- H6. rewrite <- H4.
            generalize (Z.mul_1_r b). intros. rewrite H7.
            generalize (Z.mul_opp_opp a b); intros. rewrite H8.
            generalize (Z.add_opp_r b (a * -b)); intros. rewrite <- H9.
            generalize (Z.mul_opp_l a (-b)); intros. rewrite <- H10.
            rewrite H8. auto.
          * generalize (Zlt_le_succ a 0); intros.
            apply H4 in H3. Z.swap_greater.
            generalize (Z.lt_le_incl b 0); intros. apply H5 in H2.
            generalize (Z.mul_nonpos_nonpos b (1+a)); intros. apply H6; auto.
            generalize (Z.add_1_l a); intros. rewrite H7; auto. }
        rewrite H in H4.
        generalize (Not_Empty_Z (b * (1 + a))); intros. contradiction.
      + contradiction.
      + assert ((b*(1-a)) ∈ S). { rewrite H1. apply AxiomII. exists b. split.
        * generalize (Z.mul_sub_distr_l b 1 a); intros. rewrite H4.
          generalize (Z.mul_1_r b); intros. rewrite H5.
          generalize (Z.mul_comm a b); intros. rewrite H6; auto.
        * Z.swap_greater. generalize (Z.add_comm 1 (-a)); intros.
          generalize (Z.add_opp_r 1 a); intros. rewrite H4 in H5. rewrite <- H5.
          generalize (Z.lt_le_incl b 0); intros. apply H6 in H2.
          generalize (Z.opp_neg_pos a); intros. apply H7 in H3.
          generalize (Zlt_le_succ (-a) 0); intros. apply H8 in  H3.
          generalize (Z.mul_nonpos_nonpos b (- a + 1)); intros. 
          apply H9; auto. }
          generalize (Not_Empty_Z (b * (1 - a))); intros. rewrite H in H4;
          contradiction.
      + assert ((-a) ∈ S). { rewrite H1; apply AxiomII. exists 1. split.
        * generalize (Z.mul_1_r a); intros. rewrite H4. rewrite H2. auto.
        * generalize (Z.lt_le_incl a 0); intros. apply H4 in H3. 
        generalize (Z.opp_nonneg_nonpos a); intros. apply H5 in H3. 
        Z.swap_greater. auto. } generalize (Not_Empty_Z (-a)); intros.
        rewrite H in H4; contradiction.
      + contradiction.
      + assert(a ∈ S). { rewrite H1; apply AxiomII; exists (-1); split.
        * rewrite H2. generalize (Z.add_opp_r 0 (a*-1)); intros. rewrite <- H4.
          simpl. generalize (Zopp_mult_distr_l a (-1)); intros. rewrite H5. 
          generalize (Z.mul_opp_opp a 1); intros. simpl in H6. rewrite H6. 
          generalize (Z.mul_1_r a); intros. rewrite H7; auto.
        * generalize (Z.lt_le_incl 0 a); intros. Z.swap_greater. apply H4 in H3.
          auto. } rewrite H in H4. generalize (Not_Empty_Z a); intros.
          contradiction.
      + assert ((b-a)∈ S). { rewrite H1; apply AxiomII; exists 1; split.
        * generalize (Z.mul_1_r a); intros. rewrite H4; auto.
        * generalize (Z.opp_pos_neg a); intros. apply H4 in H3.
          generalize (Z.add_nonneg_nonneg b (-a)); intros. Z.swap_greater.
          generalize (Z.lt_le_incl 0 b); generalize (Z.lt_le_incl 0 (-a)); 
          intros. apply H7 in H2; apply H6 in H3. apply H5; auto. }
          generalize (Not_Empty_Z (b-a)); intros. 
          rewrite H in H4; contradiction.
      + contradiction.
      + assert ((b + a)∈ S). { rewrite H1; apply AxiomII; exists (-1); split.
        * generalize (Z.add_opp_r b (a*-1)); intros. rewrite <- H4.
          generalize (Zopp_mult_distr_l a (-1)); intros. rewrite H5. 
          generalize (Z.mul_opp_opp a 1); intros. simpl in H6. rewrite H6.
          generalize (Z.mul_1_r a ); intros. rewrite H7; auto.
        * generalize (Z.lt_le_incl 0 b); generalize (Z.lt_le_incl 0 a); intros.
          Z.swap_greater. apply H4 in H3. apply H5 in H2.
          generalize (Z.add_nonneg_nonneg b a); intros. auto. }
          generalize (Not_Empty_Z (b+a)); intros; rewrite H in H4; contradiction.
    - red. intros. rewrite H1 in H; apply -> AxiomII in H. 
      simpl in H. destruct H, H. apply AxiomII. auto. }
    apply MiniMember_Z in H. destruct H as [r  H]. destruct H. double H.
    rewrite H1 in H3. apply -> AxiomII in H3; simpl in H3. 
    destruct H3 as [q H3]. exists q; exists r. split.
    - destruct H3. rewrite H3. 
      generalize (Zplus_minus (a*q) b); intros. auto.
    - destruct H3; split; Z.swap_greater; auto. 
      generalize (classic (r < Z.abs a));
      intros. destruct H5; auto. generalize (Ztrichotomy a 0); intros.
      destruct H6 as [H6 | [H6 | H6]]; auto.
      + assert ((b-a*(q-1)) ∈ S /\ (b-a*(q-1)) < r). { split.
        - rewrite H1; apply AxiomII. exists (q-1); split; auto. 
          generalize (Z.add_opp_r b (a * (q - 1))); intros. rewrite <- H7.
          generalize (Z.mul_sub_distr_l a q 1); intros. rewrite H8. 
          generalize (Z.add_opp_r b ((a * q - a * 1))); intros. rewrite H9.
          generalize (Z.sub_sub_distr b (a*q) (a*1)); intros. rewrite H10.
          rewrite <- H3. generalize (Z.mul_1_r a); intros; rewrite H11.
          generalize (Znot_lt_ge r (Z.abs a)); intros. apply H12 in H5.
          generalize (Z.abs_neq a); intros. generalize (Z.lt_le_incl a 0);
          intros. apply H14 in H6. apply H13 in H6. rewrite H6 in H5.
          Z.swap_greater. generalize (Z.add_le_mono_r (-a) r a); intros.
          apply H15 in H5. generalize (Z.add_opp_diag_l a); intros. 
          rewrite H16 in H5. auto. 
        - generalize (Z.add_lt_mono_r (b - a * (q - 1)) r (-r)); intros.
          apply H7. generalize (Z.add_opp_diag_r r); intros. rewrite H8.
          generalize (Z.add_opp_r b (a * (q - 1))); intros.
          rewrite <- H9. generalize (Z.mul_sub_distr_l a q 1); intros.
          rewrite H10. generalize (Z.add_opp_r b (a * q - a * 1)); intros.
          rewrite H11. generalize (Z.sub_sub_distr b (a*q) (a*1)); intros.
          rewrite H12. rewrite <- H3.
          generalize (Z.add_shuffle0 r (a*1) (-r)); intros. rewrite H13.
          generalize (Z.add_opp_diag_r r); intros. rewrite H14. 
          generalize (Z.mul_1_r a); intros. rewrite H15. auto. }
        destruct H7. apply H2 in H7. generalize (Z.le_ngt r (b - a * (q - 1)));
        intros. apply H9 in H7. contradiction.
      + contradiction.
      + assert ((b-a*(q+1)) ∈ S /\ (b-a*(q+1)) < r). { split.
        - rewrite H1; apply AxiomII. exists (q+1); split; auto. 
          generalize (Z.add_opp_r b (a * (q + 1))); intros. rewrite <- H7.
          generalize (Z.mul_add_distr_l a q 1); intros. rewrite H8. 
          generalize (Z.add_opp_r b ((a * q + a * 1))); intros. rewrite H9.
          generalize (Z.sub_add_distr b (a*q) (a*1)); intros. rewrite H10.
          rewrite <- H3. generalize (Z.mul_1_r a); intros; rewrite H11.
          generalize (Znot_lt_ge r (Z.abs a)); intros. apply H12 in H5.
          generalize (Z.abs_eq a); intros. generalize (Z.lt_le_incl 0 a); intros.
          Z.swap_greater. apply H14 in H6. apply H13 in H6. rewrite H6 in H5.
          apply Zle_minus_le_0 in H5. auto.
        - generalize (Z.add_opp_r b (a * (q + 1))); intros. rewrite <- H7.
          generalize (Z.mul_add_distr_l a q 1); intros. rewrite H8.
          generalize (Z.add_opp_r b ((a * q + a * 1))); intros. rewrite H9.
          generalize (Z.sub_add_distr b (a*q) (a*1)); intros. rewrite H10.
          rewrite <- H3. generalize (Z.lt_0_sub (r - a * 1) r ); intros.
          apply H11. generalize (Z.sub_sub_distr r r a); intros.
          generalize (Z.mul_1_r a); intros. rewrite H13. rewrite H12. 
          generalize (Z.sub_diag r); intros. rewrite H14. simpl. 
          Z.swap_greater; auto. }
        destruct H7. apply H2 in H7. generalize (Z.le_ngt r (b - a * (q + 1)));
        intros. apply H9 in H7. contradiction.
Qed.

(* 唯一性 *)
Theorem Theorem2_2_1' : forall a b q q' r r',  a ≠ 0 /\ 
  b = a * q + r /\ 0 <= r <Z.abs(a) /\ b = a * q' + r' /\ 0 <= r' <Z.abs(a) -> 
  q=q' /\ r=r'.
Proof.
  intros. destruct H, H0, H1, H2.
  assert (a * (q - q') = r' - r). { 
  generalize (Z.mul_sub_distr_l a q q'); intros. rewrite H4.
  generalize (Z.sub_move_r b r (a*q)); generalize (Z.sub_move_r b r' (a*q'));
  intros. apply H5 in H2; apply H6 in H0. rewrite <- H0; rewrite <- H2.
  generalize (Z.sub_sub_distr (b-r) b r'); intros. rewrite H7.
  generalize (Z.add_simpl_l b (-r)); intros.
  generalize (Z.add_opp_r b r); intros. rewrite H9 in H8. rewrite H8. 
  generalize (Z.add_comm r' (-r)); intros. 
  generalize (Z.add_opp_r r' r); intros. rewrite H11 in H10. auto. }
  generalize (classic (q - q' = 0)); intros; destruct H5.
  - rewrite H5 in H4. rewrite Z.mul_0_r in H4. apply Zminus_eq in H5.
    symmetry in H4. apply Zminus_eq in H4; split; auto.
  - assert (Z.abs(a*(q-q')) >= Z.abs(a)). { rewrite Z.abs_mul.
    generalize (Z.mul_le_mono_nonneg_l 1 (Z.abs (q - q')) (Z.abs a)); intros.
    Z.swap_greater. rewrite Z.mul_1_r in H6. apply H6.
    + apply Z.abs_nonneg.
    + generalize (Zlt_le_succ 0 (Z.abs (q - q'))); intros. 
      apply Z.abs_pos in H5. apply H7 in H5. auto. }
    rewrite H4 in H6. Z.swap_greater. generalize (Ztrichotomy (r' - r) 0);
    intros. destruct H7 as [H7 | [H7 | H7]].
      * apply Z.lt_le_incl in H7. apply Z.abs_neq in H7. rewrite H7 in H6.
        rewrite Z.opp_sub_distr in H6. 
        generalize (Z.le_add_le_sub_l r' r (Z.abs a)); intros.
        rewrite Z.add_opp_l in H6. apply H8 in H6.
        assert ((Z.abs a) <= (r' + Z.abs a)). {
        generalize (Zplus_le_compat_r 0 r' (Z.abs a)); intros. destruct H3.
        apply H9 in H3. auto. }
        assert ((Z.abs a) <= r). { eapply Z.le_trans; eauto. }
        destruct H1. apply Zlt_not_le in H11. contradiction.
      * rewrite H7 in H4. apply Zmult_integral in H4. 
        destruct H4; contradiction.
      * Z.swap_greater. apply Z.lt_le_incl in H7. apply Z.abs_eq in H7.
      rewrite H7 in H6. generalize (Z.le_add_le_sub_l r r' (Z.abs a)); intros.
      apply H8 in H6.
      assert ((Z.abs a) <= (r + Z.abs a)). {
      generalize (Zplus_le_compat_r 0 r (Z.abs a)); intros. destruct H1.
      apply H9 in H1. auto. }
      assert ((Z.abs a) <= r'). { eapply Z.le_trans; eauto. }
      destruct H3. apply Zlt_not_le in H11. contradiction.
Qed.

(* 定义除法 *)
Definition div (a b : Z) : (prod Z Z) :=
  C\{\ λ q r, b = a * q + r /\ 0 <= r <= Z.abs(a) \}\.

Definition q (a b : Z) : Z :=
  fst (C\{\ λ q r, b = a * q + r /\ 0 <= r <= Z.abs(a) \}\).

Definition r (a b : Z) : Z :=
  snd (C\{\ λ q r, b = a * q + r /\ 0 <= r <= Z.abs(a) \}\).
  
(* Definition exa_div a b :=
  match b with
    | 0 => a = 0
    | _ => r a b = 0
  end. *)
Definition exa_div a b := exists d, b = a * d.
(* Definition exa_div (a b : Z) := r a b = 0.
(* Notation " a | b " := (exa_div a b). *) *)


(* 定义：最大公约数 *)
Definition gcd (a b d : Z) := (exa_div d a) /\ (exa_div d b) /\ 
  (forall c, (exa_div c a) /\ (exa_div c b) -> exa_div c d).

(* 定义t[i]*a[i]的累加 *)
Fixpoint sum_a_t (a t : Ensemble (prod nat Z))(n:nat) {struct n} : Z :=
  match n with
  | O => a [O] * t[O]
  | S p => sum_a_t a t p + a [n] * t[n]
  end.


(* n个数的最大公约数 *)
Definition gcd_n (a : Ensemble (prod nat Z)) (n : nat) ( d : Z) := 
  Function a /\ dom[ a ] = \{λ u, (u < n)%nat \} -> 
  (forall i , i ∈ dom[a] -> exa_div d a[i]) /\ 
  (forall c, (forall i0, i0 ∈ dom[a] -> exa_div c a[i0]) -> exa_div c d).

Lemma Lemma1_4_2 : forall (n : nat) (a t : Ensemble (prod nat Z)), 
  Function a /\ \{λ u, (u <= n)%nat \} ⊂ dom[a] -> 
  Function t /\ \{λ u, (u <= n)%nat \} ⊂ dom[t] ->
  (forall i, (i <= n)%nat -> t[i] = 0) -> sum_a_t a t n = 0.
Proof.
  intro n. induction n.
  - intros. simpl. assert (t[0%nat] = 0). { apply H1. auto. }
    rewrite H2. apply Z.mul_0_r.
  - intros. simpl. destruct H, H0. assert ((sum_a_t a t n) = 0). { apply IHn;
    try split; auto.
    - red; intros. apply -> AxiomII in H4; simpl in H4. apply H2.
      apply AxiomII. apply Nat.le_le_succ_r; auto.
    - red; intros. apply -> AxiomII in H4; simpl in H4. apply H3.
      apply AxiomII. apply Nat.le_le_succ_r; auto. }
    rewrite H4; simpl. assert (t [S n] = 0). { apply H1. apply Nat.le_refl. }
    rewrite H5. apply Z.mul_0_r.
Qed.

Lemma Lemma1_4_2b : forall (n: nat)  (a t1 t2: Ensemble (prod nat Z)),
  Function a /\ \{λ u, (u <= n)%nat \} ⊂ dom[a] ->
  Function t1 /\ \{λ u, (u <= n)%nat \} ⊂ dom[t1] ->
  Function t2 /\ \{λ u, (u <= n)%nat \} ⊂ dom[t2] -> 
  (forall i, (i <= n)%nat -> t1[i] = t2[i]) ->
  sum_a_t a t1 n = sum_a_t a t2 n.
Proof.
  intro n. induction n; intros. 
  - simpl. assert (t1 [0%nat] = t2 [0%nat]). { apply H2. auto. }
    rewrite H3; auto.
  - simpl. assert (sum_a_t a t1 n = sum_a_t a t2 n). { apply IHn; try split;
    try tauto.
    + red; intros. destruct H. apply -> AxiomII in H3; simpl in H3.
      apply H4. apply AxiomII. apply Nat.le_le_succ_r; auto.
    + red; intros. destruct H0. apply -> AxiomII in H3; simpl in H3.
      apply H4. apply AxiomII. apply Nat.le_le_succ_r; auto.
    + red; intros. destruct H1. apply -> AxiomII in H3; simpl in H3.
      apply H4. apply AxiomII. apply Nat.le_le_succ_r; auto.
    + intros. apply Nat.le_le_succ_r in H3. apply H2 in H3. auto. }
    assert (t1 [S n] = t2[S n] ). { apply H2. auto. }
    rewrite H3. rewrite H4. auto.
Qed.
  
Lemma Lemma1_4_2a : forall (n i: nat) (a : Ensemble (prod nat Z)) k,
  Function a /\ \{λ u, (u <= n)%nat \} ⊂ dom[a] -> (i <= n)%nat ->
  k * a[i] = sum_a_t a \{\ λ (u:nat) (v:Z), (u <= n)%nat /\ ((u=i /\ v=k) \/ 
            (u≠i /\ v=0)) \}\ n.
Proof.
  intro n. induction n; intros.
  - destruct H. simpl. assert (i = 0)%nat. 
    { apply le_n_0_eq in H0. symmetry. auto. } subst i. 
    assert (Function \{\ λ(u : nat)(v : Z),(u <= 0)%nat /\
    ((u = 0%nat /\ v = k) \/ u ≠ 0%nat /\ v = 0) \}\). {
    red; intros. apply -> AxiomII_P in H2. simpl in H2. 
    apply -> AxiomII_P in H3; simpl in H3. destruct H2, H3. 
    apply le_n_0_eq in H2. destruct H4, H5, H4, H5; try contradiction.
    - rewrite H7; auto.
    - rewrite H7; auto. }
    assert ([0%nat, k] ∈ \{\ λ(u : nat)(v : Z),(u <= 0)%nat /\
    (u = 0%nat /\ v = k \/ u ≠ 0%nat /\ v = 0) \}\).
    { apply AxiomII_P. split; auto. }
    apply f_x' in H3; auto. rewrite H3. apply Z.mul_comm.
  - simpl. apply le_lt_or_eq in H0. destruct H, H0.
    + apply lt_n_Sm_le in H0.
      assert (k * a [i] = sum_a_t a
      \{\ λ(u : nat)(v : Z),(u <=  n)%nat /\ 
      (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\ n). 
      { apply IHn; auto. split; auto. red; intros. apply -> AxiomII in H2;
      simpl in H2. apply H1. apply AxiomII. 
      apply Nat.le_le_succ_r in H2; auto. }
      assert (sum_a_t a \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
      (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\ n = 
      sum_a_t a \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
      (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\ n).
      { apply Lemma1_4_2b.
        - split; auto. red; intros; apply -> AxiomII in H3; simpl in H3;
          apply H1. apply AxiomII. apply Nat.le_le_succ_r in H3; auto.
        - assert (Function \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
          (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
          { + red; intros. apply -> AxiomII_P in H3; apply -> AxiomII_P in H4.
            destruct H3, H4. destruct H5, H6, H5, H6.
            * rewrite H8; auto.
            * contradiction.
            * contradiction.
            * rewrite H8; auto. }
      split; auto.
    red; intros. apply -> AxiomII in H4; simpl in H4.
    apply AxiomII. exists \{\
    λ(u : nat)(v : Z),(u <= n)%nat /\ (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\[z].
    apply AxiomII_P. split; auto. generalize (classic (z = i)); intros.
    destruct H5.
    + left. split; auto. subst z.
      assert ([i, k] ∈ \{\
       λ(u : nat)(v : Z),(u <= n)%nat /\ 
       (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
      { apply AxiomII_P. split; auto. }
      apply f_x'; auto.
    + right. split; auto.
    assert ([z, 0] ∈ \{\
       λ(u : nat)(v : Z),(u <= n)%nat /\ 
       (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
      { apply AxiomII_P. split; auto. }
      apply f_x'; auto.
  - assert (Function \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
    (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
      { + red; intros. apply -> AxiomII_P in H3; apply -> AxiomII_P in H4.
        destruct H3, H4. destruct H5, H6, H5, H6.
        * rewrite H8; auto.
        * contradiction.
        * contradiction.
        * rewrite H8; auto. }
    split; auto.
    red; intros. apply -> AxiomII in H4; simpl in H4.
    apply AxiomII. exists \{\
    λ(u : nat)(v : Z),(u <= S n)%nat /\ 
    (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\[z].
    apply AxiomII_P. split; auto. generalize (classic (z = i)); intros.
    destruct H5.
    + left. split; auto. subst z.
      assert ([i, k] ∈ \{\
       λ(u : nat)(v : Z),(u <= S n)%nat /\ 
       (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
      { apply AxiomII_P. split; auto. }
      apply f_x'; auto.
    + right. split; auto.
    assert ([z, 0] ∈ \{\
       λ(u : nat)(v : Z),(u <=S n)%nat /\ 
       (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
      { apply AxiomII_P. split; auto. }
      apply f_x'; auto.
  - intros. generalize (classic (i0 = i)); intros. 
    assert (Function \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
    (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
      { + red; intros. apply -> AxiomII_P in H5; apply -> AxiomII_P in H6.
        destruct H5, H6. destruct H7, H8, H7, H8.
        * rewrite H10; auto.
        * contradiction.
        * contradiction.
        * rewrite H10; auto. }
    assert (Function \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
    (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
      { + red; intros. apply -> AxiomII_P in H6; apply -> AxiomII_P in H7.
        destruct H6, H7. destruct H8, H9, H8, H9.
        * rewrite H11; auto.
        * contradiction.
        * contradiction.
        * rewrite H11; auto. }
   destruct H4.
   + subst i0. assert ([i, k] ∈ 
   \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
   (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
   { apply AxiomII_P. split; auto. }
   assert ([i, k] ∈ 
   \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
   (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
   { apply AxiomII_P. split; auto. }
   assert (\{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
   (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\ [i] = k).
   { apply f_x'; auto. }
   assert (\{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
   (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\ [i] = k).
   { apply f_x'; auto. }
   rewrite H8; rewrite H9. auto.
   +assert ([i0, 0] ∈ 
   \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
   (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
   { apply AxiomII_P. split; auto. }
   assert ([i0, 0] ∈ 
   \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
   (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
   { apply AxiomII_P. split; auto. }
   assert (\{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
   (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\ [i0] = 0).
   { apply f_x'; auto. }
   assert (\{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
   (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\ [i0] = 0).
   { apply f_x'; auto. }
   rewrite H9; rewrite H10; auto. }
   rewrite H3 in H2. rewrite <- H2.
   assert ([S n, 0] ∈ \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
   (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
   { apply AxiomII_P. split; auto. right. split; auto. intro. subst i.
   generalize (Nat.lt_succ_diag_r n); intros. apply lt_not_le in H4.
   contradiction. }
   assert (Function \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
   (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
      { + red; intros. apply -> AxiomII_P in H5; apply -> AxiomII_P in H6.
        destruct H5, H6. destruct H7, H8, H7, H8.
        * rewrite H10; auto.
        * contradiction.
        * contradiction.
        * rewrite H10; auto. }
   assert (\{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
   (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\ [S n] = 0). 
   { apply f_x'; auto. } rewrite H6. rewrite Z.mul_0_r. 
  rewrite Z.add_0_r. auto.
  + assert (sum_a_t a \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
    (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\ n = 0).
    { apply Lemma1_4_2.
      - split; auto. red; intros. apply H1. apply -> AxiomII in H2; simpl in H2.
        apply AxiomII. apply Nat.le_le_succ_r in H2. auto.
      - split.
        + red; intros. apply -> AxiomII_P in H2; apply -> AxiomII_P in H3.
          simpl in H2; simpl in H3. destruct H2, H3, H4, H5, H4, H5.
          * rewrite H7. auto.
          * contradiction.
          * contradiction.
          * rewrite H7; auto.
        + red; intros. apply -> AxiomII in H2; apply AxiomII. exists
          \{\
         λ(u : nat)(v : Z),(u <= S n)%nat /\
                           (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\[z].
        assert (Function \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
        (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
        { + red; intros. apply -> AxiomII_P in H3; apply -> AxiomII_P in H4.
          destruct H3, H4. destruct H5, H6, H5, H6.
          * rewrite H8; auto.
          * contradiction.
          * contradiction.
          * rewrite H8; auto. }
      apply AxiomII_P. simpl in H2. split.
      * apply Nat.le_le_succ_r in H2. auto.
      * right. split.
        -- intro. rewrite H4 in H2. generalize (Nat.lt_succ_diag_r n);
           intros. rewrite <- H0 in H5. apply lt_not_le in H5. contradiction.
        -- assert ([z, 0] ∈ 
        \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
        (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
        { apply AxiomII_P. split. apply Nat.le_le_succ_r in H2. auto.
        right. split; auto. intro. rewrite H4 in H2. 
        generalize (Nat.lt_succ_diag_r n);
        intros. rewrite <- H0 in H5. apply lt_not_le in H5. contradiction. }
        apply f_x'; auto.
  - intros. assert ([i0, 0] ∈ 
    \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\
                  (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\). {
    apply AxiomII_P. split. apply Nat.le_le_succ_r in H2. auto. right.
    split; auto. intro. rewrite H0 in H3. generalize (Nat.lt_succ_diag_r n);
    intros. rewrite <- H3 in H4. apply lt_not_le in H4. contradiction. }
    assert (Function \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
    (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
      { + red; intros. apply -> AxiomII_P in H4; apply -> AxiomII_P in H5.
        destruct H4, H5. destruct H6, H7, H6, H7.
        * rewrite H9; auto.
        * contradiction.
        * contradiction.
        * rewrite H9; auto. }
    apply f_x'; auto. } rewrite H2. simpl. assert ([S n, k] ∈ 
    \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
    (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\ ).
    { apply AxiomII_P. split. auto. left. symmetry in H0. split; auto. }
    assert (Function \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
    (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\).
      { + red; intros. apply -> AxiomII_P in H4; apply -> AxiomII_P in H5.
        destruct H4, H5. destruct H6, H7, H6, H7.
        * rewrite H9; auto.
        * contradiction.
        * contradiction.
        * rewrite H9; auto. }
    assert (\{\ λ(u : nat)(v : Z),(u <= S n)%nat /\
            (u = i /\ v = k \/ u ≠ i /\ v = 0) \}\ 
            [S n] = k). { apply f_x'; auto. } rewrite H5. rewrite H0.
  apply Z.mul_comm; auto.
Qed.

Lemma Lemma1_4_2c : forall (n i: nat ) k, 
  Function \{\ λ (u:nat) (v:Z), (u <= n)%nat /\ 
  ((u=i /\ v=k) \/  (u≠i /\ v=0)) \}\ .
Proof.
  intros. red; intros. apply -> AxiomII_P in H; apply -> AxiomII_P in H0.
  destruct H, H0. destruct H1, H2, H1, H2.
  - rewrite H4; auto.
  - contradiction.
  - contradiction.
  - rewrite H4; auto.
Qed.

Lemma Lemma1_4_2d : forall c a b, exa_div c a -> exa_div c b ->
  exa_div c (a + b).
Proof.
  intros. red. red in H; red in H0. destruct H, H0. exists (x + x0). 
  rewrite H; rewrite H0. ring.
Qed.

Lemma Lemma1_4_2e : forall c t a, exa_div c a -> exa_div c (t*a).
Proof.
  intros. red in H; red. destruct H. exists (t*x); rewrite H; ring.
Qed.

Lemma Lemma1_4_2f : forall (n : nat) (a t : Ensemble (prod nat Z)) (c : Z),
  \{ λ u, (u <= n)%nat \} ⊂ dom[a] -> \{ λ u, (u <= n)%nat \} ⊂ dom[t] ->
  (forall i, (i<=n)%nat -> exa_div c a[i]) ->
  exa_div c (sum_a_t a t n).
Proof.
  intro n. induction n; intros.
  - red. assert (0 <= 0)%nat. { apply Nat.le_refl. } apply H1 in H2. red in H2.
    destruct H2. exists (t[0%nat]*x). simpl. rewrite H2. ring.
  - simpl. apply Lemma1_4_2d.
    + apply IHn; try red; intros.
      * apply H. apply AxiomII; apply -> AxiomII in H2; simpl in H2.
        apply Nat.le_le_succ_r in H2; auto.
      * apply H0. apply AxiomII; apply -> AxiomII in H2; simpl in H2.
        apply Nat.le_le_succ_r in H2; auto.
      * apply Nat.le_le_succ_r in H2. apply H1 in H2. red in H2. destruct H2.
        exists x; auto.
    + assert (S n <= S n)%nat. { apply Nat.le_refl. }
      apply H1 in H2. red in H2. destruct H2. red.
      exists (t[S n] * x); rewrite H2; ring.
Qed.

(* Lemma Lemma1_4_2g : forall () *)
Lemma Lemma1_4_2g : forall ( n i : nat) (a t: Ensemble (prod nat Z)) q , 
  \{ λ u, (u <= n)%nat \} ⊂ dom[a] -> \{ λ u, (u <= n)%nat \} ⊂ dom[t] ->
  Function a -> Function t -> (i<=n)%nat->
  a [i] - (sum_a_t a t n ) * q = 
  sum_a_t a \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
  (u = i /\ v = 1 - q * t [i] \/ u ≠ i /\ v = - q * t [u]) \}\ n .
Proof. 
  intro n; induction n; intros.
  - apply le_n_0_eq in H3. subst i. 
    assert (Function \{\ λ(u : nat)(v : Z),(u <= 0)%nat /\
           (u = 0%nat /\ v = 1 - q0 * t [0%nat] \/ u ≠ 0%nat /\
            v = - q0 * t [u]) \}\). 
    { red; intros. apply -> AxiomII_P in H3; apply -> AxiomII_P in H4.
      destruct H3, H4. destruct H5, H6, H5, H6.
      * rewrite H7; auto.
      * contradiction.
      * contradiction.
      * rewrite H7; auto. }
    assert ([0%nat, (1 - q0 * t[0%nat])] ∈ \{\ λ(u : nat)(v : Z),(u <= 0)%nat /\
   (u = 0%nat /\ v = (1 - q0 * t [0%nat]) \/ u ≠ 0%nat /\ v = (- q0 * t [u])) \}\).
   { apply AxiomII_P. split; auto. } 
  apply f_x' in H4; auto.
  assert (exists t', t' = \{\ λ(u : nat)(v : Z),(u <= 0)%nat /\
                    (u = 0%nat /\ v = 1 - q0 * t [0%nat] \/
                     u ≠ 0%nat /\ v = - q0 * t [u]) \}\).
  { exists \{\ λ(u : nat)(v : Z),(u <= 0)%nat /\
                    (u = 0%nat /\ v = 1 - q0 * t [0%nat] \/
                     u ≠ 0%nat /\ v = - q0 * t [u]) \}\; auto. }
   destruct H5 as [t' H5]. rewrite <- H5 in *.
   simpl. rewrite H4. ring. 
  - assert (exists t', t' = \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
    (u = i /\ v = 1 - q0 * t [i] \/ u ≠ i /\ v = - q0 * t [u]) \}\). {
    exists \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ 
    (u = i /\ v = 1 - q0 * t [i] \/ u ≠ i /\ v = - q0 * t [u]) \}\ . auto. }
    destruct H4 as [t' H4]. rewrite <- H4 in *. simpl.
    assert (Function t'). 
    { red; intros. rewrite H4 in *. apply -> AxiomII_P in H5; apply -> AxiomII_P in H6.
      destruct H5, H6. destruct H7, H8, H7, H8.
      * rewrite H9; auto.
      * contradiction.
      * contradiction.
      * rewrite H9; auto. }
    generalize (classic (i <= n)%nat); intros; destruct H6.
    + assert ( a [i] - sum_a_t a t n * q0 = 
      sum_a_t a \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
      (u = i /\ v = 1 - q0 * t [i] \/ u ≠ i /\ v = - q0 * t [u]) \}\ n). 
      { apply IHn; auto; try red; intros; try apply -> AxiomII in H7; try simpl in H7;
        try apply H; try apply H0; try apply AxiomII; auto. } 
      assert (sum_a_t a t' n = sum_a_t a \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
      (u = i /\ v = 1 - q0 * t [i] \/ u ≠ i /\ v = - q0 * t [u]) \}\ n). 
      { apply Lemma1_4_2b.
        - split; auto. red; intros. apply H. apply AxiomII.
          apply -> AxiomII in H8; simpl in H8. auto.
        - split; auto. red; intros. rewrite H4; apply AxiomII. exists
          \{\ λ(u : nat)(v : Z),(u <= S n)%nat /\ (u = i /\ v = 1 - q0 * t [i] \/
          u ≠ i /\ v = - q0 * t [u]) \}\[z]. apply AxiomII_P.
          apply -> AxiomII in H8; simpl in H8. split; auto.
          generalize (classic (z = i)); intros; destruct H9. 
          + left. split; auto.
            assert ([z, 1-q0*t[i]] ∈ t'). { rewrite H4; apply AxiomII_P.
            split; auto. } rewrite <- H4. apply f_x' in H10; auto.
          + right. split; auto.
            assert ([z, -q0*t[z]] ∈ t'). { rewrite H4; apply AxiomII_P.
            split; auto. } rewrite <- H4. apply f_x' in H10; auto.
        - assert (Function \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
          (u = i /\ v = 1 - q0 * t [i] \/ u ≠ i /\ v = - q0 * t [u]) \}\). 
          { red; intros. apply -> AxiomII_P in H8; apply -> AxiomII_P in H9;
            destruct H8, H9; simpl in H8; simpl in H9. 
            destruct H10, H11, H10, H11.
            * rewrite H13; auto.
            * contradiction.
            * contradiction.
            * rewrite H13; auto.  } split; auto.
          red; intros. apply AxiomII. apply -> AxiomII in H9; simpl in H9.
          exists \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
          (u = i /\ v = 1 - q0 * t [i] \/ u ≠ i /\ v = - q0 * t [u]) \}\[z].
          apply AxiomII_P. split; auto.
          generalize (classic (z = i)); intros; destruct H10.
          * left; split;auto.
            assert ([z, 1 - q0 * t [i]] ∈ \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
            (u = i /\ v = 1 - q0 * t [i] \/ u ≠ i /\ v = - q0 * t [u]) \}\). 
            { apply AxiomII_P. split; auto. } apply f_x' in H11; auto.
          * right; split;auto.
            assert ([z, - q0 * t [z]] ∈ \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
            (u = i /\ v = 1 - q0 * t [i] \/ u ≠ i /\ v = - q0 * t [u]) \}\). 
            { apply AxiomII_P. split; auto. } apply f_x' in H11; auto.
      - assert (Function \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
        (u = i /\ v = 1 - q0 * t [i] \/ u ≠ i /\ v = - q0 * t [u]) \}\). 
        { red; intros. apply -> AxiomII_P in H8; apply -> AxiomII_P in H9;
          destruct H8, H9; simpl in H8; simpl in H9. destruct H10, H11, H10, H11.
          * rewrite H13; auto.
          * contradiction.
          * contradiction.
          * rewrite H13; auto.  }
        intros. generalize (classic (i0 = i)); intros; destruct H10.
        + assert ([i0, 1 - q0 * t [i]] ∈ t'). { rewrite H4; apply AxiomII_P.
          split; auto. }
          assert ([i0, 1 - q0 * t [i]] ∈ \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
          (u = i /\ v = 1 - q0 * t [i] \/ u ≠ i /\ v = - q0 * t [u]) \}\). {
          apply AxiomII_P; auto. }
          apply f_x' in H11; auto. apply f_x' in H12; auto.
          rewrite H11; rewrite H12. auto.
        + assert ([i0, - q0 * t [i0]] ∈ t'). 
          { rewrite H4. apply AxiomII_P; auto. }
          assert ([i0, - q0 * t [i0]] ∈ \{\ λ(u : nat)(v : Z),(u <= n)%nat /\ 
          (u = i /\ v = 1 - q0 * t [i] \/ u ≠ i /\ v = - q0 * t [u]) \}\). {
          apply AxiomII_P; auto. } apply f_x' in H11; auto. apply f_x' in H12; auto.
          rewrite H11; rewrite H12. auto. }
      rewrite <- H8 in H7. rewrite <- H7. 
      assert ([S n, -q0 * t[S n]] ∈ t'). 
      { rewrite H4; apply AxiomII_P.
        split; auto. right; split; auto. intro. rewrite <- H9 in H6.
        generalize (Nat.lt_succ_diag_r n); intros.
        apply le_not_lt in H6. contradiction. } 
      apply f_x' in H9; auto. rewrite H9. rewrite Z.mul_add_distr_r. 
      rewrite Z.sub_add_distr.
      rewrite Z.mul_shuffle3. rewrite Z.mul_assoc. ring.
    + assert ( (i= S n)%nat). { apply not_le in H6.
      apply lt_le_S in H6. apply Nat.le_antisymm; auto. } rewrite H7.
      assert ([S n, 1 - q0 * t [i]] ∈ t'). { rewrite H4. 
      apply AxiomII_P. split; auto. } apply f_x' in H8; auto.
      rewrite H8. rewrite H7.
      assert (forall n1:nat, (n1 < i)%nat -> 
      -sum_a_t a t n1 * q0 = sum_a_t a t' n1). 
      { intro n1. induction n1; intros.
        - simpl. assert ([0%nat, - q0 * t [0%nat]] ∈ t'). { rewrite H4.
          apply AxiomII_P; split; try lia. right. split; auto. rewrite H7.
          apply Nat.neq_0_succ. } apply f_x' in H10; auto. rewrite H10. ring.
        - simpl. assert ( (n1 < i)%nat ). { lia. } apply IHn1 in H10.
          assert ([S n1, - q0 * t [S n1]] ∈ t'). 
          { rewrite H4; apply AxiomII_P. rewrite H7 in H9. split.
            - apply Nat.lt_le_incl in H9. auto.
            - right. split. rewrite <- H7 in H9. intro. rewrite <- H11 in H9.
              eapply Nat.lt_irrefl; eauto. auto. }
          apply f_x' in H11; auto.
          rewrite H11; rewrite <- H10; ring. }
      assert (n < i)%nat. { rewrite H7; auto. }
      apply H9 in H10. rewrite <- H10. ring.
Qed.

Theorem Theorem1_4_2 : forall (n : nat)(a : Ensemble (prod nat Z)), 
  (n >= 1)%nat /\ Function a /\ dom[ a ] = \{λ u, (u < n)%nat \} ->
  exists d,  gcd_n a n d.
Proof.
  intros. destruct H, H0.
  generalize (classic (forall i, i ∈ dom[a] -> a[i] = 0)); intros; destruct H2.
  (*a1=a2=...an=0*)
  - exists 0. red. repeat split; auto; intros. 
    + apply H2 in H4. rewrite H4; exists 0; auto.
    + exists 0; auto. ring.
  (* a1,a2,...,an不全为零 *)
  - assert(H3 : exists I, I = \{λ b, exists t, Function t /\
    dom[ t ] = \{λ u, (u < n)%nat \} /\ b = sum_a_t a t (n-1) \}).
    { exists \{λ b, exists t, Function t /\ dom[ t ] = \{λ u, (u < n)%nat \} /\
      b = sum_a_t a t (n-1) \}. auto. } destruct H3 as [I H3].
    assert(H4 : exists I', I' = \{ λ s, s ∈ I /\ s > 0 \}).
    { exists \{ λ s, s ∈ I /\ s > 0 \}; auto. } destruct H4 as [I' H4].
    (* I'为正整数集的一个非空子集 *)
    assert(I' ≠ Φ Z /\ I' ⊂ Z_POS).
    { apply not_all_ex_not in H2. destruct H2 as [i H2].
      apply imply_to_and in H2. destruct H2.
      split.
      (* a[i] > 0 \/ a[i] < 0 *)
      - generalize (Ztrichotomy a[i] 0); intros. 
        destruct H6 as [H6 | [H6 | H6]]; try contradiction.
        + assert ((-a[i]) ∈ I'). { rewrite H4. apply AxiomII. split.
          - rewrite H3. apply AxiomII.
            exists \{\ λ (u:nat) (v:Z), (u < n)%nat /\ ((u=i /\ v=-1) \/ 
            (u≠i /\ v=0)) \}\. 
            assert (Function \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = -1 \/ u ≠ i /\ v = 0) \}\). {
            red; intros. apply -> AxiomII_P in H7; apply -> AxiomII_P in H8.
              destruct H7, H8. destruct H9, H10, H9, H10.
              * rewrite H12; auto.
              * contradiction.
              * contradiction.
              * rewrite H12; auto. }
            assert (dom[ \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = -1 \/ u ≠ i /\ v = 0) \}\] = 
            \{ λ u : nat,(u < n)%nat \} ). { apply AxiomI; split; intros.
            - apply -> AxiomII in H8. simpl in H8. destruct H8.
              apply -> AxiomII_P in H8. simpl in H8. apply AxiomII. tauto.
            - apply AxiomII. exists \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = -1 \/ u ≠ i /\ v = 0) \}\[z]. apply AxiomII_P.
            apply -> AxiomII in H8; simpl in H8. split; auto.
            generalize (classic (z = i)); intros. destruct H9.
              + left. split; auto. assert ([z, -1] ∈ 
              \{\ λ(u : nat)(v : Z),(u < n)%nat /\
              (u = i /\ v = -1 \/ u ≠ i /\ v = 0) \}\). apply AxiomII_P.
              split; auto. apply f_x'; auto.
              + right; split; auto. assert ([z, 0] ∈ 
              \{\ λ(u : nat)(v : Z),(u < n)%nat /\
              (u = i /\ v = -1 \/ u ≠ i /\ v = 0) \}\). apply AxiomII_P.
              split; auto. apply f_x'; auto. } repeat split; auto.
            assert (  \{\
            λ(u : nat)(v : Z),(u < n)%nat /\
            ((u = i /\ v = -1) \/ u ≠ i /\ v = 0) \}\ = 
              \{\  λ(u : nat)(v : Z),(u <= n - 1)%nat /\
              ((u = i /\ v = -1) \/ u ≠ i /\ v = 0) \}\ ).
     { apply AxiomI; split; intros.
      - apply Property_P in H9. destruct H9, H9, H9. rewrite H9.
        rewrite H9 in H10. apply AxiomII_P. apply -> AxiomII_P in H10. simpl
        in H10. repeat split; try tauto. destruct H10. 
        apply Nat.lt_le_pred in H10. rewrite Nat.sub_1_r. auto. 
      - apply Property_P in H9. destruct H9, H9, H9. rewrite H9.
        rewrite H9 in H10. apply AxiomII_P. apply -> AxiomII_P in H10. simpl
        in H10. repeat split; try tauto. destruct H10. 
        apply le_lt_n_Sm in H10. rewrite Nat.sub_1_r in H10.
        rewrite Nat.succ_pred_pos in H10; auto. } rewrite H9.
        assert (-a[i] = -1 * a[i]). { ring. } rewrite H10. 
        apply Lemma1_4_2a.
        + split; auto. red; intros. apply -> AxiomII in H11; simpl in H11.
          rewrite H1. apply AxiomII. apply le_lt_n_Sm in H11. 
          rewrite Nat.sub_1_r in H11. rewrite Nat.succ_pred_pos in H11; auto.
        + rewrite H1 in H2. apply -> AxiomII in H2. simpl in H2.
          apply Nat.lt_le_pred in H2. rewrite Nat.sub_1_r. auto.
      - apply Z.opp_pos_neg in H6. Z.swap_greater; auto. }
    intro. rewrite H8 in H7. generalize (Not_Empty_Z (-a[i])); 
    intros. contradiction.
    + assert (a[i] ∈ I'). { rewrite H4. apply AxiomII. split.
          - rewrite H3. apply AxiomII.
            exists \{\ λ (u:nat) (v:Z), (u < n)%nat /\ ((u=i /\ v=1) \/ 
            (u≠i /\ v=0)) \}\. intros. 
            assert (Function \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = 1 \/ u ≠ i /\ v = 0) \}\). {
            red; intros. apply -> AxiomII_P in H7; apply -> AxiomII_P in H8.
              destruct H7, H8. destruct H9, H10, H9, H10.
              * rewrite H12; auto.
              * contradiction.
              * contradiction.
              * rewrite H12; auto. }
            assert (dom[ \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = 1 \/ u ≠ i /\ v = 0) \}\] = 
            \{ λ u : nat,(u < n)%nat \} ). { apply AxiomI; split; intros.
            - apply -> AxiomII in H8. simpl in H8. destruct H8.
              apply -> AxiomII_P in H8. simpl in H8. apply AxiomII. tauto.
            - apply AxiomII. exists \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = 1 \/ u ≠ i /\ v = 0) \}\[z]. apply AxiomII_P.
            apply -> AxiomII in H8; simpl in H8. split; auto.
            generalize (classic (z = i)); intros. destruct H9.
              + left. split; auto. assert ([z, 1] ∈ 
              \{\ λ(u : nat)(v : Z),(u < n)%nat /\
              (u = i /\ v = 1 \/ u ≠ i /\ v = 0) \}\). apply AxiomII_P.
              split; auto. apply f_x'; auto.
              + right; split; auto. assert ([z, 0] ∈ 
              \{\ λ(u : nat)(v : Z),(u < n)%nat /\
              (u = i /\ v = 1 \/ u ≠ i /\ v = 0) \}\). apply AxiomII_P.
              split; auto. apply f_x'; auto. } repeat split; auto.
     assert (  \{\ λ(u : nat)(v : Z),(u < n)%nat /\
            ((u = i /\ v = 1) \/ u ≠ i /\ v = 0) \}\ = 
              \{\  λ(u : nat)(v : Z),(u <= n - 1)%nat /\
              ((u = i /\ v = 1) \/ u ≠ i /\ v = 0) \}\ ).
     { apply AxiomI; split; intros.
      - apply Property_P in H9. destruct H9, H9, H9. rewrite H9.
        rewrite H9 in H10. apply AxiomII_P. apply -> AxiomII_P in H10. simpl
        in H10. repeat split; try tauto. destruct H10. 
        apply Nat.lt_le_pred in H10. rewrite Nat.sub_1_r. auto. 
      - apply Property_P in H9. destruct H9, H9, H9. rewrite H9.
        rewrite H9 in H10. apply AxiomII_P. apply -> AxiomII_P in H10. simpl
        in H10. repeat split; try tauto. destruct H10. 
        apply le_lt_n_Sm in H10. rewrite Nat.sub_1_r in H10.
        rewrite Nat.succ_pred_pos in H10; auto. } rewrite H9.
        assert (a[i] = 1 * a[i]). { ring. } rewrite H10. 
        apply Lemma1_4_2a.
        + split; auto. red; intros. apply -> AxiomII in H11; simpl in H11.
          rewrite H1. apply AxiomII. apply le_lt_n_Sm in H11. 
          rewrite Nat.sub_1_r in H11. rewrite Nat.succ_pred_pos in H11; auto.
        + rewrite H1 in H2. apply -> AxiomII in H2. simpl in H2.
          apply Nat.lt_le_pred in H2. rewrite Nat.sub_1_r. auto.
      - auto. }
    intro. rewrite H8 in H7. generalize (Not_Empty_Z (a[i])); 
    intros. contradiction.
  - red; intros. rewrite H4 in H6. apply -> AxiomII in H6; simpl in H6.
    apply AxiomII. tauto. }
  apply MiniMember_Z' in H5. destruct H5 as [d H5]. destruct H5. generalize H5.
  intros H77. rewrite H4 in H5. apply -> AxiomII in H5; simpl in H5. destruct H5.
  rewrite H3 in H5; apply -> AxiomII in H5; simpl in H5. destruct H5 as [t H5].
  exists d. red. intros.
  apply not_all_ex_not in H2. destruct H2 as [i0 H2].
  apply imply_to_and in H2. destruct H2. 
  (* 由带余除法可得ai = d * q + r *)
  split; intros.
  + generalize (Theorem1_4_1 d a[i]); intros. assert (d ≠ 0). { Z.swap_greater;
    apply Z.lt_neq in H7. apply not_eq_sym; auto. } 
    apply H11 in H12. destruct H12 as [q [r H12]]. destruct H12. 
    generalize (classic (r > 0)); intros. destruct H14.
    * assert (r ∈ I'). { 
        assert (r = a[i] - d * q). { symmetry in H12.
        apply Z.add_move_l in H12. auto. } rewrite H15. rewrite H4.
        apply AxiomII. split.
        -- rewrite H3. apply AxiomII.
           exists ( \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
              ((u = i /\ v = (1 - q * t[i])) \/ (u ≠ i /\ v = - q * t[u])) \}\).
               assert (Function \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
              ((u = i /\ v = (1 - q * t[i])) \/ (u ≠ i /\ v = - q * t[u])) \}\). 
              { red; intros. apply -> AxiomII_P in H16; apply -> AxiomII_P in H17.
                destruct H16, H17. destruct H18, H19, H18, H19.
                * rewrite H20; auto.
                * contradiction.
                * contradiction.
                * rewrite H20; auto. }
               assert(dom[ \{\ λ(u : nat)(v : Z),(u < n)%nat /\
               (u = i /\ v = 1 - q * t [i] \/ u ≠ i /\ v = - q * t [u]) \}\] =
                \{ λ u : nat, (u < n)%nat \}).
                { apply AxiomI; split; intros.
                  - apply -> AxiomII in H17. simpl in H17. destruct H17.
                    apply -> AxiomII_P in H17. simpl in H17. apply AxiomII. tauto.
                  - apply AxiomII. exists \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
                    ((u = i /\ v = (1 - q * t[i])) \/ 
                    (u ≠ i /\ v = - q * t[u])) \}\[z]. 
                    apply AxiomII_P.
                    apply -> AxiomII in H17; simpl in H17. split; auto.
                    generalize (classic (z = i)); intros. destruct H18.
                    + left. split; auto. assert ([z, 1 - q * t [i]] ∈ 
                    \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
                    ((u = i /\ v = (1 - q * t[i])) \/ 
                    (u ≠ i /\ v = - q * t[u])) \}\ ).
                    apply AxiomII_P.
                    split; auto. apply f_x'; auto.
                    + right; split; auto. assert ([z, - q * t [z]] ∈ 
                    \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
                    ((u = i /\ v = (1 - q * t[i])) \/ 
                    (u ≠ i /\ v = - q * t[u])) \}\).
                    apply AxiomII_P.
                    split; auto. apply f_x'; auto. } repeat split; auto.
                    destruct H5, H18. rewrite H19.
                    assert (\{\ λ(u : nat)(v : Z),(u < n)%nat /\
                    (u = i /\ v = 1 - q * t [i] \/ u ≠ i /\ v = - q * t [u]) \}\ 
                    = \{\ λ(u : nat)(v : Z),(u <= n-1)%nat /\
                    (u = i /\ v = 1 - q * t [i] \/ u ≠ i /\ v = - q * t [u]) \}\).
                    { apply AxiomI; split; intros.
            - apply Property_P in H20. destruct H20, H20, H20. rewrite H20.
              rewrite H20 in H21. apply AxiomII_P. apply -> AxiomII_P in H21.
              simpl in H21. repeat split; try tauto. destruct H21. 
              apply Nat.lt_le_pred in H21. rewrite Nat.sub_1_r. auto. 
            - apply Property_P in H20. destruct H20, H20, H20. rewrite H20.
              rewrite H20 in H21. apply AxiomII_P. apply -> AxiomII_P in H21.
              simpl in H21. repeat split; try tauto. destruct H21. 
              apply le_lt_n_Sm in H21. rewrite Nat.sub_1_r in H21.
              rewrite Nat.succ_pred_pos in H21; auto. } rewrite H20.
              apply Lemma1_4_2g; auto; try red; intros; 
              try apply -> AxiomII in H21; try simpl in H21; try rewrite H1;
              try apply AxiomII; try auto.
              apply le_lt_n_Sm in H21.
              rewrite Nat.sub_1_r in H21. 
              rewrite Nat.succ_pred_pos in H21; auto.
              - exists t[z]. apply x_fx; auto. rewrite H18. apply AxiomII. 
                apply le_lt_n_Sm in H21.
              rewrite Nat.sub_1_r in H21. 
              rewrite Nat.succ_pred_pos in H21; auto.
              - apply AxiomII. auto. rewrite H1 in H10. apply -> AxiomII in H10.
              simpl in H10.
              apply Nat.lt_le_pred in H10. rewrite Nat.sub_1_r. auto.
        -- rewrite <- H15; auto. }
    apply H6 in H15. destruct H13. Z.swap_greater. apply Z.lt_le_incl in H7.
    rewrite Z.abs_eq in H16; auto. apply Zlt_not_le in H16. contradiction. 
    * destruct H13. Z.swap_greater. apply Znot_lt_ge in H14.
      assert (r = 0). { Z.swap_greater; apply Z.le_antisymm; auto. }
      exists q; rewrite H16 in H12. rewrite Z.add_0_r in H12. auto.
  + destruct H5, H11. rewrite H12. apply Lemma1_4_2f; red; intros.
    * rewrite H1; apply AxiomII; apply -> AxiomII in H13; simpl in H13.
      apply le_lt_n_Sm in H13.
      rewrite Nat.sub_1_r in H13; auto. rewrite Nat.succ_pred_pos in H13; auto.
    * rewrite H11; apply AxiomII; apply -> AxiomII in H13; simpl in H13.
      apply le_lt_n_Sm in H13.
      rewrite Nat.sub_1_r in H13; auto. rewrite Nat.succ_pred_pos in H13; auto.
    * assert (i ∈ dom[a]). { rewrite H1; apply AxiomII.
      apply le_lt_n_Sm in H13. rewrite Nat.sub_1_r in H13; auto. 
      rewrite Nat.succ_pred_pos in H13; auto. } apply H10 in H14.
      red in H14; destruct H14. exists x; auto.
Qed.


Theorem Theorem1_4_2' : forall (n : nat) d1 d2 (a : Ensemble (prod nat Z)),
  Function a -> dom[a] = \{ λ u, (u < n)%nat \} ->
  gcd_n a n d1 -> gcd_n a n d2 -> d1 = d2 \/ d1 = -d2.
Proof.
  intros. red in H1, H2. 
  assert (Function a /\ dom[ a] = \{ λ u,(u < n)%nat \}).
  { split; auto. } double H3. apply H1 in H3. apply H2 in H4. clear H1 H2.
  destruct H3, H4. generalize (H2 d2); intros. 
  apply H5 in H3. generalize (H4 d1); intros.
  apply H6 in H1. clear H2 H4 H5 H6. 
  destruct H1, H3. double H1; double H2. rewrite H3 in H4.
  generalize (classic (d1 = 0)); intros. clear H3; destruct H5.
  - rewrite H3 in H1. simpl in H1. rewrite <- H1 in H3. auto.
  - rewrite Zred_factor0 in H4 at 1.
    generalize (Z.mul_reg_l 1 (x*x0) d1); intros. apply H5 in H3; auto.
    + symmetry in H3. apply Z.mul_eq_1 in H3.
      destruct H3. rewrite H3 in H1.
      rewrite Z.mul_1_r in H1. symmetry in H1; auto. simpl in H3. 
      rewrite H3 in H1. generalize (Z.opp_eq_mul_m1 d1); intros.
      rewrite <- H6 in H1. apply Z.eq_opp_l in H1. symmetry in H1; auto.
    + rewrite Z.mul_assoc. auto.
Qed.


Lemma Lemma1_4_3 : forall (n : nat)  (a t : Ensemble (prod nat Z)),
  Function a -> \{λ u, (u <= n)%nat \} ⊂ dom[a] ->
  Function t -> \{λ u, (u <= n)%nat \} ⊂ dom[t] ->
  sum_a_t a \{\ λ (u:nat) v, u ∈ dom[t] /\ v = -t[u] \}\ n = -sum_a_t a t n.
Proof.
  intro n. induction n; intros.
  - simpl. assert ([0%nat, -t[0%nat]] ∈ 
    \{\ λ(u : nat)(v : Z),u ∈ dom[ t] /\ v = - t [u] \}\ ). 
    { apply AxiomII_P. split; auto. apply H2. apply AxiomII. auto. }
    assert (Function \{\ λ(u : nat)(v : Z),u ∈ dom[ t] /\ v = - t [u] \}\).
    { red; intros. apply -> AxiomII_P in H4; apply -> AxiomII_P in H5; 
      simpl in H4; simpl in H5. destruct H4, H5; rewrite <- H7 in H6; auto. }
    apply f_x' in H3; auto. rewrite H3. rewrite Z.mul_opp_r.
    apply Z.opp_inj_wd; auto.
  - simpl. rewrite IHn; auto.
    + assert ([S n, -t[S n]] ∈ 
      \{\ λ(u : nat)(v : Z),u ∈ dom[ t] /\ v = - t [u] \}\). 
      { apply AxiomII_P. split; auto. apply H2; apply AxiomII. auto. }
      assert (Function \{\ λ(u : nat)(v : Z),u ∈ dom[ t] /\ v = - t [u] \}\).
      { red; intros. apply -> AxiomII_P in H4; simpl in H4.
        apply -> AxiomII_P in H5; simpl in H5; destruct H4, H5.
        rewrite <- H7 in H6. auto. }
      apply f_x' in H3; auto.
      rewrite H3. rewrite Z.mul_opp_r. rewrite Z.opp_add_distr. auto.
    + red; intros; apply H0; apply AxiomII. 
      apply -> AxiomII in H3; simpl in H3. auto.
    + red; intros; apply H2; apply AxiomII. 
      apply -> AxiomII in H3; simpl in H3. auto.
Qed.

Theorem Theorem1_4_3 : forall (n: nat) d (a : Ensemble (prod nat Z)),
  (0 < n)%nat -> Function a -> dom[a] = \{ λ u, (u < n)%nat \} -> 
  gcd_n a n d -> exists (t : Ensemble (prod nat Z)), 
  Function t /\ dom[t] = \{ λ u, (u < n)%nat \} /\ sum_a_t a t (n-1)%nat = d.
Proof.
  intros.
  generalize (classic (forall i, i ∈ dom[a] -> a[i] = 0)); intros; destruct H3.
  - assert (gcd_n a n 0). { red. split; auto; intros.
    -- red. apply H3 in H5. exists 0; rewrite H5; auto.
    -- assert (0%nat ∈ dom[a]). { rewrite H1. apply AxiomII. auto. }
       double H6; apply H5 in H6. apply H3 in H7. rewrite H7 in H6. auto. }
    generalize (Theorem1_4_2' n d 0 a). intros.
    assert (d = 0 \/ d = -0). { apply H5; auto. }
    assert (d = 0). { destruct H6; simpl; auto. } clear H6. rewrite H7.
    exists \{\ λ (u:nat) v, (u < n)%nat /\ v = 0 \}\. 
    assert (Function \{\ λ(u : nat)(v : Z),(u < n)%nat /\ v = 0 \}\). {
    red; intros. apply -> AxiomII_P in H6; simpl in H6; 
    apply -> AxiomII_P in H8; simpl in H8; destruct H6, H8. rewrite H10; auto. }
    assert (dom[ \{\ λ(u : nat)(v : Z),(u < n)%nat /\ v = 0 \}\] = 
    \{ λ u,(u < n)%nat \}). {
    apply AxiomI; split; intros; apply -> AxiomII in H8; simpl in H8;
    apply AxiomII.
    - destruct H8; apply -> AxiomII_P in H8; simpl in H8. tauto.
    - exists \{\ λ(u : nat)(v : Z),(u < n)%nat /\ v = 0 \}\[z].
      apply AxiomII_P. split; auto.
      assert ([z, 0] ∈ \{\ λ(u : nat)(v : Z),(u < n)%nat /\ v = 0 \}\). {
      apply AxiomII_P. split; auto. } apply f_x' in H9; auto. }
      repeat split; auto.
    apply Lemma1_4_2; auto. try split; auto. 
    + red; intros. apply -> AxiomII in H9; simpl in H9. 
      rewrite H1; apply AxiomII. apply le_lt_n_Sm in H9. 
      rewrite Nat.sub_1_r in H9. rewrite Nat.succ_pred_pos in H9; auto.
    + split; auto. red; intros. apply -> AxiomII in H9; simpl in H9; 
      apply AxiomII. exists \{\ λ(u : nat)(v : Z),(u < n)%nat /\ v = 0 \}\[z].
      apply AxiomII_P. apply le_lt_n_Sm in H9. 
      rewrite Nat.sub_1_r in H9. rewrite Nat.succ_pred_pos in H9; auto.
      split; auto.
      assert ([z, 0] ∈ \{\ λ(u : nat)(v : Z),(u < n)%nat /\ v = 0 \}\).
      { apply AxiomII_P. split; auto. } apply f_x' in H10; auto.
    + intros. apply le_lt_n_Sm in H9. 
      rewrite Nat.sub_1_r in H9. rewrite Nat.succ_pred_pos in H9; auto.
      assert ([i, 0] ∈ \{\ λ(u : nat)(v : Z),(u < n)%nat /\ v = 0 \}\).
      { apply AxiomII_P. split; auto. } apply f_x' in H10; auto.
  - assert(H4 : exists I, I = \{λ b, exists t, Function t /\
    dom[ t ] = \{λ u, (u < n)%nat \} /\ b = sum_a_t a t (n-1) \}).
    { exists \{λ b, exists t, Function t /\ dom[ t ] = \{λ u, (u < n)%nat \} /\
      b = sum_a_t a t (n-1) \}. auto. } destruct H4 as [I H4].
    assert(H6 : exists I', I' = \{ λ s, s ∈ I /\ s > 0 \}).
    { exists \{ λ s, s ∈ I /\ s > 0 \}; auto. } destruct H6 as [I' H6].
    assert (I' ≠ Φ Z /\ I' ⊂ Z_POS).
    { apply not_all_ex_not in H3. destruct H3 as [i H3].
      apply imply_to_and in H3. destruct H3. split.
      - generalize (Ztrichotomy a[i] 0); intros. 
        destruct H7 as [H7 | [H7 | H7]]; try contradiction.
        + assert ((-a[i]) ∈ I'). { rewrite H6. apply AxiomII. split.
          - rewrite H4. apply AxiomII.
            exists \{\ λ (u:nat) (v:Z), (u < n)%nat /\ ((u=i /\ v=-1) \/ 
            (u≠i /\ v=0)) \}\. 
            assert (Function \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = -1 \/ u ≠ i /\ v = 0) \}\). {
            red; intros. apply -> AxiomII_P in H8; apply -> AxiomII_P in H9.
              destruct H8, H9. destruct H10, H11, H10, H11.
              * rewrite H13; auto.
              * contradiction.
              * contradiction.
              * rewrite H13; auto. }
            assert (dom[ \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = -1 \/ u ≠ i /\ v = 0) \}\] = 
            \{ λ u : nat,(u < n)%nat \} ). { apply AxiomI; split; intros.
            - apply -> AxiomII in H9. simpl in H9. destruct H9.
              apply -> AxiomII_P in H9. simpl in H9. apply AxiomII. tauto.
            - apply AxiomII. exists \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = -1 \/ u ≠ i /\ v = 0) \}\[z]. apply AxiomII_P.
            apply -> AxiomII in H9; simpl in H9. split; auto.
            generalize (classic (z = i)); intros. destruct H10.
              + left. split; auto. assert ([z, -1] ∈ 
              \{\ λ(u : nat)(v : Z),(u < n)%nat /\
              (u = i /\ v = -1 \/ u ≠ i /\ v = 0) \}\). apply AxiomII_P.
              split; auto. apply f_x'; auto.
              + right; split; auto. assert ([z, 0] ∈ 
              \{\ λ(u : nat)(v : Z),(u < n)%nat /\
              (u = i /\ v = -1 \/ u ≠ i /\ v = 0) \}\). apply AxiomII_P.
              split; auto. apply f_x'; auto. } repeat split; auto.
            assert (  \{\
            λ(u : nat)(v : Z),(u < n)%nat /\
            ((u = i /\ v = -1) \/ u ≠ i /\ v = 0) \}\ = 
              \{\  λ(u : nat)(v : Z),(u <= n - 1)%nat /\
              ((u = i /\ v = -1) \/ u ≠ i /\ v = 0) \}\ ).
     { apply AxiomI; split; intros.
      - apply Property_P in H10. destruct H10, H10, H10. rewrite H10.
        rewrite H10 in H11. apply AxiomII_P. apply -> AxiomII_P in H11. simpl
        in H11. repeat split; try tauto. destruct H11. 
        apply Nat.lt_le_pred in H11. rewrite Nat.sub_1_r. auto. 
      - apply Property_P in H10. destruct H10, H10, H10. rewrite H10.
        rewrite H10 in H11. apply AxiomII_P. apply -> AxiomII_P in H11. simpl
        in H11. repeat split; try tauto. destruct H11. 
        apply le_lt_n_Sm in H11. rewrite Nat.sub_1_r in H11.
        rewrite Nat.succ_pred_pos in H11; auto. } rewrite H10.
        assert (-a[i] = -1 * a[i]). { ring. } rewrite H11. 
        apply Lemma1_4_2a.
        + split; auto. red; intros. apply -> AxiomII in H12; simpl in H12.
          rewrite H1. apply AxiomII. apply le_lt_n_Sm in H12. 
          rewrite Nat.sub_1_r in H12. rewrite Nat.succ_pred_pos in H12; auto.
        + rewrite H1 in H3. apply -> AxiomII in H3. simpl in H3.
          apply Nat.lt_le_pred in H3. rewrite Nat.sub_1_r. auto.
      - apply Z.opp_pos_neg in H7. Z.swap_greater; auto. }
    intro. rewrite H9 in H8. generalize (Not_Empty_Z (-a[i])); 
    intros. contradiction.
    + assert (a[i] ∈ I'). { rewrite H6. apply AxiomII. split.
          - rewrite H4. apply AxiomII.
            exists \{\ λ (u:nat) (v:Z), (u < n)%nat /\ ((u=i /\ v=1) \/ 
            (u≠i /\ v=0)) \}\. intros. 
            assert (Function \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = 1 \/ u ≠ i /\ v = 0) \}\). {
            red; intros. apply -> AxiomII_P in H8; apply -> AxiomII_P in H9.
              destruct H8, H9. destruct H10, H11, H10, H11.
              * rewrite H13; auto.
              * contradiction.
              * contradiction.
              * rewrite H13; auto. }
            assert (dom[ \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = 1 \/ u ≠ i /\ v = 0) \}\] = 
            \{ λ u : nat,(u < n)%nat \} ). { apply AxiomI; split; intros.
            - apply -> AxiomII in H9. simpl in H9. destruct H9.
              apply -> AxiomII_P in H9. simpl in H9. apply AxiomII. tauto.
            - apply AxiomII. exists \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
            (u = i /\ v = 1 \/ u ≠ i /\ v = 0) \}\[z]. apply AxiomII_P.
            apply -> AxiomII in H9; simpl in H9. split; auto.
            generalize (classic (z = i)); intros. destruct H10.
              + left. split; auto. assert ([z, 1] ∈ 
              \{\ λ(u : nat)(v : Z),(u < n)%nat /\
              (u = i /\ v = 1 \/ u ≠ i /\ v = 0) \}\). apply AxiomII_P.
              split; auto. apply f_x'; auto.
              + right; split; auto. assert ([z, 0] ∈ 
              \{\ λ(u : nat)(v : Z),(u < n)%nat /\
              (u = i /\ v = 1 \/ u ≠ i /\ v = 0) \}\). apply AxiomII_P.
              split; auto. apply f_x'; auto. } repeat split; auto.
     assert (  \{\ λ(u : nat)(v : Z),(u < n)%nat /\
            ((u = i /\ v = 1) \/ u ≠ i /\ v = 0) \}\ = 
              \{\  λ(u : nat)(v : Z),(u <= n - 1)%nat /\
              ((u = i /\ v = 1) \/ u ≠ i /\ v = 0) \}\ ).
     { apply AxiomI; split; intros.
      - apply Property_P in H10. destruct H10, H10, H10. rewrite H10.
        rewrite H10 in H11. apply AxiomII_P. apply -> AxiomII_P in H11. simpl
        in H11. repeat split; try tauto. destruct H11. 
        apply Nat.lt_le_pred in H11. rewrite Nat.sub_1_r. auto. 
      - apply Property_P in H10. destruct H10, H10, H10. rewrite H10.
        rewrite H10 in H11. apply AxiomII_P. apply -> AxiomII_P in H11. simpl
        in H11. repeat split; try tauto. destruct H11. 
        apply le_lt_n_Sm in H11. rewrite Nat.sub_1_r in H11.
        rewrite Nat.succ_pred_pos in H11; auto. } rewrite H10.
        assert (a[i] = 1 * a[i]). { ring. } rewrite H11. 
        apply Lemma1_4_2a.
        + split; auto. red; intros. apply -> AxiomII in H12; simpl in H12.
          rewrite H1. apply AxiomII. apply le_lt_n_Sm in H12. 
          rewrite Nat.sub_1_r in H12. rewrite Nat.succ_pred_pos in H12; auto.
        + rewrite H1 in H3. apply -> AxiomII in H3. simpl in H3.
          apply Nat.lt_le_pred in H3. rewrite Nat.sub_1_r. auto.
      - auto. }
    intro. rewrite H9 in H8. generalize (Not_Empty_Z (a[i])); 
    intros. contradiction.
  - red; intros. rewrite H6 in H7. apply -> AxiomII in H7; simpl in H7.
    apply AxiomII. tauto. }
  apply MiniMember_Z' in H5. destruct H5 as [d0 H5]. destruct H5. generalize H5.
  intros H77. rewrite H6 in H5. apply -> AxiomII in H5; simpl in H5. destruct H5.
  rewrite H4 in H5; apply -> AxiomII in H5; simpl in H5. destruct H5 as [t H5].
  assert (gcd_n a n d0). { red. intros.
  apply not_all_ex_not in H3. destruct H3 as [i0 H3].
  apply imply_to_and in H3. destruct H3. 
  (* 由带余除法可得ai = d * q + r *)
  split; intros.
  + generalize (Theorem1_4_1 d0 a[i]); intros. assert (d0 ≠ 0). { 
    Z.swap_greater; apply Z.lt_neq in H8. apply not_eq_sym; auto. } 
    apply H12 in H13. destruct H13 as [q [r H13]]. destruct H13. 
    generalize (classic (r > 0)); intros. destruct H15.
    * assert (r ∈ I'). { 
        assert (r = a[i] - d0 * q). { symmetry in H13.
        apply Z.add_move_l in H13. auto. } rewrite H16. rewrite H6.
        apply AxiomII. split.
        -- rewrite H4. apply AxiomII.
           exists ( \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
              ((u = i /\ v = (1 - q * t[i])) \/ (u ≠ i /\ v = - q * t[u])) \}\).
               assert (Function \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
              ((u = i /\ v = (1 - q * t[i])) \/ (u ≠ i /\ v = - q * t[u])) \}\). 
              { red; intros. apply -> AxiomII_P in H17; apply -> AxiomII_P in H18.
                destruct H17, H18. destruct H19, H20, H19, H20.
                * rewrite H22; auto.
                * contradiction.
                * contradiction.
                * rewrite H22; auto. }
               assert(dom[ \{\ λ(u : nat)(v : Z),(u < n)%nat /\
               (u = i /\ v = 1 - q * t [i] \/ u ≠ i /\ v = - q * t [u]) \}\] =
                \{ λ u : nat, (u < n)%nat \}).
                { apply AxiomI; split; intros.
                  - apply -> AxiomII in H18. simpl in H18. destruct H18.
                    apply -> AxiomII_P in H18. simpl in H18. apply AxiomII. tauto.
                  - apply AxiomII. exists \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
                    ((u = i /\ v = (1 - q * t[i])) \/ 
                    (u ≠ i /\ v = - q * t[u])) \}\[z]. 
                    apply AxiomII_P.
                    apply -> AxiomII in H18; simpl in H18. split; auto.
                    generalize (classic (z = i)); intros. destruct H19.
                    + left. split; auto. assert ([z, 1 - q * t [i]] ∈ 
                      \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
                      ((u = i /\ v = (1 - q * t[i])) \/ 
                      (u ≠ i /\ v = - q * t[u])) \}\ ).
                      apply AxiomII_P. split; auto. apply f_x'; auto.
                    + right; split; auto. assert ([z, - q * t [z]] ∈ 
                      \{\ λ(u : nat)(v : Z),(u < n)%nat /\ 
                      ((u = i /\ v = (1 - q * t[i])) \/ 
                      (u ≠ i /\ v = - q * t[u])) \}\).
                      apply AxiomII_P. split; auto. apply f_x'; auto. } 
                      repeat split; auto. destruct H5, H19. rewrite H20.
                      assert (\{\ λ(u : nat)(v : Z),(u < n)%nat /\
                      (u = i /\ v = 1 - q * t [i] \/ u ≠ i /\ v = - q * t [u]) \}\ 
                      = \{\  λ(u : nat)(v : Z),(u <= n-1)%nat /\
                      (u = i /\ v = 1 - q * t [i] \/ u ≠ i /\ v = - q * t [u]) \}\).
                      { apply AxiomI; split; intros.
            - apply Property_P in H21. destruct H21, H21, H21. rewrite H21.
              rewrite H21 in H22. apply AxiomII_P. apply -> AxiomII_P in H22.
              simpl in H22. repeat split; try tauto. destruct H22. 
              apply Nat.lt_le_pred in H22. rewrite Nat.sub_1_r. auto. 
            - apply Property_P in H21. destruct H21, H21, H21. rewrite H21.
              rewrite H21 in H22. apply AxiomII_P. apply -> AxiomII_P in H22.
              simpl in H22. repeat split; try tauto. destruct H22. 
              apply le_lt_n_Sm in H22. rewrite Nat.sub_1_r in H22.
              rewrite Nat.succ_pred_pos in H22; auto. } 
              rewrite H21. apply Lemma1_4_2g; auto; try red; intros; 
              try apply -> AxiomII in H22; try simpl in H22; try rewrite H1;
              try apply AxiomII; try auto. 
              apply le_lt_n_Sm in H22.
              rewrite Nat.sub_1_r in H22. 
              rewrite Nat.succ_pred_pos in H22; auto.
              - exists t[z]. apply x_fx; auto. rewrite H19. apply AxiomII. 
                apply le_lt_n_Sm in H22. 
              rewrite Nat.sub_1_r in H22. 
              rewrite Nat.succ_pred_pos in H22; auto.
              - apply AxiomII. auto. rewrite H1 in H11. apply -> AxiomII in H11.
              simpl in H11. 
              apply Nat.lt_le_pred in H11. rewrite Nat.sub_1_r. auto.
        -- rewrite <- H16; auto. } 
    apply H7 in H16. destruct H14. Z.swap_greater. apply Z.lt_le_incl in H8.
    rewrite Z.abs_eq in H17; auto. apply Zlt_not_le in H17. contradiction. 
    * destruct H14. Z.swap_greater. apply Znot_lt_ge in H15.
      assert (r = 0). { Z.swap_greater; apply Z.le_antisymm; auto. }
      exists q; rewrite H17 in H13. rewrite Z.add_0_r in H13. auto.
  + destruct H5, H12. rewrite H13. apply Lemma1_4_2f; red; intros.
    * rewrite H1; apply AxiomII; apply -> AxiomII in H14; simpl in H14.
      apply le_lt_n_Sm in H14.
      rewrite Nat.sub_1_r in H14; auto. rewrite Nat.succ_pred_pos in H14; auto.
    * rewrite H12; apply AxiomII; apply -> AxiomII in H14; simpl in H14.
      apply le_lt_n_Sm in H14.
      rewrite Nat.sub_1_r in H14; auto. rewrite Nat.succ_pred_pos in H14; auto.
    * assert (i ∈ dom[a]). { rewrite H1; apply AxiomII.
      apply le_lt_n_Sm in H14. rewrite Nat.sub_1_r in H14; auto. 
      rewrite Nat.succ_pred_pos in H14; auto. } apply H11 in H15.
      red in H15; destruct H15. exists x; auto. }
  generalize (Theorem1_4_2' n d d0 a). intros.
  assert (d = d0 \/ d = -d0). { apply H10; auto. } destruct H11.
  + rewrite H6 in H77. apply -> AxiomII in H77; simpl in H77. destruct H77.
    rewrite H4 in H12. apply -> AxiomII in H12; simpl in H12. destruct H12.
    exists t.
    assert (Function t). { tauto. }
    assert (dom[ t] = \{ λ u,(u < n)%nat \}). { tauto. } repeat split; auto.
    intros. destruct H5, H16. rewrite H11. symmetry; auto.
  + assert ((-d0) ∈ I). 
    { rewrite H6 in H77. apply -> AxiomII in H77; simpl in H77. destruct H77.
      rewrite H4 in H12. apply -> AxiomII in H12; simpl in H12. destruct H12.
      rewrite H4. apply AxiomII. 
      exists \{\ λ (u:nat) v, u ∈ dom[x] /\ v = -x[u] \}\. 
      assert (Function \{\ λ (u:nat) v, u ∈ dom[x] /\ v = -x[u] \}\). 
      { red; intros. apply -> AxiomII_P in H14; simpl in H14; 
        apply -> AxiomII_P in H15; simpl in H15. destruct H14, H15. 
        rewrite <- H17 in H16; auto. } 
      repeat split; auto.
      * apply AxiomI; split; intros; apply -> AxiomII in H15; simpl in H15;
        apply AxiomII. 
        -- destruct H15. apply -> AxiomII_P in H15; simpl in H15. 
           destruct H15. destruct H12, H17. rewrite H17 in H15.
           apply -> AxiomII in H15; simpl in H15. auto.
        -- exists \{\ λ(u : nat)(v : Z),u ∈ dom[x] /\ v = - x [u] \}\[z].
           apply AxiomII_P. split. destruct H12, H16. rewrite H16.
           apply AxiomII. auto.
           assert ([z, -x[z]] ∈
           \{\ λ(u : nat)(v : Z),u ∈ dom[x] /\ v = - x [u] \}\). 
           { apply AxiomII_P. split; auto. destruct H12, H16. rewrite H16;
             apply AxiomII. auto. }
           apply f_x' in H16; auto.
      * destruct H12, H15. rewrite H16. symmetry. apply Lemma1_4_3; auto;
        red; intros.
        -- apply -> AxiomII in H17; simpl in H17. rewrite H1; apply AxiomII.
           apply le_lt_n_Sm in H17. rewrite Nat.sub_1_r in H17.
           rewrite Nat.succ_pred_pos in H17; auto.
        -- apply -> AxiomII in H17; simpl in H17. rewrite H15; apply AxiomII.
           apply le_lt_n_Sm in H17. rewrite Nat.sub_1_r in H17.
           rewrite Nat.succ_pred_pos in H17; auto. }
     rewrite H4 in H12. apply -> AxiomII in H12; simpl in H12. destruct H12.
     exists x. intros. repeat split; try tauto. 
     rewrite H11; symmetry; tauto.
Qed.


(* 定义互素 *)
Definition prime_n (n : nat) (a : Ensemble (prod nat Z)) := gcd_n a n 1.

Theorem Theorem1_4_4 : forall (n : nat) (a : Ensemble (prod nat Z)), 
  (forall d, gcd_n a n d -> d >= 0) ->
  (0 < n)%nat -> Function a ->dom[a] = \{ λ u, (u < n)%nat \} ->
  (prime_n n a <-> exists (t : Ensemble (prod nat Z)), 
  Function t /\ dom[t] = \{ λ u, (u < n)%nat \} /\ sum_a_t a t (n-1)%nat = 1).
Proof.
  intros. split; intros.
  - generalize (Theorem1_4_3 n 1 a); intros. apply H4 in H0; auto. 
  - destruct H3, H3, H4. red. generalize (Theorem1_4_2 n a); intros.
    assert (∃d : Z,gcd_n a n d). { apply H6. split; auto. } clear H6.
    destruct H7 as [c H7]. 
    assert (exa_div c 1). { rewrite <- H5. apply Lemma1_4_2f; 
    try red; intros; try apply -> AxiomII in H6; simpl in H6.
    + rewrite H2; apply AxiomII. rewrite Nat.sub_1_r in H6.
      apply le_lt_n_Sm in H6. rewrite Nat.succ_pred_pos in H6; auto.
    + rewrite H4; apply AxiomII. rewrite Nat.sub_1_r in H6.
      apply le_lt_n_Sm in H6. rewrite Nat.succ_pred_pos in H6; auto.
    + assert (Function a /\ dom[ a] = \{ λ u,(u < n)%nat \}). { split; auto. }
      red in H7. apply H7 in H8. clear H7. destruct H8.
      assert (i ∈ dom[a]). { rewrite H2; apply AxiomII. 
      rewrite Nat.sub_1_r in H6. apply le_lt_n_Sm in H6. 
      rewrite Nat.succ_pred_pos in H6; auto. } apply H7 in H9. 
      red in H9; auto. } red in H6. destruct H6.
      symmetry in H6. apply Z.mul_eq_1 in H6. destruct H6; subst c; auto.
      apply H in H7. contradiction.
Qed.

(* 定义素数 *)
Definition prime p := p >1 /\ 
  (forall c, exa_div c p -> c = 1 \/ c = p \/ c = -1 \/ c = -p).
(* Definition prime p := p >1 /\ 
  (forall c, exa_div c p -> c = 1 \/ c = p ). *)


Lemma Lemma1_4_5a : forall p b (a : Ensemble (prod nat Z)),
  Function a ->  dom[a] = \{ λ u, (u<2)%nat \} ->
  prime p -> a = \{\ λ (u : nat) v, u=0%nat/\v=p \/ u=1%nat/\v=b \}\ ->
  ~exa_div p b -> gcd_n a 2%nat 1.
Proof.
  intros. red. intros. split; intros.
  - red. exists a[i]; ring.
  - assert (0%nat ∈ dom[a]).
    { rewrite H0; apply AxiomII. auto. }
    apply H5 in H6. assert ([0%nat, p] ∈ a).
    { rewrite H2. apply AxiomII_P. auto. }
    apply f_x' in H7; auto. rewrite H7 in H6.
    red in H1. destruct H1. apply H8 in H6. destruct H6.
    + subst c; red; exists 1; auto.
    + destruct H6.
      * assert (exa_div p b).
        { assert (1%nat ∈ dom[a]).
          { rewrite H0; apply AxiomII; auto. }
          apply H5 in H9. assert ([1%nat, b] ∈ a).
          { rewrite H2. apply AxiomII_P. auto. }
          apply f_x' in H10; auto. rewrite H10 in H9.
          rewrite H6 in H9. auto. }
        contradiction.
      * destruct H6.
        -- subst c; red; exists(-1); auto.
        -- assert (exa_div (-p) b).
           { assert (1%nat ∈ dom[a]).
             { rewrite H0; apply AxiomII; auto. }
             apply H5 in H9. assert ([1%nat, b] ∈ a).
             { rewrite H2. apply AxiomII_P. auto. }
             apply f_x' in H10; auto. rewrite H10 in H9.
             rewrite H6 in H9. auto. }
           assert (exa_div p b).
           { red in H9; destruct H9. red. exists(-x).
            rewrite <- Z.mul_opp_comm; auto. }
           contradiction.
Qed.


(* 定理1.4.5 *)
Theorem Theorem1_4_5 : forall (p a b : Z) (t : Ensemble (prod nat Z)),
  Function t -> dom[t] = \{ λ u, (u<2)%nat \} ->
  (forall d (t' : Ensemble (prod nat Z)), gcd_n t' 2%nat d -> d >= 0) ->
  prime p -> exa_div p (a*b) -> exa_div p a \/ exa_div p b.
Proof.
  intros. generalize (classic (exa_div p a)); intros; destruct H4; auto. right.
  assert (exists t, t = \{\ λ (u : nat) v, u=0%nat/\v=p \/ u=1%nat/\v=a \}\ ).
  { exists \{\ λ (u : nat) v, u=0%nat/\v=p \/ u=1%nat/\v=a \}\; auto. }
  destruct H5 as [t1 H5]. generalize (Lemma1_4_5a p a t1); intros.
  assert (Function t1).
  { red; intros. rewrite H5 in H7; rewrite H5 in H8.
    apply -> AxiomII_P in H7; apply -> AxiomII_P in H8.
    simpl in H7; simpl in H8. destruct H7, H8, H7, H8.
    - rewrite H10; auto.
    - rewrite H7 in H8. assert (0%nat <> 1%nat). { auto. } contradiction.
    - rewrite H7 in H8. assert (1%nat <> 0%nat). { auto. } contradiction.
    - rewrite H10; auto. }
  assert (dom[t1] = \{ λ u,(u < 2)%nat \}).
  { apply AxiomI; split; intros.
    - apply -> AxiomII in H8; simpl in H8. destruct H8.
      rewrite H5 in H8. apply -> AxiomII_P in H8; simpl in H8.
      apply AxiomII. destruct H8, H8; rewrite H8; auto.
    - apply AxiomII. exists t1[z]. rewrite H5; apply AxiomII_P.
      apply -> AxiomII in H8; simpl in H8. 
      assert (z = 0 \/ z = 1)%nat.
      { apply Nat.lt_le_pred in H8. simpl in H8. apply Nat.le_1_r in H8. auto. }
      destruct H9.
      + left. split; auto. assert ([z, p] ∈ t1).
        { rewrite H5; apply AxiomII_P. auto. }
        rewrite <- H5. apply f_x' in H10; auto.
      + right. split; auto. assert ([z, a] ∈ t1).
        { rewrite H5; apply AxiomII_P. auto. }
        rewrite <- H5. apply f_x' in H10; auto. }
  assert (gcd_n t1 2 1). { apply H6; auto. }
  assert (prime_n 2 t1). { red. auto. }
  apply Theorem1_4_4 in H9; auto.
  - destruct H9, H9, H11. simpl in H12.
    assert (t1[0%nat] = p /\ t1[1%nat] = a).
    { split.
      + assert ([0%nat, p] ∈ t1). { rewrite H5; apply AxiomII_P. auto. }
        apply f_x' in H13; auto.
      + assert ([1%nat, a] ∈ t1). { rewrite H5; apply AxiomII_P. auto. }
        apply f_x' in H13; auto. }
    destruct H13. rewrite H13 in H12.
    rewrite H14 in H12. rewrite Z.mul_comm in H12.
    pattern (a * x [1%nat]) in H12; rewrite Z.mul_comm in H12.
    assert (x [0%nat] * p * b + x [1%nat] * a * b = b). 
    { generalize (Z.mul_comm (x [0%nat] * p) b); intros. rewrite H15.
      generalize (Z.mul_comm (x [1%nat] * a) b); intros. rewrite H16.
      generalize (Zred_factor4 b (x [0%nat] * p) (x [1%nat] * a)); intros.
      rewrite H17. rewrite H12. ring. }
    rewrite <- H15. apply Lemma1_4_2d.
    * red. exists (x[0%nat]*b). ring.
    * rewrite <- Z.mul_assoc. apply Lemma1_4_2e. auto.
  - intros; apply H1 in H12; auto.
Qed.

End H14.
Export H14.























