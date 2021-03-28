Require Export H1_5.

Module Section2_1.

Fixpoint sum_a_powx (a : Ensemble (prod nat R))
  (x : R)(n : nat){struct n} : R :=
  match n with
  | O => a[O]
  | S p => sum_a_powx a x p + a[n] * pow x n
  end.


Definition Full (A : Type) := \{λ x : A, x = x \}.

(* 定义1：文字x的多项式 *)
Definition Polynomial (a : Ensemble (prod nat R)) := 
  Function a /\ dom[a] = Full nat /\
  exists n : nat, forall m : nat, (m > n)%nat -> a[m] = 0.

(* 定义2：多项式相等 *)
Definition Polynomial_Equal (f g : Ensemble (prod nat R)) :=
  Polynomial f /\ Polynomial g /\ 
  forall n : nat, n ∈ (Full nat) -> f[n] = g[n].

(* 定义3：多项式的次数 *)
Definition Polynomial_Degree (a : Ensemble (prod nat R)) (n : nat) :=
  Polynomial a /\ a[n] ≠ 0 /\ forall m, (m > n)%nat -> a[m] = 0.
Axiom Equal_Degree : forall(f : Ensemble (prod nat R)) (n m : nat),
  Polynomial_Degree f n -> Polynomial_Degree f m -> n = m.

(* 定义多项式的加 *)
Definition Poly_Add (f g : Ensemble (prod nat R)) :=
  \{\ λ (u : nat) v, v = f[u] + g[u] \}\.

Fixpoint sum (a : Ensemble (prod nat R)) (n : nat) {struct n} :=
  match n with
  | O => a[O]
  | S n' => sum a n' + a[n]
  end.

Definition Ck (f g : Ensemble (prod nat R)) (k : nat) := 
  sum \{\ λ (u:nat) v, v = f[u] * g[(k-u)%nat] \}\ k.

(* 定义多项式的乘 *)
Definition Poly_Mult (f g : Ensemble (prod nat R)) :=
  \{\ λ (u : nat) v, v = (Ck f g u) \}\.

(* 定义负多项式 *)
Definition Poly_neg (f : Ensemble (prod nat R)) :=
  \{\ λ (u : nat) v, v = - f[u] \}\.

(* 定义多项式乘系数 *)
Definition a_mult (f : Ensemble (prod nat R))(c : R) :=
  \{\ λ (u : nat) v, v = c * f[u] \}\.
(* 定义多项式的减 *)
(* Definition Poly_Sub (f g : Ensemble (prod nat R)) :=
    \{\ λ (u : nat) v, v = f[u] - g[u] \}\. *)
Definition Poly_Sub (f g : Ensemble (prod nat R)) :=
  Poly_Add f (Poly_neg g).

(* 多项式加法交换律 *)
Lemma Poly_Add_comm (f g : Ensemble (prod nat R)) :
  Poly_Add f g = Poly_Add g f.
Proof.
  apply AxiomI; intros; split; intros;
  apply Property_P in H; destruct H, H, H; rewrite H in H0;
  apply -> AxiomII_P in H0; simpl in H0; rewrite H;
  apply AxiomII_P; rewrite Rplus_comm; tauto.
Qed.

Lemma Poly_Add_a (f g : Ensemble (prod nat R)) :
  Function f -> Function g -> Function (Poly_Add f g).
Proof.
  intros. red; intros.
  apply -> AxiomII_P in H1; simpl in H1.
  apply -> AxiomII_P in H2; simpl in H2.
  destruct H1, H2. auto.
Qed.

Lemma Poly_Mult_cc (f g : Ensemble (prod nat R)) :
  Polynomial f -> Polynomial g -> Polynomial (Poly_Mult f g).
Proof.
Admitted.

Lemma Poly_Add_b (f g : Ensemble (prod nat R)) :
  Function f -> Function g ->
  (forall x : nat, x ∈ (Full nat) -> (Poly_Add f g)[x] = f[x] + g[x]).
Proof.
  intros. assert (Function (Poly_Add f g)). { apply Poly_Add_a; auto. }
  assert ([x, f[x]+g[x]] ∈ (Poly_Add f g)).
  { apply AxiomII_P. split; auto. }
  apply f_x' in H3; auto.
Qed.

(* 多项式加法结合律 *)
Lemma Poly_Add_assoc (f g h: Ensemble (prod nat R)) :
  Function f -> Function g -> Function h ->
  Poly_Add (Poly_Add f g) h = Poly_Add f (Poly_Add g h).
Proof.
  intros; apply AxiomI; split; intros.
  - apply Property_P in H2. destruct H2, H2, H2.
    rewrite H2 in *. apply -> AxiomII_P in H3; simpl in H3.
    apply AxiomII_P.
    rewrite Poly_Add_b in H3; auto. rewrite Poly_Add_b; auto.
    + rewrite H3. rewrite Rplus_assoc. auto.
    + apply AxiomII. auto.
    + apply AxiomII. auto.
  - apply Property_P in H2. destruct H2, H2, H2.
    rewrite H2 in *. apply -> AxiomII_P in H3; simpl in H3.
    apply AxiomII_P.
    rewrite Poly_Add_b in H3; auto. rewrite Poly_Add_b; auto.
    + rewrite H3. rewrite Rplus_assoc. auto.
    + apply AxiomII. auto.
    + apply AxiomII. auto.
Qed.

Lemma Poly_Add_Sub (f: Ensemble (prod nat R)) :
  Poly_Add (Poly_neg f) f = \{\ λ(u : nat)(v : R), v = 0 \}\.
Proof.
  unfold Poly_neg. unfold Poly_Add.
  apply AxiomI; split; intros.
  - destruct z. apply -> AxiomII_P in H; simpl in H.
    assert( - f[x] = \{\ λ(u0 : nat)(v0 : R),v0 = - f [u0] \}\ [x]).
    { intros. 
      assert([x,(- f[x])] ∈ \{\ λ(u0 : nat)(v0 : R),v0 = - f [u0] \}\).
      { apply AxiomII_P. auto. }
      apply f_x' in H0; auto.
      red; intros.
      apply -> AxiomII_P in H2; simpl in H2.
      apply -> AxiomII_P in H1; simpl in H1.
      rewrite H2; rewrite H1; auto. }
    rewrite <- H0 in H. rewrite Rplus_comm in H.
    rewrite Rplus_opp_r in H.
    apply AxiomII_P; auto.
  - destruct z. apply -> AxiomII_P in H; simpl in H.
    apply AxiomII_P; simpl.
    assert( - f[x] = \{\ λ(u0 : nat)(v0 : R),v0 = - f [u0] \}\ [x]).
    { intros. 
      assert([x,(- f[x])] ∈ \{\ λ(u0 : nat)(v0 : R),v0 = - f [u0] \}\).
      { apply AxiomII_P. auto. }
      apply f_x' in H0; auto.
      red; intros.
      apply -> AxiomII_P in H2; simpl in H2.
      apply -> AxiomII_P in H1; simpl in H1.
      rewrite H2; rewrite H1; auto. }
    rewrite <- H0. rewrite Rplus_comm. rewrite Rplus_opp_r; auto.
Qed.

Fixpoint sum_rev (a : Ensemble (prod nat R)) (n k: nat) {struct k} :=
  match k with
  | O => a[n]
  | S k' => a[(n-k)%nat] + sum_rev a n k'  
  end.

Lemma Poly_Mult_a (a : Ensemble (prod nat R)) :
  forall k n : nat,
  sum_rev a n k + a[S n] = sum_rev a (S n) (S k).
Proof.
  intro k. induction k.
  - intros. simpl. assert ((n-0)%nat = n). { lia. }
    rewrite H; auto.
  - intros. simpl. generalize (IHk n); intros.
    rewrite Rplus_assoc. rewrite H. simpl. auto.
Qed.

Lemma Poly_Mult_b (a : Ensemble (prod nat R)) (n : nat) :
  sum a n = sum_rev a n n.
Proof.
  induction n.
  - simpl. auto.
  - rewrite <- Poly_Mult_a. simpl. rewrite IHn. auto.
Qed.

(* 多项式乘法交换律 *)
Lemma Poly_Mult_comm (f g : Ensemble (prod nat R)) : 
  Poly_Mult f g = Poly_Mult g f.
Proof.
  apply AxiomI; intros; split; intros.
  - apply Property_P in H; destruct H, H, H.
    rewrite H in *. apply -> AxiomII_P in H0.
    simpl in H0. apply AxiomII_P. 
    assert (forall x : nat, Ck f g x = Ck g f x). {
    intro k. unfold Ck.
    assert (\{\ λ(u : nat)(v : R),v = g [u] * f [(k - u)%nat] \}\
    = \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\). {
    apply AxiomI; split; intros.
    - apply Property_P in H1; destruct H1, H1, H1. rewrite H1 in *.
      apply -> AxiomII_P in H2; simpl in H2. apply AxiomII_P.
      rewrite H2; field.
    - apply Property_P in H1; destruct H1, H1, H1. rewrite H1 in *.
      apply -> AxiomII_P in H2; simpl in H2. apply AxiomII_P.
      rewrite H2; field. } rewrite H1; clear H1.
    assert (forall n : nat, (n <= k)%nat ->
    sum \{\ λ(u : nat)(v : R),v = f [u] * g [(k - u)%nat] \}\ n
    = sum_rev \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\ k n ).
    { intro n. induction n.
      - intros H77; simpl.
        assert ([0%nat, f[0%nat]*g[k]] ∈ 
        \{\ λ(u : nat)(v : R),v = f [u] * g [(k - u)%nat] \}\ ). {
        apply AxiomII_P. assert ((k-0)%nat = k). { lia. }
        rewrite H1. auto. }
        assert (Function \{\ λ(u : nat)(v : R),v = f [u] * g [(k - u)%nat] \}\).
        { red; intros. apply -> AxiomII_P in H2; apply -> AxiomII_P in H3;
        simpl in H2; simpl in H3. rewrite H3; auto. }
        apply f_x' in H1; auto.
        assert ([k, f[0%nat]*g[k]] ∈ 
        \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\ ). {
        apply AxiomII_P. assert ((k-k) = 0)%nat. { lia. }
        rewrite H3. field. }
        assert (Function \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\).
        { red; intros. apply -> AxiomII_P in H4; apply -> AxiomII_P in H5;
        simpl in H4; simpl in H5. rewrite H4; auto. }
        apply f_x' in H3; auto. 
        rewrite H1; rewrite H3; auto.
      - intros H77; simpl.
        assert ([S n, f[S n]*g[(k - S n)%nat]] ∈ 
        \{\ λ(u : nat)(v : R),v = f [u] * g [(k - u)%nat] \}\ ). {
        apply AxiomII_P.  auto. }
        assert (Function \{\ λ(u : nat)(v : R),v = f [u] * g [(k - u)%nat] \}\).
        { red; intros. apply -> AxiomII_P in H2; apply -> AxiomII_P in H3;
        simpl in H2; simpl in H3. rewrite H3; auto. }
        apply f_x' in H1; auto.
        assert ([(k - S n)%nat, f[S n]*g[(k - S n)%nat]] ∈ 
        \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\ ). {
        apply AxiomII_P. assert ((k - (k - S n))%nat = S n). { lia. }
        rewrite H3. auto. }
        assert (Function \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\).
        { red; intros. apply -> AxiomII_P in H4; apply -> AxiomII_P in H5;
        simpl in H4; simpl in H5. rewrite H4; auto. }
        apply f_x' in H3; auto. 
        rewrite H1; rewrite H3; rewrite IHn.
        apply Rplus_comm. lia. } rewrite H1. symmetry.
        apply Poly_Mult_b. lia. } rewrite H0; apply H1.
  - apply Property_P in H; destruct H, H, H.
    rewrite H in *. apply -> AxiomII_P in H0.
    simpl in H0. apply AxiomII_P. 
    assert (forall x : nat, Ck f g x = Ck g f x). {
    intro k. unfold Ck.
    assert (\{\ λ(u : nat)(v : R),v = g [u] * f [(k - u)%nat] \}\
    = \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\). {
    apply AxiomI; split; intros.
    - apply Property_P in H1; destruct H1, H1, H1. rewrite H1 in *.
      apply -> AxiomII_P in H2; simpl in H2. apply AxiomII_P.
      rewrite H2; field.
    - apply Property_P in H1; destruct H1, H1, H1. rewrite H1 in *.
      apply -> AxiomII_P in H2; simpl in H2. apply AxiomII_P.
      rewrite H2; field. } rewrite H1; clear H1.
    assert (forall n : nat, (n <= k)%nat ->
    sum \{\ λ(u : nat)(v : R),v = f [u] * g [(k - u)%nat] \}\ n
    = sum_rev \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\ k n ).
    { intro n. induction n.
      - intros H77; simpl.
        assert ([0%nat, f[0%nat]*g[k]] ∈ 
        \{\ λ(u : nat)(v : R),v = f [u] * g [(k - u)%nat] \}\ ). {
        apply AxiomII_P. assert ((k-0)%nat = k). { lia. }
        rewrite H1. auto. }
        assert (Function \{\ λ(u : nat)(v : R),v = f [u] * g [(k - u)%nat] \}\).
        { red; intros. apply -> AxiomII_P in H2; apply -> AxiomII_P in H3;
        simpl in H2; simpl in H3. rewrite H3; auto. }
        apply f_x' in H1; auto.
        assert ([k, f[0%nat]*g[k]] ∈ 
        \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\ ). {
        apply AxiomII_P. assert ((k-k) = 0)%nat. { lia. }
        rewrite H3. field. }
        assert (Function \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\).
        { red; intros. apply -> AxiomII_P in H4; apply -> AxiomII_P in H5;
        simpl in H4; simpl in H5. rewrite H4; auto. }
        apply f_x' in H3; auto. 
        rewrite H1; rewrite H3; auto.
      - intros H77; simpl.
        assert ([S n, f[S n]*g[(k - S n)%nat]] ∈ 
        \{\ λ(u : nat)(v : R),v = f [u] * g [(k - u)%nat] \}\ ). {
        apply AxiomII_P.  auto. }
        assert (Function \{\ λ(u : nat)(v : R),v = f [u] * g [(k - u)%nat] \}\).
        { red; intros. apply -> AxiomII_P in H2; apply -> AxiomII_P in H3;
        simpl in H2; simpl in H3. rewrite H3; auto. }
        apply f_x' in H1; auto.
        assert ([(k - S n)%nat, f[S n]*g[(k - S n)%nat]] ∈ 
        \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\ ). {
        apply AxiomII_P. assert ((k - (k - S n))%nat = S n). { lia. }
        rewrite H3. auto. }
        assert (Function \{\ λ(u : nat)(v : R),v = f [(k - u)%nat] * g [u] \}\).
        { red; intros. apply -> AxiomII_P in H4; apply -> AxiomII_P in H5;
        simpl in H4; simpl in H5. rewrite H4; auto. }
        apply f_x' in H3; auto. 
        rewrite H1; rewrite H3; rewrite IHn.
        apply Rplus_comm. lia. } rewrite H1. symmetry.
        apply Poly_Mult_b. lia. } rewrite H0. generalize (H1 x); intros.
        rewrite H2; auto.
Qed.

(* 定理2.1.1 *)

(* 两个多项式和的次数小于等于这两个多项式次数的最大值 *)
Theorem Theorem2_1_1a : forall (f g: Ensemble (prod nat R)) (n m : nat),
  (Polynomial_Degree f n) -> (Polynomial_Degree g m) ->
  (forall q : nat, Polynomial_Degree (Poly_Add f g) q -> 
  (q <= Nat.max n m)%nat).
Proof.
  intros.
  red in H, H0, H1. destruct H, H0, H1, H2, H3, H4.
  generalize (classic (n > m)%nat); intros. destruct H8.
  - assert (Nat.max n m = n). { apply Nat.lt_le_incl in H8.
    apply Nat.max_l in H8. auto. } rewrite H9.
    generalize (classic (q0 <= n)%nat); intros; destruct H10; auto.
    apply not_le in H10. 
    assert (q0 > m)%nat. { lia. }
    apply H5 in H10. apply H6 in H11. red in H, H0.
    assert ((Poly_Add f g)[q0] = f[q0] + g[q0]). {
    apply Poly_Add_b; try tauto. apply AxiomII; auto. }
    rewrite H10 in H12. rewrite H11 in H12. rewrite Rplus_0_l in H12.
    contradiction.
  - apply not_lt in H8. assert (Nat.max n m = m). {
    apply Nat.max_r in H8. auto. } rewrite H9.
    generalize (classic (q0 <= m)%nat); intros; destruct H10; auto.
    apply not_le in H10.
    assert (q0 > n)%nat. { lia. }
    apply H5 in H11. apply H6 in H10. red in H, H0.
    assert ((Poly_Add f g)[q0] = f[q0] + g[q0]). {
    apply Poly_Add_b; try tauto. apply AxiomII; auto. }
    rewrite H10 in H12. rewrite H11 in H12. rewrite Rplus_0_l in H12.
    contradiction.
Qed.

Lemma Lemma2_1_1b' : forall (f : Ensemble (prod nat R)) (n: nat),
  (forall x : nat, (x <= n)%nat -> f[x] = 0) -> sum f n = 0.
Proof.
  intros; induction n.
  - simpl; auto.
  - assert(sum f (S n) = sum f n + f[S n]). { simpl; auto. }
    rewrite H0. rewrite H; auto. rewrite IHn; auto. ring.
Qed.

Lemma Lemma2_1_1b'' : forall(n i: nat) (f : Ensemble (prod nat R)) ,
  (i <= n)%nat -> (forall x : nat, (x ≠ i) -> (x <= n)%nat -> f[x] = 0) ->
  sum f n = f[i].
Proof.
  intro n. induction n.
  - intros. assert(i = 0)%nat. { lia. } rewrite H1. simpl. auto.
  - intros. simpl. 
    apply le_lt_or_eq in H; destruct H.
    + rewrite H0; auto.
      assert(sum f n + 0 = sum f n). { ring. } rewrite H1. apply IHn; auto.
      lia. intro. rewrite H1 in H. eapply Nat.lt_irrefl. eauto.
    + rewrite Lemma2_1_1b'; auto. rewrite H. ring.
      intros. apply H0; auto. intro. rewrite <- H2 in H. rewrite H in H1.
      eapply Nat.nle_succ_diag_l; eauto.
Qed.

(* 两个多项式乘积的次数等于两个多项式的次数之和 *)
Theorem Theorem2_1_1b : forall (f g: Ensemble (prod nat R)) (n m : nat),
  (Polynomial_Degree f n) -> (Polynomial_Degree g m) ->
  Polynomial_Degree (Poly_Mult f g) (n+m).
Proof.
  intros. red in H, H0. destruct H, H0, H1, H2.
  assert (Function (Poly_Mult f g)). {
  red; intros. 
  apply -> AxiomII_P in H5; simpl in H5.
  apply -> AxiomII_P in H6; simpl in H6.
  rewrite H6; auto. }
  red. repeat split; auto.
  - apply AxiomI; split; intros.
    + apply AxiomII. auto.
    + apply AxiomII. exists ((Poly_Mult f g)[z]).
      apply AxiomII_P. assert ([z, Ck f g z] ∈ (Poly_Mult f g)). {
      apply AxiomII_P. auto. } apply f_x' in H7; auto.
  - exists (n+m)%nat. intros.
    assert ([m0, 0] ∈ (Poly_Mult f g)). {
    apply AxiomII_P. unfold Ck.
    assert (exists a, 
    \{\ λ(u : nat)(v : R),v = f [u] * g [(m0 - u)%nat] \}\ = a). {
    exists \{\ λ(u : nat)(v : R),v = f [u] * g [(m0 - u)%nat] \}\. auto. }
    destruct H7 as [t H7]. rewrite H7. 
    assert (Function t). { red; intros. rewrite <- H7 in *.
    apply -> AxiomII_P in H8; simpl in H8.
    apply -> AxiomII_P in H9; simpl in H9. 
    rewrite H9; auto. }
    assert (m0 > n /\ m0 > m)%nat. { split; lia. } destruct H9.
    assert (forall x : nat, sum t x = 0). {
    intro x; induction x; intros.
    - simpl. assert ([0%nat, 0] ∈ t). { rewrite <- H7.
      apply AxiomII_P. assert ((m0 - 0) = m0)%nat. { lia. } rewrite H11.
      apply H4 in H10. rewrite H10. ring. } apply f_x' in H11; auto.
    - simpl. rewrite IHx. assert ([S x, 0] ∈ t). {
      rewrite <- H7. apply AxiomII_P.
      generalize (classic ( S x > n)%nat); intros; destruct H11.
      + apply H3 in H11. rewrite H11; ring.
      + assert ((m0 - S x) > m)%nat. { lia. }
        apply H4 in H12. rewrite H12; ring. }
      apply f_x' in H11; auto. rewrite H11; ring. }
    symmetry; apply H11. }
    apply f_x' in H7; auto.
  - assert ([(n + m)%nat, f[n]*g[m]] ∈ (Poly_Mult f g)). {
    apply AxiomII_P. unfold Ck. symmetry. 
    assert (exists a, \{\ λ(u : nat)(v : R),
    v = f [u] * g [(n + m - u)%nat] \}\ = a). {
    exists \{\ λ(u : nat)(v : R),v = f [u] * g [(n + m - u)%nat] \}\; auto. }
    destruct H6 as [a H6]. rewrite H6.
    assert ([n, f[n]*g[m]] ∈ a). { rewrite <- H6; apply AxiomII_P.
    assert ((n+m-n) = m)%nat. { lia. } rewrite H7. auto. }
    assert (Function a). { red; intros. rewrite <- H6 in *.
    apply -> AxiomII_P in H8; simpl in H8.
    apply -> AxiomII_P in H9; simpl in H9.
    rewrite H9; auto. }
    apply f_x' in H7; auto. rewrite <- H7.
    apply Lemma2_1_1b''; try lia. 
    intro x. induction x.
    - intros. assert ([0%nat, 0] ∈ a). { rewrite <- H6.
      apply AxiomII_P. assert ((n+m-0) = n+m)%nat. { lia. }
      rewrite H11. assert ((n + m) > m)%nat. { 
      apply Nat.lt_add_pos_l. apply neq_0_lt. auto. }
      apply H4 in H12. rewrite H12; ring. } apply f_x' in H11; auto.
    - intros. assert ([S x, 0] ∈ a). { rewrite <- H6. apply AxiomII_P. 
      generalize (classic ( S x > n)%nat). intros; destruct H11.
      + apply H3 in H11. rewrite H11; ring.
      + assert (n+m-S x >= m)%nat. lia.
        assert (n >= S x)%nat. { lia. } assert (n > S x)%nat. {
        apply le_lt_or_eq in H13. destruct H13; try symmetry; 
        try contradiction. auto. } assert (n + m - S x > m)%nat. lia.
        apply H4 in H15; rewrite H15; ring. }
        apply f_x' in H11; auto. } apply f_x' in H6; auto. rewrite H6.
    apply Rmult_integral_contrapositive_currified; auto.
  - intros.
    assert ([m0, 0] ∈ (Poly_Mult f g)). {
    apply AxiomII_P. unfold Ck.
    assert (exists a, 
    \{\ λ(u : nat)(v : R),v = f [u] * g [(m0 - u)%nat] \}\ = a). {
    exists \{\ λ(u : nat)(v : R),v = f [u] * g [(m0 - u)%nat] \}\. auto. }
    destruct H7 as [t H7]. rewrite H7.
    assert (Function t). { red; intros. rewrite <- H7 in *.
    apply -> AxiomII_P in H8; simpl in H8.
    apply -> AxiomII_P in H9; simpl in H9. 
    rewrite H9; auto. }
    assert (m0 > n /\ m0 > m)%nat. { split; lia. } destruct H9.
    assert (forall x : nat, sum t x = 0). {
    intro x; induction x; intros.
    - simpl. assert ([0%nat, 0] ∈ t). { rewrite <- H7.
      apply AxiomII_P. assert ((m0 - 0) = m0)%nat. { lia. } rewrite H11.
      apply H4 in H10. rewrite H10. ring. } apply f_x' in H11; auto.
    - simpl. rewrite IHx. assert ([S x, 0] ∈ t). {
      rewrite <- H7. apply AxiomII_P.
      generalize (classic ( S x > n)%nat); intros; destruct H11.
      + apply H3 in H11. rewrite H11; ring.
      + assert ((m0 - S x) > m)%nat. { lia. }
        apply H4 in H12. rewrite H12; ring. }
      apply f_x' in H11; auto. rewrite H11; ring. }
    symmetry; apply H11. }
    apply f_x' in H7; auto.
Qed.



(* 推论2.1.1 *)
(* 零多项式,没有次数 *)
Definition degree_0 (f : Ensemble (prod nat R)) := 
  Polynomial f /\
  forall x : nat, x ∈ dom[f] -> f[x] = 0.

Lemma Lemma2_1_1'a : forall (f : Ensemble (prod nat R)),
  Polynomial f -> ~ degree_0 f -> 
  exists n, Polynomial_Degree f n.
Proof.
  intros.
  double H. unfold Polynomial in H. destruct H, H2.
  destruct H3 as [n H3].
  unfold degree_0 in H0. Search(~(_/\_)).
  apply not_and_or in H0; destruct H0. contradiction.
  apply not_all_ex_not in H0.
  destruct H0 as [n0 H0]. apply not_imply_elim2 in H0.
  assert (n0 <= n)%nat. {
    generalize (classic (n0 <= n)%nat); intros; destruct H4; auto.
    assert (n0 > n)%nat. { lia. }
    apply H3 in H5. contradiction. }
  induction n.
  - assert (n0 = 0)%nat. { lia. } subst n0.
    exists 0%nat. red. tauto.
  - generalize (classic (n0 = S n)%nat). intros; destruct H5.
    + rewrite H5 in H0. exists (S n). red; tauto.
    + generalize (classic (f[S n] = 0)); intros; destruct H6.
      * apply IHn.
        -- intros. generalize (classic (m = S n)%nat); intros; destruct H8.
           rewrite H8; auto. assert (m > S n)%nat. { lia. }
           apply H3 in H9; auto.
        -- lia.
      * exists (S n). red; tauto. 
Qed.

Theorem Theorem2_1_1' : forall (f g : Ensemble (prod nat R)),
  Polynomial f -> Polynomial g ->
  degree_0 f \/ degree_0 g <-> degree_0 (Poly_Mult f g).
Proof.
  intros. split; intros.
  - unfold degree_0. split. apply Poly_Mult_cc; auto.
    intros. destruct H1.
    + red in H1.
      assert ([x, 0] ∈ (Poly_Mult f g)). {
      apply AxiomII_P. unfold Ck.
      assert (forall n : nat, 
      sum \{\ λ(u : nat)(v : R),v = f [u] * g [(x - u)%nat] \}\ n = 0). { 
      assert (H4 :Function \{\ λ(u : nat)(v : R),
      v = f [u] * g [(x - u)%nat] \}\).
      { red; intros.
        apply -> AxiomII_P in H3; simpl in H3.
        apply -> AxiomII_P in H4; simpl in H4.
        rewrite H4; auto. }
      intro n; induction n.
      - simpl. assert ([0%nat, 0] ∈ 
        \{\ λ(u : nat)(v : R),v = f [u] * g [(x - u)%nat] \}\). {
        apply AxiomII_P. assert (0%nat∈ dom[f]). { 
        destruct H, H3. rewrite H3; apply AxiomII; auto. }
        apply H1 in H3. rewrite H3; ring. }
        apply f_x' in H3; auto.
      - simpl. rewrite IHn.
        assert ([S n, 0] ∈ 
        \{\ λ(u : nat)(v : R),v = f [u] * g [(x - u)%nat] \}\). {
        apply AxiomII_P. assert (S n ∈ dom[f]). {
        destruct H, H3. rewrite H3; apply AxiomII; auto. }
        apply H1 in H3. rewrite H3; ring. }
        apply f_x' in H3; auto. rewrite H3. ring. }
      symmetry; apply H3. } apply f_x' in H3; auto.
      red; intros.
      apply -> AxiomII_P in H4; simpl in H4.
      apply ->AxiomII_P in H5; simpl in H5.
      rewrite H5; auto.
    + rewrite Poly_Mult_comm. red in H1.
      assert ([x, 0] ∈ (Poly_Mult g f)). {
      apply AxiomII_P. unfold Ck.
      assert (forall n : nat, 
      sum \{\ λ(u : nat)(v : R),v = g [u] * f [(x - u)%nat] \}\ n = 0). { 
      assert (H4 :Function \{\ λ(u : nat)(v : R),
      v = g [u] * f [(x - u)%nat] \}\).
      { red; intros.
        apply -> AxiomII_P in H3; simpl in H3.
        apply -> AxiomII_P in H4; simpl in H4.
        rewrite H4; auto. }
      intro n; induction n.
      - simpl. assert ([0%nat, 0] ∈ 
      \{\ λ(u : nat)(v : R),v = g [u] * f [(x - u)%nat] \}\). {
      apply AxiomII_P. assert (0%nat∈ dom[g]). { 
      destruct H0, H3. rewrite H3; apply AxiomII; auto. }
      apply H1 in H3. rewrite H3; ring. }
      apply f_x' in H3; auto.
      - simpl. rewrite IHn.
        assert ([S n, 0] ∈ 
        \{\ λ(u : nat)(v : R),v = g [u] * f [(x - u)%nat] \}\). {
        apply AxiomII_P. assert (S n ∈ dom[g]). {
        destruct H0, H3. rewrite H3; apply AxiomII; auto. }
        apply H1 in H3. rewrite H3; ring. }
        apply f_x' in H3; auto. rewrite H3. ring. }
      symmetry; apply H3. } apply f_x' in H3; auto.
      red; intros.
      apply -> AxiomII_P in H4; simpl in H4.
      apply ->AxiomII_P in H5; simpl in H5.
      rewrite H5; auto.
  - generalize (classic (degree_0 f \/ degree_0 g)); intros.
    destruct H2; auto. apply Decidable.not_or in H2.
    apply Lemma2_1_1'a in H; try tauto.
    apply Lemma2_1_1'a in H0; try tauto.
    destruct H as [n H]; destruct H0 as [m H0].
    generalize (Theorem2_1_1b f g n m); intros.
    apply H3 in H; auto.
    red in H. destruct H, H4.
    red in H1. destruct H1.
    assert ((n+m)%nat ∈ dom[Poly_Mult f g]). {
    red in H. destruct H, H7. rewrite H7.
    apply AxiomII; auto. }
    apply H6 in H7. contradiction.
Qed.

End Section2_1.
Export Section2_1.



















