Require Export H2_2.

Module Section2_3.

(* 定义：公因式 *)
Definition CD (f g h : Ensemble (prod nat R)) :=
  exa_div f h /\ exa_div g h.

(* 定义：最大公因式 *)
Definition GCD (f g h : Ensemble (prod nat R)) := CD f g h /\ 
  (forall a, exa_div f a /\ exa_div g a -> exa_div h a).

Lemma IsFun : forall (f : Ensemble (prod nat R)),
  Function \{\ λ x y, y = f [ x ] \}\.
Proof.
  intros f n v1 v2 H0 H1.
  apply -> AxiomII_P in H0; simpl in H0.
  apply -> AxiomII_P in H1; simpl in H1.
  rewrite H1. assumption.
Qed.

Lemma FunValue : forall (f : Ensemble (prod nat R))(x:nat),
  \{\ λ x y, y = f [ x ] \}\ [ x ] = f [ x ].
Proof.
  intros.
  apply f_x'; [apply IsFun | apply AxiomII_P]. 
  reflexivity.
Qed.

Lemma Lemma2_3_1 : forall x (g : Ensemble (prod nat R)),
  sum \{\ λ(u : nat)(v : R),v = g [u] * \{\ λ(u0 : nat)(v0 : R),
  u0 = 0%nat /\ v0 = 1 \/ u0 <> 0%nat /\ v0 = 0 \}\
  [match u with | 0%nat => S x | S l => (x - l)%nat end] \}\ x = 0.
Proof.
  intros. induction x.
  - simpl.
    assert([0%nat, 0] ∈ \{\ λ(u : nat)(v : R),v = g [u] *
    \{\ λ(u0 : nat)(v0 : R),u0 = 0%nat /\ v0 = 1 \/
    u0 <> 0%nat /\ v0 = 0 \}\ [match u with | 0%nat => 1%nat
    | S _ => 0%nat end] \}\).
    { apply AxiomII_P.
      assert([1%nat, 0] ∈ \{\ λ(u0 : nat)(v0 : R),u0 = 0%nat /\ v0 = 1 
      \/ u0 <> 0%nat /\ v0 = 0 \}\).
      { apply AxiomII_P; right; auto. }
      apply f_x' in H. rewrite H. rewrite Rmult_0_r; auto.
      red; intros. apply -> AxiomII_P in H0; simpl in H0.
      apply -> AxiomII_P in H1; simpl in H1.
      destruct H1, H0, H1, H0; rewrite H2; rewrite H3; tauto. }
    apply f_x' in H. rewrite H; auto.
    red; intros. apply -> AxiomII_P in H0; simpl in H0.
    apply -> AxiomII_P in H1; simpl in H1.
    rewrite H0; rewrite H1; auto.
  - simpl sum.

Admitted.

Lemma Lemma2_3_3 : forall(f : Ensemble(prod nat R)),
  Polynomial f ->
  f = Poly_Mult f \{\ λ(u : nat)(v : R), (u = 0%nat /\ v = 1 \/
  u <> 0%nat /\ v = 0) \}\.
Proof.
  intros. apply AxiomI; split; intros; destruct z.
  - apply AxiomII_P. destruct x.
    + unfold Ck. simpl. 
      assert( \{\ λ(u0 : nat)(v0 : R),u0 = 0%nat /\ v0 = 1 \/
      u0 <> 0%nat /\ v0 = 0 \}\[0%nat] = 1).
      { apply f_x'. red; intros.
        apply -> AxiomII_P in H2; simpl in H2.
        apply -> AxiomII_P in H1; simpl in H1.
        destruct H2, H2, H1, H1; rewrite H4; rewrite H3; tauto.
        apply AxiomII_P. left; auto. }
      rewrite H1; clear H1. apply f_x' in H0.
      assert([0%nat,f[0%nat]] ∈ \{\λ(u : nat)(v : R),v = f [u] * 1\}\).
      { apply AxiomII_P. rewrite Rmult_1_r; auto. } 
      apply f_x' in H1. rewrite H1. auto.
      red; intros. apply -> AxiomII_P in H3; simpl in H3.
      apply -> AxiomII_P in H2; simpl in H2.
      rewrite H3; rewrite H2; auto. red in H; tauto.
    + simpl. unfold Ck. simpl sum.
      assert(\{\ λ(u : nat)(v : R),v = f [u] * 
      \{\ λ(u0 : nat)(v0 : R),u0 = 0%nat /\ v0 = 1 \/ u0 <> 0%nat /\ v0 = 0 \}\
      [match u with
       | 0%nat => S x
       | S l => (x - l)%nat
       end] \}\ [S x] = f[S x]).
      { assert([S x, f[S x]] ∈ \{\ λ(u : nat)(v : R),v =
        f [u] * \{\ λ(u0 : nat)(v0 : R),u0 = 0%nat /\ v0 = 1 \/
        u0 <> 0%nat /\ v0 = 0 \}\
        [match u with
         | 0%nat => S x
         | S l => (x - l)%nat
         end] \}\).
        { apply AxiomII_P. assert((x - x = 0)%nat). lia.
          rewrite H1. assert([0%nat, 1] ∈ \{\ λ(u0 : nat)(v0 : R),
          u0 = 0%nat /\ v0 = 1 \/ u0 <> 0%nat /\ v0 = 0 \}\).
          { apply AxiomII_P. left. auto. }
          apply f_x' in H2. rewrite H2. rewrite Rmult_1_r. auto.
          red; intros. apply -> AxiomII_P in H3; simpl in H3.
          apply -> AxiomII_P in H4; simpl in H4.
          destruct H3, H3, H4, H4; rewrite H5; rewrite H6; auto.
          contradiction. contradiction. }
        apply f_x' in H1. rewrite H1. auto.
        red; intros. apply -> AxiomII_P in H2; simpl in H2.
        apply -> AxiomII_P in H3; simpl in H3.
        rewrite H2; rewrite H3; auto. }
      rewrite H1. clear H1. rewrite Lemma2_3_1.
      apply f_x' in H0. rewrite H0.
      rewrite Rplus_0_l. auto. red in H; tauto.
  - apply -> AxiomII_P in H0; simpl in H0.
    unfold Ck in H0. destruct x.
    + simpl in H0.
      assert( \{\ λ(u0 : nat)(v0 : R),u0 = 0%nat /\ v0 = 1 \/
      u0 <> 0%nat /\ v0 = 0 \}\[0%nat] = 1).
      { apply f_x'. red; intros.
        apply -> AxiomII_P in H1; simpl in H1.
        apply -> AxiomII_P in H2; simpl in H2.
        destruct H1, H1, H2, H2; rewrite H3; rewrite H4; tauto.
        apply AxiomII_P. left; auto. }
      rewrite H1 in H0; clear H1.
      assert([0%nat,f[0%nat]] ∈ \{\λ(u : nat)(v : R),v = f [u] * 1\}\).
      { apply AxiomII_P. rewrite Rmult_1_r; auto. }
      apply f_x' in H1. rewrite H1 in H0; clear H1.
      rewrite H0. apply x_fx. red in H; tauto.
      destruct H, H1. rewrite H1. apply AxiomII; auto.
      red; intros. apply -> AxiomII_P in H2; simpl in H2.
      apply -> AxiomII_P in H3; simpl in H3.
      rewrite H2; rewrite H3; auto.
    + simpl in H0.
      assert(\{\ λ(u : nat)(v : R),v = f [u] * 
      \{\ λ(u0 : nat)(v0 : R),u0 = 0%nat /\ v0 = 1 \/ u0 <> 0%nat /\ v0 = 0 \}\
      [match u with
       | 0%nat => S x
       | S l => (x - l)%nat
       end] \}\ [S x] = f[S x]).
      { assert([S x, f[S x]] ∈ \{\ λ(u : nat)(v : R),v =
        f [u] * \{\ λ(u0 : nat)(v0 : R),u0 = 0%nat /\ v0 = 1 \/
        u0 <> 0%nat /\ v0 = 0 \}\
        [match u with
         | 0%nat => S x
         | S l => (x - l)%nat
         end] \}\).
        { apply AxiomII_P. assert((x - x = 0)%nat). lia.
          rewrite H1. assert([0%nat, 1] ∈ \{\ λ(u0 : nat)(v0 : R),
          u0 = 0%nat /\ v0 = 1 \/ u0 <> 0%nat /\ v0 = 0 \}\).
          { apply AxiomII_P. left. auto. }
          apply f_x' in H2. rewrite H2. rewrite Rmult_1_r. auto.
          red; intros. apply -> AxiomII_P in H3; simpl in H3.
          apply -> AxiomII_P in H4; simpl in H4.
          destruct H3, H3, H4, H4; rewrite H5; rewrite H6; auto.
          contradiction. contradiction. }
        apply f_x' in H1. rewrite H1. auto.
        red; intros. apply -> AxiomII_P in H2; simpl in H2.
        apply -> AxiomII_P in H3; simpl in H3.
        rewrite H2; rewrite H3; auto. }
      rewrite H1 in H0; clear H1. rewrite Lemma2_3_1 in H0.
      rewrite Rplus_0_l in H0.
      rewrite H0. apply x_fx. destruct H. tauto.
      destruct H, H1. rewrite H1. apply AxiomII; auto.
Qed.

(* 定理2.3.1 *)
Theorem Theorem2_3_1 : forall (f g : Ensemble(prod nat R)),
  forall n m : nat, Polynomial_Degree f n -> Polynomial_Degree g m ->
  exists d : Ensemble (prod nat R), GCD f g d.
Proof.
  intros. generalize dependent g. generalize dependent f.
  generalize dependent n.
  (* 对g的次数进行归纳 *)
  apply The_Second_Mathematical_Induction with (n := m).
  (* g为零次 *)
  - intros. destruct n.
    + exists f. red; split.
      red; split; try apply Lemma2_2_5; auto.
      red in H, H0; tauto. red in H, H0; tauto.
      intros. tauto.
    + exists g. red; split.
      red; split; try apply Lemma2_2_5; auto.
      red in H, H0; tauto. red in H, H0; tauto.
      intros; tauto.
  (* g的次数不为0 *)
  - intros. generalize H1; intros H10.
    apply Theorem2_2_1 with (f:=f)(n:=n) in H1; auto.
    destruct H1 as [q H1]. destruct H1 as [r H1], H1.
    generalize(classic(degree_0 r)); intros H11.
    destruct H11 as [H11|H11].
    + exists g. assert(r = \{\ λ(u : nat)(v : R), v = 0 \}\).
      { red in H11. destruct H11 as [H11 H12], H11.
        apply AxiomI; split; intros; destruct z.
        - apply f_x' in H5; auto.
          apply AxiomII_P. rewrite <- H5.
          apply H12. destruct H4. rewrite H4.
          apply AxiomII; auto.
        - apply -> AxiomII_P in H5; simpl in H5.
          rewrite H5. assert(x ∈ dom[ r]).
          { destruct H4. rewrite H4. apply AxiomII; auto. }
          double H6. apply H12 in H6. rewrite <- H6.
          apply x_fx; auto. }
      rewrite H3 in H1. rewrite Poly_add_0 in H1.
      red; split.
      * red; split; red; red in H0; red in H10;
        split; try tauto; split; try tauto.
        exists q; auto.
        exists \{\ λ(u : nat)(v : R), 
        (u = 0%nat /\ v = 1) \/ (u <> 0%nat /\ v = 0) \}\.
        rewrite <- Lemma2_3_3; auto. tauto.
      * intros. tauto.
    + destruct H2 as [H2 H12], H2. contradiction.
      apply Lemma2_1_1'a in H11; auto. destruct H11. double H3.
      apply H2 with(b:=k) in H3; auto.
      apply H with(f:=g)(n:=k)(g:=r) in H3; auto.
      destruct H3, H3, H3.
      exists x0. split.
      * split; auto; split; auto. red in H0; tauto.
        split; red in H3; auto. tauto.
        destruct H3, H6, H7, H8, H9, H11.
        rewrite H1. rewrite H9. rewrite Poly_Mult_assoc.
        rewrite H11. rewrite <- Poly_Mult_distr.
        exists (Poly_Add (Poly_Mult x1 q) x2). auto.
      * intros. apply H5. split; try tauto.
        destruct H7,H7. red.
        assert(r = Poly_Sub f (Poly_Mult g q)).
        { rewrite H1. unfold Poly_Sub. rewrite Poly_Add_comm.
          rewrite <- Poly_Add_assoc. rewrite Poly_Add_Sub.
          rewrite Poly_Add_comm. rewrite Poly_add_0. auto.
          unfold Poly_neg. red; intros.
          apply -> AxiomII_P in H13; simpl in H13.
          apply -> AxiomII_P in H11; simpl in H11.
          rewrite H13; rewrite H11; auto.
          red; intros.
          apply -> AxiomII_P in H13; simpl in H13.
          apply -> AxiomII_P in H11; simpl in H11.
          rewrite H13; rewrite H11; auto.
          red in H4. destruct H4, H4. auto. }
        split; auto; split. tauto. destruct H9, H13.
        rewrite H11. destruct H8, H14, H15. rewrite H15.
        rewrite Poly_Mult_assoc. rewrite H13.
        rewrite <- Poly_Mult_distr'.
        exists (Poly_Sub x1 (Poly_Mult x2 q)). auto.
Qed.

Theorem Theorem2_3_1' : forall (f g d1 d2: Ensemble(prod nat R))(c:R),
  GCD f g d1 -> GCD f g d2 -> d1 = a_mult d2 c.
Proof.
  intros. destruct H, H0, H, H0, H, H3, H0, H4.
  Admitted.
  


Lemma Lemma2_3_2 : forall(f : Ensemble(prod nat R)),
  Poly_Mult f \{\ λ u v, (u = 0%nat /\ v = 1 / f[0%nat]) \/
  (u <> 0%nat /\ v = 0) \}\ =
  \{\ λ(u0 : nat)(v0 : R),u0 = 0%nat /\ v0 = 1 \/
  u0 <> 0%nat /\ v0 = 0 \}\. Admitted.

Lemma Lemma2_3_2' : forall(f g q: Ensemble(prod nat R)),
  f = Poly_Mult g q -> GCD f g g.
Proof.
  intros. red.
  Admitted.


(* 定理2.3.2 *) 
Theorem Theorem3_3_2 : forall(f g d: Ensemble(prod nat R)),
  forall n m : nat, Polynomial_Degree f n -> Polynomial_Degree g m ->
  GCD f g d -> exists u v, Poly_Add(Poly_Mult f u)(Poly_Mult g v) = d.
Proof.
  intros. generalize dependent g. generalize dependent f.
  generalize dependent n.
  (* 对g的次数进行归纳 *)
  apply The_Second_Mathematical_Induction with (n := m).
  (* g为零次 *)
  - intros. exists \{\ λ(u : nat)(v : R), v = 0 \}\.
    rewrite Poly_mult_0. destruct H1, H1, H3, H4, H5.
    rewrite H5. exists \{\ λ u v, (u = 0%nat /\ v = 1/x[0%nat]) \/
    (u <> 0%nat /\ v = 0) \}\.
    rewrite Poly_Add_comm. rewrite Poly_add_0.
    rewrite Poly_Mult_assoc. rewrite Lemma2_3_2.
    rewrite Lemma2_3_3; auto.
  (* g的次数不为零 *)
  - intros. double H1.
    apply Theorem2_2_1 with (f:=f)(n:=n) in H3; auto.
    destruct H3 as [q H3]. destruct H3 as [r H3], H3, H4.
    generalize(classic(degree_0 r)); intros; destruct H6.
    + assert(r = \{\ λ(u : nat)(v : R), v = 0 \}\).
      { red in H6. destruct H6, H6, H8.
        apply AxiomI; split; intros; destruct z.
        - apply f_x' in H10; auto.
          apply AxiomII_P. rewrite <- H10.
          apply H7. rewrite H8.
          apply AxiomII; auto.
        - apply -> AxiomII_P in H10; simpl in H10.
          rewrite H10. assert(x ∈ dom[ r]).
          { rewrite H8. apply AxiomII; auto. }
          double H11. apply H7 in H11. rewrite <- H11.
          apply x_fx; auto. }
      rewrite H7 in H3. rewrite -> Poly_add_0 in H3.
      apply Lemma2_3_2' in H3. 
      apply Theorem2_3_1' with(d1:=d)(c:=1) in H3; auto.
      assert(a_mult g 1 = g).
      { apply AxiomI; split; intros; destruct z.
        - apply -> AxiomII_P in H8; simpl in H8.
          rewrite Rmult_1_l in H8. rewrite H8.
          destruct H1, H1, H10.
          apply x_fx; auto. rewrite H10; apply AxiomII; auto.
        - apply AxiomII_P. destruct H1, H1.
          apply f_x' in H8; auto. rewrite H8.
          rewrite Rmult_1_l; auto. }
      rewrite H8 in H3; clear H8. rewrite H3.
      exists \{\ λ(u : nat)(v : R), v = 0 \}\.
      rewrite Poly_mult_0.
      exists \{\ λ u v, (u = 0%nat /\ v = 1) \/
      (u <> 0%nat /\ v = 0) \}\.
      rewrite <- Lemma2_3_3. rewrite Poly_Add_comm.
      rewrite Poly_add_0; auto. red in H1; tauto.
    + destruct H4. contradiction.
      apply Lemma2_1_1'a in H6; auto. destruct H6. double H6.
      apply H4 with (b:=k) in H6; auto.
      apply H with (n:=k)(f:=g)(g:=r) in H6; auto.
      destruct H6 as [u [v H6]].
      assert(r = Poly_Sub f (Poly_Mult g q)).
      { rewrite H3. unfold Poly_Sub. rewrite Poly_Add_comm.
        rewrite <- Poly_Add_assoc. rewrite Poly_Add_Sub.
        rewrite Poly_Add_comm. rewrite Poly_add_0. auto.
        unfold Poly_neg. red; intros.
        apply -> AxiomII_P in H9; simpl in H9.
        apply -> AxiomII_P in H8; simpl in H8.
        rewrite H9; rewrite H8; auto. red; intros.
        apply -> AxiomII_P in H9; simpl in H9.
        apply -> AxiomII_P in H8; simpl in H8.
        rewrite H9; rewrite H8; auto.
        red in H5. destruct H5. auto. }
      rewrite H8 in H6. rewrite Poly_Add_comm in H6.
      rewrite Poly_Mult_comm in H6.
      rewrite Poly_Mult_distr' in H6. unfold Poly_Sub in H6.
      rewrite Poly_Add_assoc in H6. rewrite Poly_Mult_comm in H6.
      exists v. exists (Poly_Sub u (Poly_Mult q v)).
      rewrite <- H6.
      assert(Poly_Sub(Poly_Mult g u)(Poly_Mult v (Poly_Mult g q)) =
      (Poly_Add (Poly_neg (Poly_Mult v (Poly_Mult g q))) (Poly_Mult g u))).
      { unfold Poly_Sub. rewrite Poly_Add_comm; auto. }
      rewrite <- H9; clear H9.
      assert(Poly_Mult v (Poly_Mult g q) = Poly_Mult g (Poly_Mult q v)).
      { rewrite <- Poly_Mult_assoc. rewrite Poly_Mult_comm.
        rewrite <- Poly_Mult_assoc. rewrite Poly_Mult_comm. auto. }
      rewrite H9; clear H9.
      rewrite Poly_Mult_distr'; auto.
      * red; intros.
        apply -> AxiomII_P in H9; simpl in H9.
        apply -> AxiomII_P in H10; simpl in H10.
        rewrite H9; rewrite H10; auto.
      * red; intros.
        apply -> AxiomII_P in H9; simpl in H9.
        apply -> AxiomII_P in H10; simpl in H10.
        rewrite H9; rewrite H10; auto.
      * red; intros.
        apply -> AxiomII_P in H9; simpl in H9.
        apply -> AxiomII_P in H10; simpl in H10.
        rewrite H9; rewrite H10; auto.
      * red. red in H2; destruct H2, H2.
        assert(exa_div r d). 
        { rewrite H3 in H2; red in H2.
          destruct H2, H10, H11. red.
          split; auto. split; auto.
          assert(r = Poly_Sub(Poly_Mult d x0) (Poly_Mult g q)).
          { unfold Poly_Sub. rewrite <- H11. rewrite Poly_Add_comm.
            rewrite <- Poly_Add_assoc. rewrite Poly_Add_Sub.
            rewrite Poly_Add_comm; rewrite Poly_add_0; auto.
            red; intros.
            apply -> AxiomII_P in H12; simpl in H12.
            apply -> AxiomII_P in H13; simpl in H13.
            rewrite H12; rewrite H13; auto.
            red; intros.
            apply -> AxiomII_P in H12; simpl in H12.
            apply -> AxiomII_P in H13; simpl in H13.
            rewrite H12; rewrite H13; auto.
            destruct H5; auto. }
          destruct H9, H13, H14. rewrite H14 in H12.
          pattern(Poly_Mult (Poly_Mult d x1) q) in H12.
          rewrite Poly_Mult_assoc in H12.
          rewrite <- Poly_Mult_distr' in H12.
          exists (Poly_Sub x0 (Poly_Mult x1 q)); auto. }
        split. split; auto.
        intros. red. split; red in H2. tauto.
        split; destruct H11; red in H11. tauto.
        destruct H10, H13, H14. destruct H12, H15, H16.
        rewrite H14 in H16. admit.
Admitted.

(* 定义：多项式互素 *)
Definition Prime (f g : Ensemble(prod nat R)) := 
  GCD f g \{\ λ u v, u = 0%nat /\ v = 1 \/ u <> 0%nat /\ v = 0 \}\.



(* 定理2.3.3 *)
Theorem Theorem2_3_3 : forall(f g : Ensemble(prod nat R)),
  forall n m : nat, Polynomial_Degree f n -> Polynomial_Degree g m ->
  ( Prime f g <-> exists u v, Poly_Add(Poly_Mult f u)(Poly_Mult g v) = 
  \{\ λ(u : nat)(v : R), (u = 0%nat /\ v = 1 \/ u <> 0%nat /\ v = 0) \}\ ).
Proof.
  intros; split; intros.
  - red in H1. apply Theorem2_3_2 with(n:=n)(m:=m) in H1; auto.
  - red. red. unfold CD. split. split.
    + red. split; red in H. tauto.
      split. admit.
      exists f. rewrite Poly_Mult_comm.
      rewrite <- Lemma2_3_3; auto. tauto.
    + red. split; red in H0. tauto.
      split. admit.
      exists g. rewrite Poly_Mult_comm.
      rewrite <- Lemma2_3_3; auto. tauto.
    + intros. red. destruct H2, H2, H4, H5, H3, H6, H7.
      destruct H1, H1. rewrite H5 in H1. rewrite H7 in H1.
      rewrite Poly_Mult_assoc in H1. rewrite Poly_Mult_assoc in H1.
      rewrite <- Poly_Mult_distr in H1.
      split. admit. split; auto.
      exists (Poly_Add (Poly_Mult x x1) (Poly_Mult x0 x2)). auto.
Admitted.
