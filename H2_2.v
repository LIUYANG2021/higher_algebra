Require Export H2_1_new.

Module Section2_2.

(* 定义 整除 *)
Definition exa_div (f g : Ensemble (prod nat R)) :=
  Polynomial f /\ Polynomial g /\
  exists h : Ensemble (prod nat R), f = Poly_Mult g h.

Axiom Poly_Mult_assoc : forall (f g h : Ensemble(prod nat R)),
  Poly_Mult (Poly_Mult f g) h = Poly_Mult f (Poly_Mult g h).

Axiom Poly_Mult_distr : forall (f g h : Ensemble(prod nat R)),
  Poly_Mult f (Poly_Add g h) = Poly_Add (Poly_Mult f g) (Poly_Mult f h).

Axiom Poly_Mult_distr' : forall (f g h : Ensemble(prod nat R)),
  Poly_Mult f (Poly_Sub g h) = Poly_Sub (Poly_Mult f g) (Poly_Mult f h).

Axiom Poly_mult_0 : forall (f : Ensemble(prod nat R)),
  Poly_Mult f \{\ λ (u : nat) v, v = 0 \}\ = \{\ λ (u : nat) v, v = 0 \}\.

Axiom Poly_add_0 : forall (f : Ensemble(prod nat R)),
  Poly_Add f \{\ λ (u : nat) v, v = 0 \}\ = f.

(* 基本性质 *)
Lemma Lemma2_2_1 : forall (f g h : Ensemble(prod nat R)),
  exa_div f g /\ exa_div g h -> exa_div f h.
Proof.
  intros; destruct H. red in H; destruct H,H1,H2.
  red in H0; destruct H0,H3,H4.
  rewrite H4 in H2. rewrite Poly_Mult_assoc in H2.
  red; split; auto. split; auto. exists (Poly_Mult x0 x); auto.
Qed.


Lemma Lemma2_2_2 : forall (h f g : Ensemble(prod nat R)),
  exa_div h f /\ exa_div h g -> exa_div h (Poly_Add f g).
Proof.
  intros; destruct H. red in H; destruct H,H1,H2.
  red in H0; destruct H0,H3,H4.
  red; split; auto; split.
  - repeat split.
Admitted.

Lemma Lemma2_2_5 : forall (f g : Ensemble(prod nat R)),
  Polynomial f -> Polynomial_Degree g 0 -> exa_div f g.
Proof.
  intros. red; split; auto. split; red in H0. tauto.
  exists \{\ λ(u : nat)(v : R), v = f[u]/g[0%nat] \}\.
  apply AxiomI; split; intros; destruct z.
  - apply AxiomII_P. admit. 
  - admit. 
Admitted.

(* 定理2.2.1 *)
Theorem Theorem2_2_1 : forall (f g : Ensemble (prod nat R)),
  forall n m : nat, Polynomial_Degree f n -> Polynomial_Degree g m ->
  (exists q r : Ensemble (prod nat R), f = Poly_Add (Poly_Mult g q) r /\
  (degree_0 r \/ (forall a b : nat, Polynomial_Degree r a ->
  Polynomial_Degree g b -> (a < b)%nat)) /\ Polynomial r).
Proof.
  intros f g n. generalize dependent f.
  (* 数学归纳法f *)
  apply The_Second_Mathematical_Induction with (n := n).
  (* f次数为0，g的次数分情况讨论 *)
  - intros. destruct m; intros.
    (* g是0次多项式 *)
    + exists \{\ λ(u : nat)(v : R),u = 0%nat/\v = f[0%nat]/g[0%nat] \/
      (u > 0)%nat/\v=0 \}\, \{\ λ(u : nat)(v : R), v = 0 \}\. repeat split.
      * red in H0. 
        assert(Poly_Mult g \{\ λ(u : nat)(v : R),u = 0%nat /\ 
        v = f [0%nat]/g [0%nat] \/ (u > 0)%nat/\v=0 \}\ = f).
        { apply AxiomI; split; intros; destruct z.
          - apply -> AxiomII_P in H1; simpl in H1. unfold Ck in H1.
            admit.
          - apply AxiomII_P.
        admit. }
        rewrite H1. rewrite Poly_add_0; auto.
      * left. unfold degree_0. split. { admit. } intros.
        assert([x,0] ∈ \{\ λ(_ : nat)(v : R),v = 0 \}\).
        { apply AxiomII_P; auto. }
        apply f_x' in H2; auto.
        red; intros. apply -> AxiomII_P in H3; simpl in H3.
        apply -> AxiomII_P in H4; simpl in H4.
        rewrite H3; rewrite H4; auto.
      * red; intros. apply -> AxiomII_P in H1; simpl in H1.
        apply -> AxiomII_P in H2; simpl in H2.
        rewrite H1; rewrite H2; auto.
      * apply AxiomI; split; intros.
        -- apply AxiomII; auto.
        -- apply AxiomII. exists 0. apply AxiomII_P. auto.
      * exists 0%nat. intros.
        apply f_x'.
        red; intros. apply -> AxiomII_P in H2; simpl in H2.
        apply -> AxiomII_P in H3; simpl in H3.
        rewrite H2; rewrite H3; auto.
        apply AxiomII_P. auto.
    (* g的次数不为0 *)
    + exists \{\ λ(u : nat)(v : R), v = 0 \}\, f; split.
      * rewrite Poly_mult_0. rewrite Poly_Add_comm; rewrite Poly_add_0. auto.
      * split.
        right. intros.
        assert(0 = a)%nat. { apply Equal_Degree with f; auto. }
        assert(S m = b). { apply Equal_Degree with g; auto. }
        rewrite <- H3; rewrite <- H4. apply Nat.lt_0_succ.
        red in H. tauto.
  (* f次数不为0  讨论f和g次数的大小*)
  - intros. generalize(classic(k < m)%nat); intros; destruct H2 as [H12|H12].
    + exists \{\ λ(u : nat)(v : R), v = 0 \}\, f; split.
      * rewrite Poly_mult_0. rewrite Poly_Add_comm; rewrite Poly_add_0. auto.
      * split. right. intros.
        assert(k = a)%nat. { apply Equal_Degree with f; auto. }
        assert(m = b). { apply Equal_Degree with g; auto. }
        rewrite <- H4; rewrite <- H5. auto.
        red in H0; tauto.
     (* k>=m *)
    + apply not_lt in H12.
      assert(exists h, h = \{\ λ(u : nat)(v : R), u = (k-m)%nat /\ v = f[k]/g[m]
      \/ u<>(k-m)%nat /\ v=0\}\).
      { exists \{\ λ(u : nat)(v : R), u = (k-m)%nat /\ v = f[k]/g[m] \/ 
        u<>(k-m)%nat /\ v=0\}\. auto. }
      destruct H2 as [h H2].
      assert(exists f1, f1 = Poly_Sub f (Poly_Mult h g)).
      { exists (Poly_Sub f (Poly_Mult h g)). auto. }
      destruct H3 as [f1 H3].
      assert(Function f1).
      { red; intros. rewrite H3 in H4. rewrite H3 in H5.
        apply -> AxiomII_P in H4; simpl in H4.
        apply -> AxiomII_P in H5; simpl in H5.
        rewrite H4; rewrite H5; auto. }
      assert(Polynomial f1).
      { unfold Poly_Sub in H3. unfold Poly_Mult in H3.
        red; repeat split; auto.
        - apply AxiomI; split; intros.
          apply AxiomII; auto.
          apply AxiomII. exists f1[z]. rewrite H3. apply AxiomII_P.
          assert([z,f [z] + (Poly_neg \{\ λ(u : nat)(v : R),v = Ck h g u \}\) [z]] ∈
          (Poly_Add f (Poly_neg \{\ λ(u : nat)(v : R),v = Ck h g u \}\))).
          { apply AxiomII_P; auto. }
          apply f_x' in H6; auto. rewrite <- H3; auto.
        - exists k. intros. assert([m0,0] ∈ f1).
          { rewrite H3. apply AxiomII_P; simpl.

            admit. }
          apply f_x'; auto.
        }
      generalize(classic(degree_0 f1)); intros; destruct H6 as [H20|H20].
      * exists h, \{\ λ(u : nat)(v : R), v = 0 \}\; split.
        -- rewrite Poly_add_0. red in H20. rewrite H3 in H20. admit.
        -- split. left. red. split. { admit. } intros. apply f_x'.
           red; intros. apply -> AxiomII_P in H7; simpl in H7.
           apply -> AxiomII_P in H8; simpl in H8.
           rewrite H7; rewrite H8; auto.
           apply AxiomII_P; auto. red; repeat split.
           ++ red; intros. apply -> AxiomII_P in H6; simpl in H6.
              apply -> AxiomII_P in H7; simpl in H7.
              rewrite H6; rewrite H7; auto.
           ++ apply AxiomI; split; intros.
              apply AxiomII; auto.
              apply AxiomII. exists 0. apply AxiomII_P. auto.
           ++ exists 0%nat. intros.
              apply f_x'.
              red; intros. apply -> AxiomII_P in H7; simpl in H7.
              apply -> AxiomII_P in H8; simpl in H8.
              rewrite H7; rewrite H8; auto.
              apply AxiomII_P. auto.
      * double H5.
        apply Lemma2_1_1'a in H6; auto. destruct H6 as [n1 H6].
        assert(Function h).
        { red; intros. rewrite H2 in H7. rewrite H2 in H8.
          apply -> AxiomII_P in H7; simpl in H7.
          apply -> AxiomII_P in H8; simpl in H8.
          destruct H7, H8; destruct H7, H8; rewrite H9; rewrite H10; auto.
          contradiction. contradiction. }
        assert(Polynomial h).
        { red; repeat split; auto.
          - apply AxiomI; split; intros.
            apply AxiomII; auto.
            generalize(classic(z = k-m)%nat); intros; destruct H9 as [H40| H40].
            + apply AxiomII. exists h[(z)%nat]. rewrite H2.
              apply AxiomII_P. left; split; auto.
              rewrite H40.
              assert([(k - m)%nat, f[k]/g[m]] ∈ \{\λ(u : nat)(v : R),
              u = (k - m)%nat /\ v = f [k] / g [m] \/ 
              u <> (k - m)%nat /\ v = 0 \}\).
              { apply AxiomII_P. left; auto. }
              apply f_x' in H9; auto. rewrite <- H2; auto.
            + apply AxiomII. exists h[(z)%nat]. rewrite H2.
              apply AxiomII_P. right; split; auto.
              assert([z, 0] ∈ \{\λ(u : nat)(v : R), u = (k - m)%nat /\ 
              v = f [k] / g [m] \/ u <> (k - m)%nat /\ v = 0 \}\).
              { apply AxiomII_P. right; auto. }
              apply f_x' in H9; auto. rewrite <- H2; auto.
          - exists(k-m)%nat. intros. assert([m0, 0] ∈ h).
            { rewrite H2. apply AxiomII_P. right; split; auto. lia. }
            apply f_x'; auto.
        }
        assert(H30 : ~ degree_0 h). 
        { intro. unfold degree_0 in H9.
          assert((k-m)%nat ∈ dom[h]).
          { apply AxiomII. exists h[(k-m)%nat]. rewrite H2.
            apply AxiomII_P. left; split; auto.
            assert([(k-m)%nat, f[k]/g[m]] ∈ \{\ λ(u : nat)(v : R),u = (k - m)%nat 
            /\ v = f [k] / g [m] \/ u <> (k - m)%nat /\ v = 0 \}\).
            { apply AxiomII_P. left; auto. }
            apply f_x'; auto. rewrite <- H2; auto. }
          apply H9 in H10.
          assert([(k-m)%nat, f [k]/g [m]] ∈ h).
          { rewrite H2; apply AxiomII_P. left; auto. }
          apply f_x' in H11; auto. rewrite H10 in H11. admit. }
        double H8; apply Lemma2_1_1'a in H9; auto.
        destruct H9 as [h1 H9].
        assert(h1 = k - m)%nat.
        { red in H9. destruct H9, H10.
          rewrite H2 in H10. 
          generalize(classic(h1 = k-m)%nat); intros; destruct H13; auto.
          assert([h1, 0] ∈ \{\ λ(u : nat)(v : R),u = (k - m)%nat /\ 
          v = f [k] / g [m] \/ u <> (k - m)%nat /\ v = 0 \}\).
          { apply AxiomII_P. right. auto. }
          apply f_x' in H14. contradiction.
          red; intros. apply -> AxiomII_P in H15; simpl in H15.
          apply -> AxiomII_P in H16; simpl in H16.
          destruct H15,H15; destruct H16,H16; rewrite H17; rewrite H18; auto.
          contradiction. contradiction. }
        rewrite H10 in H9.
        generalize(Theorem2_1_1b h g (k-m) m); intros.
        double H9; apply H11 in H9; auto. clear H11.
        assert(k-m+m = k)%nat. { apply Nat.sub_add. auto. }
        rewrite H11 in H9; clear H11.
        assert(Function (Poly_Mult h g)).
        { red in H9; destruct H9. red in H9; tauto. }
        assert(n1 < k)%nat.
        { rewrite H3 in H6.  admit. }
        apply H with (f:=f1)(m0:=m) in H14; auto.
        destruct H14 as [q [r H14]]. destruct H14.
        assert(f = Poly_Add f1 (Poly_Mult h g)).
        { rewrite H3. unfold Poly_Sub. rewrite Poly_Add_assoc; auto.
          rewrite Poly_Add_Sub. rewrite Poly_add_0; auto.
          red in H0; destruct H0. red in H0; tauto.
          red; intros. apply -> AxiomII_P in H16; simpl in H16.
          apply -> AxiomII_P in H17; simpl in H17.
          rewrite H16; rewrite H17; auto. }
        red in H1; destruct H1. red in H1; destruct H1.
        rewrite H14 in H16. rewrite Poly_Add_comm in H16.
        rewrite <- Poly_Add_assoc in H16.
        assert(Poly_Add (Poly_Mult h g) (Poly_Mult g q) = 
        Poly_Mult g (Poly_Add h q)).
        { rewrite Poly_Mult_distr. rewrite Poly_Mult_comm. auto. }
        rewrite H19 in H16; clear H19.
        exists (Poly_Add h q), r; split; auto. apply H11.
        red; intros.
        apply -> AxiomII_P in H19; simpl in H19.
        apply -> AxiomII_P in H21; simpl in H21.
        rewrite H19; rewrite H21; auto.
        destruct H15. red in H19. tauto.

Admitted.


Theorem Theorem2_2_1' : forall (f g q r q' r' : Ensemble (prod nat R)),
  f = Poly_Add (Poly_Mult g q) r /\(degree_0 r \/ 
  (forall a b : nat, Polynomial_Degree r a ->
  Polynomial_Degree q b -> (a < b)%nat)) ->
  f = Poly_Add (Poly_Mult g q') r' /\(degree_0 r' \/ 
  (forall a b : nat, Polynomial_Degree r' a ->
  Polynomial_Degree q' b -> (a < b)%nat)) ->
  q = q' /\ r = r'.
Proof.
  intros. destruct H, H0.
  
Admitted.

(* 定义多项式除法 *)
Definition Poly_div (f g : Ensemble (prod nat R)) :=
  \{\ λ q r , f = Poly_Add (Poly_Mult g q) r /\(degree_0 r \/ 
  (forall a b : nat, Polynomial_Degree r a ->
  Polynomial_Degree q b -> (a < b)%nat)) \}\.



End Section2_2.
Export Section2_2.










