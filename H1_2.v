Require Export H1_1.

(* H_1_2 映射 *)
Module H12.

Set Implicit Arguments.

Proposition Lemma_x : forall A : Prop, A -> A /\ A.
Proof. intros; split; auto. Qed.

Ltac double H := apply Lemma_x in H; destruct H.

Definition Relation(A B: Type) X Y (f: Ensemble (prod A B)) := f ⊂ X × Y.

(* 1.定义映射 *)
Definition mapping(A B: Type)X Y(f: Ensemble (prod A B)) :=
  Relation X Y f /\ (forall x, x ∈ X -> exists y, [x,y] ∈ f) /\
  (forall x y z, [x, y] ∈ f /\ [x, z] ∈ f -> y = z).
(* 定义定义域 *)
Definition Domain(X Y : Type) (f : Ensemble(prod X Y)) :=
  \{λ x, exists y, [x, y] ∈ f \}.
Notation "dom[ f ]" := (Domain f)(at level 5).

Parameter C : Ɐ (A : Type) (X : (Ensemble A)), A.
Axiom AxiomC : Ɐ (A : Type) (X : (Ensemble A)), (C X) ∈ X.

Theorem ChooseSingleton : forall(A: Type)(x: A), C [x] = x.
Proof.
  intros A x. assert (H0 : C [x] ∈ [x]). apply AxiomC.
  apply -> AxiomII in H0. apply H0.
Qed.

(* 定义像 *)
Definition image (A B: Type) (f: Ensemble (prod A B))(x: A) :=
  C\{ λ y, [x, y] ∈ f \}.
Notation "f [ x ]" := (image f x)(at level 5).

Theorem f_x : Ɐ (A B: Type)(x: A)(y: B)(X: Ensemble A)(Y: Ensemble B) f,
  mapping X Y f -> [x, y] ∈ f -> f[ x ] = y.
Proof.
  intros. unfold image.
  assert (\{ λ y0 : B, [x, y0] ∈ f \} = [ y ]).
  { apply AxiomI. intro z; split; intro H2.
    - apply -> AxiomII in H2; simpl in H2. apply <- AxiomII.
      apply H with (x := x); auto.
    - apply <- AxiomII. apply -> AxiomII in H2; simpl in H2.
      rewrite H2. auto. }
  rewrite H1.
  rewrite ChooseSingleton. auto.
Qed.


(* 定义：函数  *)
Definition Function (A B : Type) (f : Ensemble (prod A B)) : Prop := 
  forall x y z, [x, y] ∈ f -> [x, z] ∈ f -> y = z.


(* 定义：值域 *)
Definition Range (X Y : Type) (f : Ensemble (prod X Y)) :=
  \{ λ y, exists x, [x, y] ∈ f \}.
Notation "ran[ f ]" := (Range f) (at level 5).

Theorem f_x' : forall (X Y : Type) (f : Ensemble (prod X Y)) (x : X)(y : Y) ,
  Function f -> [x, y] ∈ f -> f[ x ] = y.
Proof.
  intros X Y f x y H1 H2. unfold image. 
  assert (H3 : \{ λ y0 : Y, [x, y0] ∈ f \} = [y]). 
  { apply AxiomI. intro z. split; intro H3.
    + apply -> AxiomII in H3. simpl in H3. apply AxiomII.
      apply H1 with (x := x);auto.
    + apply AxiomII. apply -> AxiomII in H3. simpl in H3.
      rewrite H3. auto. }
  rewrite H3. apply ChooseSingleton. 
Qed.

Theorem x_fx : forall (X Y: Type) (f : Ensemble (prod X Y))(x : X)(y : Y),
  Function f -> x ∈ dom[f] -> [x, f[x]] ∈ f.
Proof.
  intros. apply -> AxiomII in H0; simpl in H0.
  destruct H0.  apply f_x' with(X:=X)(Y:=Y) in H0 as H2; auto.
  rewrite H2; auto.
Qed.

(* 2.定义满射 *)
Definition surjective(A B: Type)(X: Ensemble A)(Y: Ensemble B) f :=
  mapping X Y f /\ (forall y, y ∈ Y -> ∃ x, x ∈ X /\ [x, y] ∈ f).


(* 3.定义单射 *)
Definition injective(A B: Type)(X: Ensemble A)(Y: Ensemble B) f :=
  mapping X Y f /\ (forall x1 x2, x1 ∈ X -> x2 ∈ X ->
  x1 ≠ x2 -> f [ x1 ] ≠ f [ x2 ]).


(* 4.定义合成 *)
Axiom AxiomII_P : Ɐ(A B: Type)(a: A)(b: B)(P: A -> B -> Prop),
  [a,b] ∈ \{\ P \}\ <-> P a b.

Axiom Property_P : Ɐ(A B: Type)(P: A -> B -> Prop)(z: prod A B),
  z ∈ \{\ P \}\ -> (∃(a: A)(b: B), z=[a,b]) /\ z ∈ \{\ P \}\.
  
Check or_introl.

Ltac PP H a b := 
  apply Property_P in H; destruct H as [[a [b H]]]; rewrite H in *.

Definition Composition(A B C: Type)(g: Ensemble(prod B C))(f: Ensemble(prod A B)) :=
  \{\ λ a c, (∃ b, [a,b] ∈ f /\ [b,c] ∈ g) \}\.
Notation "g ◦ f" := (Composition g f)(at level 50, no associativity).


(* 5.定义双射（一一映射） *)
Definition bijective(A B: Type)(X: Ensemble A)(Y: Ensemble B)(f: Ensemble(prod A B)) :=
  surjective X Y f /\ injective X Y f.

(* 定义恒等映射 *)
Definition identity_mapping(A: Type)(X: Ensemble A) :=
  \{\ λ x y, x ∈ X /\ y ∈ X /\ x = y\}\.
Notation "id[ X ] " := (identity_mapping X)(at level 5).

(* 定义逆映射 *)
Definition Inverse(A B: Type)(f : Ensemble (prod A B)) :=
  \{\ λ x y, [y, x] ∈ f \}\.
Notation "f ﹣¹" := (Inverse f)(at level 5).


Lemma Lemma1_2_1 : forall(A B: Type)(a: A)(b: B)(X: Ensemble A)(Y: Ensemble B)
  (f: Ensemble (prod A B)), bijective X Y f -> [a,b] ∈ f -> [b,a] ∈ f ﹣¹.
Proof.
  intros. apply AxiomII_P; auto.
Qed.


Lemma Property_Value : forall(A B: Type)(x: A)(X: Ensemble A)(Y: Ensemble B)
  (f: Ensemble (prod A B)), mapping X Y f -> x ∈ X -> [x, f[ x ]] ∈ f.
Proof.
  intros. generalize H; intros.
  destruct H, H2.
  apply H2 in H0. destruct H0.
  assert (f[x]=x0).
  { apply f_x with(X:=X)(Y:=Y); auto. }
  rewrite H4; auto.
Qed.

Lemma Lemma1_2_1''' : forall(A B: Type)(X : Ensemble A)(Y : Ensemble B) f,
  mapping X Y f -> Relation Y X f ﹣¹.
Proof.
  intros. red in H. destruct H. red in H.
  red. red. intros. unfold Inverse in H1. PP H1 a b. apply -> AxiomII_P in H2.
  simpl in H2. apply H in H2. apply -> AxiomII_P in H2. simpl in H2.
  apply AxiomII_P. tauto.
Qed.

Lemma Lemma1_2_1' : forall(A B: Type)(a: A)(b: B)(X: Ensemble A)(Y: Ensemble B)
  (f: Ensemble (prod A B)), bijective X Y f -> [b,a] ∈ f ﹣¹ -> [a,b] ∈ f.
Proof.
  intros. apply -> AxiomII_P in H0; simpl in H0; auto.
Qed.

Lemma Lemma1_2_1'' : forall(A B : Type)(X : Ensemble A)(Y : Ensemble B) 
  (f : Ensemble(prod A B)), bijective X Y f -> bijective Y X f ﹣¹.
Proof.
  intros. red in H; red. destruct H. generalize H; intros. red in H1. 
  destruct H1. clear H2.
  assert (mapping Y X f ﹣¹) as G.
  {red; repeat split; intros.
  - apply Lemma1_2_1''' in H1. auto.
  - red in H1. destruct H1, H3. red in H. destruct H. apply H5 in H2. 
    destruct H2, H2. exists x0. apply AxiomII_P; auto.
  - destruct H2. apply -> AxiomII_P in H2; simpl in H2.
    apply -> AxiomII_P in H3; simpl in H3. red in H0. destruct H0.
    generalize (classic (y = z)); intros; destruct H5; auto.
    generalize H2 H3. intros. apply H0 in H6; apply H0 in H7.
    apply -> AxiomII_P in H6. simpl in H6. apply -> AxiomII_P in H7. 
    simpl in H7. destruct H6, H7. 
    assert ([y, f[y]] ∈ f /\ [z, f[z]] ∈ f). 
    { split; eapply Property_Value; eauto. } destruct H10.
    assert ([y, x] ∈ f /\ [y, f [y]] ∈ f). {tauto. }
    assert ([z, x] ∈ f /\ [z, f [z]] ∈ f). {tauto. }
    apply H0 in H12. apply H0 in H13.
    assert (f[y] ≠ f[z]). { apply H4; auto. } rewrite <- H12 in H14.
    rewrite <- H13 in H14. contradiction. }
    split; split; auto; intros.
  - exists f[y]. eapply Property_Value in H2; eauto. generalize H2; intros.
    apply H1 in H2. apply -> AxiomII_P in H2. simpl in H2. split; try tauto.
    apply AxiomII_P; auto.
  - eapply Property_Value in H2; eauto. eapply Property_Value in H3; eauto.
    generalize (classic ((f ﹣¹) [x1] = (f ﹣¹) [x2])). intros. destruct H5;
    auto. apply -> AxiomII_P in H2. simpl in H2. apply -> AxiomII_P in H3;
    simpl in H3.
    assert ([(f ﹣¹) [x1], x1] ∈ f /\ [(f ﹣¹) [x2], x2] ∈ f ). {tauto. }
    rewrite H5 in H6. apply H in H6. contradiction.
Qed.


(* 定理1.2.1 *)
Theorem Theorem1_2_1: forall (A B : Type)(X: Ensemble A)(Y: Ensemble B)
  (f: Ensemble (prod A B)),
  mapping X Y f -> (∃g, bijective X Y f <-> (mapping Y X g /\
  g ◦ f = id[ X ] /\ f ◦ g = id[ Y ])).
Proof.
  intros. exists f ﹣¹. split; intros.
  - generalize H0; intros. unfold bijective in H0; destruct H0.
    unfold surjective in H0; unfold injective in H2; destruct H0,H2.
    generalize H1; intros. apply Lemma1_2_1'' in H5. 
    destruct H5, H5. split; auto. clear H6 H7. split. 
    + unfold Composition. apply AxiomI; split; intros.
      * destruct z. apply -> AxiomII_P in H6; simpl in H6.
        destruct H6,H6. apply Lemma1_2_1 with (X:=X)(Y:=Y) in H6; auto.
        assert([x0, x] ∈ f ﹣¹ /\ [x0, y] ∈ f ﹣¹). { tauto. }
        apply H5 in H6. apply -> AxiomII_P in H6; simpl in H6; destruct H6.
        apply H5 in H7. apply -> AxiomII_P in H7; simpl in H7; destruct H7.
        apply H5 in H8. apply AxiomII_P. auto.
      * destruct z. apply AxiomII_P; apply -> AxiomII_P in H6; simpl in H6;
        destruct H6, H7. exists f[ x ]; split.
        -- apply Property_Value with(X := X)(Y := Y); auto.
        -- apply AxiomII_P. rewrite H8.
           apply Property_Value with(X := X)(Y := Y); auto.
    + unfold Composition. apply AxiomI; split; intros.
      * destruct z. apply -> AxiomII_P in H6; simpl in H6.
        destruct H6,H6. apply -> AxiomII_P in H6; simpl in H6.
        assert([x0, x] ∈ f /\ [x0, y] ∈ f). { tauto. }
        apply H in H6; apply -> AxiomII_P in H6; simpl in H6; destruct H6.
        apply H in H7; apply -> AxiomII_P in H7; simpl in H7; destruct H7.
        apply H in H8. apply AxiomII_P. auto.
      * destruct z. apply AxiomII_P; apply -> AxiomII_P in H6; simpl in H6;
        destruct H6, H7. exists f ﹣¹[ x ]; split.
        -- apply Property_Value with(X := Y)(Y := X); auto.
        -- apply Lemma1_2_1' with(X := X)(Y := Y); auto. rewrite H8.
           apply Property_Value with(X := Y)(Y := X); auto.
  - destruct H0, H1. split; split; auto. intros.
    + exists f ﹣¹[y]. assert ( [y , (f ﹣¹) [y]] ∈f ﹣¹ ). 
      eapply Property_Value in H3; eauto. generalize H4; intros. apply H0 in H4.
      apply -> AxiomII_P in H4. simpl in H4. destruct H4. 
      apply -> AxiomII_P in H5; simpl in H5. auto.
    + intros. generalize (classic (f[x1] = f[x2])). intros. destruct H6; auto.
      assert ([x1, f[x1]] ∈ f /\ [x2, f[x2]] ∈ f ).
      split; eapply Property_Value; eauto. destruct H7. rewrite H6 in H7.
      assert ([f[x2], x1] ∈ f ﹣¹ /\ [f[x2], x2] ∈ f ﹣¹). { split; 
      apply AxiomII_P; auto. } apply H0 in H9. contradiction.
Qed.

Lemma Lemma1_2_1'''' : forall(A B : Type)(f:Ensemble (prod A B))
  (g:Ensemble (prod B A))(h:Ensemble (prod B A)), (g ◦ (f ◦ h) = (g ◦ f) ◦ h).
Proof.
  intros; apply AxiomI; split; intros.
  - destruct z. apply -> AxiomII_P in H; simpl in H; destruct H,H.
    apply -> AxiomII_P in H; simpl in H; destruct H,H.
    apply AxiomII_P; exists x1; split; auto. apply AxiomII_P; exists x0; auto.
  - destruct z. apply -> AxiomII_P in H; simpl in H; destruct H,H.
    apply -> AxiomII_P in H0; simpl in H0; destruct H0,H0.
    apply AxiomII_P; exists x1; split; auto. apply AxiomII_P; exists x0; auto.
Qed.

Theorem Theorem1_2_1' : forall (A B : Type)(X: Ensemble A)(Y: Ensemble B)f g h ,
  mapping X Y f -> (mapping Y X g /\ g ◦ f = id[ X ] /\ f ◦ g = id[ Y ]) /\
  (mapping Y X h /\ h ◦ f = id[ X ] /\ f ◦ h = id[ Y ]) -> g = h.
Proof.
  intros. destruct H0,H0,H2,H1,H4.
  assert(g = g ◦ id[Y]).
  { apply AxiomI; intros; split; intros.
    - destruct z; apply AxiomII_P. exists x; split; auto. apply AxiomII_P.
      apply H0 in H6; apply -> AxiomII_P in H6; simpl in H6. tauto.
    - destruct z; apply -> AxiomII_P in H6; simpl in H6; destruct H6,H6.
      apply -> AxiomII_P in H6; simpl in H6; destruct H6,H8.
      rewrite H9; auto. }
  rewrite <- H5 in H6. rewrite Lemma1_2_1'''' in H6. rewrite H2 in H6.
  assert(h = id[X] ◦ h).
  { apply AxiomI; intros; split; intros.
    - destruct z; apply AxiomII_P. exists y; split; auto. apply AxiomII_P.
      apply H1 in H7; apply -> AxiomII_P in H7; simpl in H7. tauto.
    - destruct z; apply -> AxiomII_P in H7; simpl in H7; destruct H7,H7.
      apply -> AxiomII_P in H8; simpl in H8; destruct H8,H9.
      rewrite <- H10; auto. }
  rewrite H7; auto.
Qed.

End H12.
Export H12.





