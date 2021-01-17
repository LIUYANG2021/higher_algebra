Require Export Classical.
Require Export Lia.

(* H_1_1 集合 *)
Module H11.

Set Implicit Arguments.

Notation "'Ɐ' x .. y , P" := (forall x, .. (forall y, P) ..)
(at level 200, x binder, y binder, right associativity,
format "'[' 'Ɐ' x .. y ']' , P") : type_scope. 

Notation "'∃' x .. y , P" := (exists x, .. (exists y, P) ..)
(at level 200, x binder, y binder, right associativity,
format "'[ ' '∃' x .. y ']' , P") : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
(at level 200, x binder, y binder, right associativity,
format "'[ ' 'λ' x .. y ']' , t").

Proposition Lemma_x : forall A: Prop, A -> A /\ A.
Proof. intros; split; auto. Qed.

Ltac double H := apply Lemma_x in H; destruct H.

(* 1.定义集合类型 *)
Parameter Ensemble : Type -> Type.

(* 2.定义属于∈:  x∈y : In x y  *)
Parameter In : Ɐ (A: Type), A -> (Ensemble A) -> Prop.
Notation "a ∈ A" := (In a A) (at level 10).

(* 3.外延公理 *)
Axiom AxiomI : Ɐ (A: Type) (X Y: (Ensemble A)),
  X = Y <-> (Ɐ z : A, z ∈ X <-> z ∈ Y).

(* 4.定义子集：x是y的子集 <-> (Ɐz: z∈x -> z∈y) *)
Definition Included (A: Type)(X Y: Ensemble A) : Prop := forall z, z ∈ X -> z ∈ Y.
Notation "X ⊂ Y" := (Included X Y)(at level 70).

(* 5.分类符号{...:...} ： {所有……的集使得……} *)
Parameter Classifier : Ɐ(A: Type)(P: A -> Prop), (Ensemble A).
Notation "\{ P \}" := (Classifier P) (at level 0).

(* 6.分类公理图式 *)
Axiom AxiomII : Ɐ(A : Type)(x: A) (P: A -> Prop),
 x ∈ \{ P \} <-> (P x).

(* 7.定义并集  x∪y = {z:z∈x或者z∈y} *)
Definition Union(A: Type)(x y: (Ensemble A)) : (Ensemble A) :=
  \{ λ z, z ∈ x \/ z ∈ y \}.
Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

(* 8.定义交集  x∩y = {z:z∈x同时z∈y} *)
Definition Intersection(A: Type)(x y: (Ensemble A)) : (Ensemble A) :=
  \{ λ z, z ∈ x /\ z ∈ y \}.
Notation "x ∩ y" := (Intersection x y) (at level 60, right associativity).

(* 补充定义  x≠y <-> ~(x=y) *)
Definition Inequality(A: Type) (x y: A) : Prop := ~ (x = y).
Notation "x ≠ y" := (Inequality x y) (at level 70).

(* 9.定义空集  Φ={x:x≠x} *)
Definition Φ (A: Type) := \{ λ x: A, x ≠ x \}.

(* 补充定义  ¬x={y：y∉x} *)
Definition NotIn(A: Type)(x: A)(y: Ensemble A): Prop := ~ x ∈ y.
Notation "x ∉ y" := (NotIn x y) (at level 10).

Definition Complement(A: Type)(x: Ensemble A): Ensemble A := \{ λ y: A, y ∉ x \}.
Notation "¬ x" := (Complement x) (at level 5, right associativity).

Definition Singleton (A: Type)(x: A): (Ensemble A) := \{ λ z, z = x \}.
Notation "[ x ]" := (Singleton x) (at level 0, right associativity).


(* 10.定义差集  x~y=x∩(¬ y) *)
Definition Setminus(A: Type)(x y: Ensemble A): Ensemble A := x ∩ (¬ y).
Notation "x ~ y" := (Setminus x y) (at level 50, left associativity).

(* 补充定义全域 U={x:x=x} *)
Definition U(A:Type) := \{ λ x: A, x = x \}.

(* 补充定义有序数对 *)
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Notation "[ x , y ]" := (pair x y).

Definition fst (X Y : Type) (p : (prod X Y)) : X :=
  match p with
  | [x, y] => x
  end.

Definition snd (X Y : Type) (p : prod X Y) : Y :=
  match p with
  | [x, y] => y
  end.

(* 11.定义笛卡尔积 *)
Parameter Classifier_P : Ɐ(A B: Type)(P: A -> B -> Prop), Ensemble(prod A B).
Notation "\{\ P \}\" := (Classifier_P P)(at level 0).

Definition Cartesian (A B: Type)(X: Ensemble A)(Y: Ensemble B) :=
  \{\ λ u v, u∈X /\ v∈Y \}\.
Notation "X × Y" := (Cartesian X Y)(at level 2, right associativity).


End H11.
Export H11.



















