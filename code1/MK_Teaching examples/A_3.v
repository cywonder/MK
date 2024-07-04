Require Export A_2.

(* A.3 类的初等代数 *)

Module A3.

(* 定理2  并集 x∪y = {z:z∈x或者z∈y} *)

Definition Union x y : Class := \{ λ z, z∈x \/ z∈y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

(* 定义3  交集 x∩y = {z:z∈x同时z∈y} *)
Definition Intersection x y : Class := \{ λ z, z∈x /\ z∈y \}.

Notation "x ∩ y" := (Intersection x y) (at level 60, right associativity).


(* 定理4  z∈x∪y当且仅当z∈x或者z∈y，而z∈x∩y当且仅当z∈x同时z∈y *)

Theorem Theorem4 : forall (x y: Class) (z: Class),
  z∈x \/ z∈y <-> z ∈ (x ∪ y).
Proof.
  intros. split.
  - intros. apply AxiomII. split.
    + destruct H. unfold Ensemble. exists x. apply
      H. exists y. apply H.
    + apply H.
  - intros. apply AxiomII in H. apply H.
Qed.

Theorem Theorem4' : forall x y z, z∈x /\ z∈y <-> z∈(x∩y).
Proof.
  intros. split.
  - intros. apply AxiomII. split.
    + unfold Ensemble. exists x. apply H.
    + apply H.
  - intros. apply AxiomII in H. apply H.
Qed.

(* 定理5  x∪x=x同时x∩x=x *)

Theorem Theorem5 : forall x, x ∪ x = x.
Proof.
  intros. apply AxiomI. split.
  - intros. apply Theorem4 in H. destruct H. apply H. apply H.
  - intros. apply Theorem4.
    left. apply H.
Qed.

Theorem Theorem5' : forall x, x ∩ x = x.
Proof. 
  intros. apply AxiomI. split.
  - intros. apply Theorem4' in H. destruct H. apply H.
  - intros. apply Theorem4'. split. apply H. apply H.
Qed.

(* 定理6  x∪y=y∪x同时x∩y=y∩x *)

Theorem Theorem6 : forall x y, x ∪ y = y ∪ x.
Proof.
 intros. apply AxiomI. split.
 - intros. apply Theorem4 in H. apply  Theorem4. intuition.
 - intros. apply Theorem4 in H. apply  Theorem4. intuition.
Qed.

Theorem Theorem6' : forall x y, x ∩ y = y ∩ x.
Proof.
  intros. apply AxiomI. split.
  - intros. apply Theorem4' in H. apply  Theorem4'. destruct H. split.
    apply H0. apply H.
  - intros.  apply Theorem4' in H. apply  Theorem4'. destruct H. split.
    apply H0. apply H.
Qed.

(* 定理7  (x∪y)∪z=x∪(y∪z)同时(x∩y)∩z=x∩(y∩z) *)

Theorem Theorem7 : forall x y z, (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros. apply AxiomI. split.
  - intros. apply Theorem4 in H. apply Theorem4. destruct H.
    + apply Theorem4 in H. destruct H.
      * left. apply H.
      * intros. right. apply Theorem4. left. apply H.
    + right. apply Theorem4. right. apply H.
  - intros.  apply Theorem4 in H. apply Theorem4. destruct H.
    + left. apply Theorem4. left. apply H.
    + apply Theorem4 in H. destruct H.
      * left.  apply Theorem4. right. apply H.
      * right. apply H.
Qed.

Theorem Theorem7' : forall x y z, (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros. apply AxiomI. split.
  - intros. apply Theorem4' in H. apply Theorem4'. destruct H. split.
    + intros. apply AxiomII in H. destruct H. destruct H1. apply H1.
    + intros. apply AxiomII in H.  apply AxiomII. destruct H. destruct H1. split.
      * apply H.
      * split. apply H2. apply H0.
 - intros. apply Theorem4' in H. apply Theorem4'. destruct H. split.
    + apply AxiomII in H0.  apply AxiomII. destruct H0. split.
      * apply H0.
      * split.
        -- apply H.
        -- destruct H1. apply H1.
    + apply AxiomII in H0. destruct H0. destruct H1. apply H2.
Qed.

(* 定理8  x∩(y∪z)=(x∩y)∪(x∩z)同时x∪(y∩z)=(x∪y)∩(x∪z) *)

Theorem Theorem8 : forall x y z, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; apply AxiomI; split; intros.
  - apply Theorem4. apply Theorem4' in H. destruct H.
    apply Theorem4 in H0; destruct H0.
    + left; apply Theorem4'; split; auto.
    + right; apply Theorem4'; split; auto.
  - apply Theorem4 in H; apply Theorem4'; destruct H.
    + apply Theorem4' in H; destruct H; split; auto.
      apply Theorem4; left; auto.
    + apply Theorem4' in H; destruct H; split; auto.
      apply Theorem4; right; auto.
Qed.

Theorem Theorem8' : forall x y z, x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  intros. apply AxiomI. split.
  - intros. apply AxiomII in H. apply AxiomII. split.
    + destruct H. apply H.
    + destruct H. split.
      * apply AxiomII. split.
        -- apply H.
        --  destruct H0. left. apply H0. apply AxiomII in H0. destruct H0.
             destruct H1. right. apply H1.
      * apply AxiomII. split.
        --  apply H.
        --  destruct H0. left. apply H0. apply AxiomII in H0. destruct H0.
            destruct H1. right. apply H2.
  - intros.  apply AxiomII in H. apply AxiomII. split.
    + destruct H. apply H.
    + destruct H. destruct H0. apply AxiomII in H0. destruct H0. destruct H2.
      left. apply  H2. apply AxiomII in H1.  destruct H1. destruct H3. left.
      apply H3. right. apply AxiomII. split.
      * apply H.
      * split. apply H2. apply H3.
Qed.

(* 定义9  x∉y当且仅当x∈y不真 *)

Definition NotIn x y : Prop := ~ x∈y.

Notation "x ∉ y" := (NotIn x y) (at level 10).


(* 定义10  ¬x={y：y∉x} *)

Definition Complement x : Class := \{λ y, y ∉ x \}.

Notation "¬ x" := (Complement x) (at level 5, right associativity).

(* 定理11  ¬ (¬ x) = x *)

Theorem Theorem11: forall x, ¬ (¬ x) = x.
Proof.
  intros. apply AxiomI. split.
  - intros. apply AxiomII in H. unfold NotIn in H. destruct H.
    assert (z ∈ ¬ x <-> Ensemble z /\ z∉x ).
     { split.
       - intros. apply AxiomII in H1. apply H1.
       - intros. apply AxiomII. apply H1. }
     apply Lemma_z in H1. apply not_and_or in H1. destruct H1.
     + contradiction.
     + unfold NotIn in H1. apply NNPP in H1. apply H1.
     + apply H0.
  - intros. apply AxiomII. split. Ens. unfold NotIn. intro.
    apply AxiomII in H0. destruct H0. contradiction.
Qed.

(* 定理12  De Morgan   ¬(x∪y)=(¬x)∩(¬y)同时¬(x∩y)=(¬x)∪(¬y) *)

Theorem Theorem12 : forall x y, ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros. apply AxiomI. split.
  - intros. apply AxiomII in H. destruct H. unfold NotIn in H0.
    apply Lemma_z with (B:= z∈x \/ z∈y )in H0.
    + apply not_or_and in H0. destruct H0. apply Theorem4'. split.
      * apply AxiomII. unfold NotIn. auto.
      * apply AxiomII. unfold NotIn. auto.
    + split. apply Theorem4. intros. apply Theorem4. apply H1.
  - intros. apply Theorem4' in H. apply AxiomII. split. destruct H.
    Ens. unfold NotIn.
    apply Lemma_z with (A:= z∈x \/ z∈y ).
    + split. intros.
      apply Theorem4. apply H0. intros.
      apply Theorem4 in H0. apply H0.
    + apply and_not_or. destruct H. apply AxiomII in H, H0.
      destruct H, H0. unfold NotIn in H1, H2.
      split. apply H1. apply H2.
Qed.

Theorem Theorem12' : forall x y, ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros; generalize (Theorem4' x y); intros.
  apply AxiomI; split; intro.
  - apply AxiomII in H0; unfold NotIn in H0; destruct H0.
    apply Lemma_z with (B:= z∈x /\ z∈y) in H1.
    + apply Theorem4; apply not_and_or in H1; destruct H1.
      * left; apply AxiomII; split; auto.
      * right; apply AxiomII; split; auto.
    + split; apply H.
  - apply AxiomII; split; Ens.
    unfold NotIn; apply Lemma_z with (A:= z∈x /\ z∈y); auto.
    apply or_not_and; apply Theorem4 in H0; destruct H0.
    + apply AxiomII in H0; unfold NotIn in H0; tauto.
    + apply AxiomII in H0; unfold NotIn in H0; tauto.
Qed.

(* 定义13  x~y=x∩(¬ y) *)

Definition Setminus x y : Class := x ∩ (¬ y).

Notation "x ~ y" := (Setminus x y) (at level 50, left associativity).

(* 定理14  x∩(y~z)=(x∩y)~z *)

Theorem Theorem14 : forall x y z, x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  intros. unfold Setminus. rewrite Theorem7'. auto.
Qed.

(* 定义15  x≠y 当且仅当 x=y 不真 *)

Definition Inequality (x y: Class) : Prop := ~ (x = y).

Notation "x ≠ y" := (Inequality x y) (at level 70).

Corollary Property_Ineq : forall x y, (x ≠ y) <-> (y ≠ x).
Proof.
 intros; split; intros; intro; apply H; auto.
Qed.

(* 定义15  Φ={x:x≠x} *)

Definition Φ : Class := \{λ x, x ≠ x \}.

(* 定理16  x∉Φ *)

Theorem Theorem16 : forall x, x ∉ Φ.
Proof.
  intros. unfold NotIn. intro. apply AxiomII in H. destruct H.
  contradiction.
Qed.

(* 定理17  Φ∪x=x同时Φ∩x=Φ *)

Theorem Theorem17 : forall x, Φ ∪ x = x.
Proof.
  intros. apply AxiomI. split. 
  - intros. apply Theorem4 in H. destruct H.
    + generalize (Theorem16 z). intros.  contradiction.
    +  auto.
  - intros. apply Theorem4. auto.
Qed.

Theorem Theorem17' : forall x, Φ ∩ x = Φ.
Proof.
  intros. apply AxiomI. split.
  -  intros. apply Theorem4' in H. destruct H. apply H.
  -  intros.  apply Theorem4'. split.
     + auto.
     + generalize (Theorem16 z). intros. contradiction.
Qed.

(* 定义18  全域 μ={x:x=x} *)

Definition μ : Class := \{ λ x, x = x \}.

Corollary Property_μ : forall x, x ∪ (¬ x) = μ.
Proof. intros. apply AxiomI. split.
  - intros. apply Theorem4 in H. destruct H.
    + apply AxiomII. split.
      * unfold Ensemble. exists x. apply H.
      * auto.
    + apply AxiomII. split.
      * unfold Ensemble. exists ¬x. apply H.
      * auto.
  - intros.  apply Theorem4. apply AxiomII in H. destruct H.
    generalize (classic (z∈x)). intros. destruct H1.
    + auto.
    + right. apply AxiomII. split. apply H. unfold NotIn. auto.
Qed.

(* 定理19  x∈μ当且仅当x是一个集  *)

Theorem Theorem19 : forall x, x ∈ μ <-> Ensemble x.
Proof. intros. split.
  - intros. Ens.
  - intros. apply AxiomII. auto.
Qed.

(* 定理20  x∪μ=μ同时x∩μ=x *)

Theorem Theorem20 : forall x, x ∪ μ = μ.
Proof. intros. apply AxiomI. split.
  - intros. apply Theorem4 in H. destruct H.
    + apply Theorem19. Ens.
    + auto.
  - intros. apply Theorem4. auto.
Qed.

Theorem Theorem20' : forall x, x ∩ μ = x.
Proof. intros. apply AxiomI. split.
  - intros. apply Theorem4' in H. destruct H. auto.
  - intros. apply Theorem4'. split. auto. apply Theorem19. Ens.
Qed.

(* 定理21  ¬Φ=μ同时¬μ=Φ *) 

Theorem Theorem21 : ¬ Φ = μ.
Proof. intros. apply AxiomI. split.
  - intros. apply AxiomII in H. destruct H. apply Theorem19. auto.
  - intros. apply Theorem19 in H. apply AxiomII. split. auto. 
    apply Theorem16.
Qed.

Theorem Theorem21' : ¬ μ = Φ.
Proof. intros. apply AxiomI. split.
  - intros. apply AxiomII in H. destruct H. apply Theorem19 in H.
    contradiction.
  - intros. apply AxiomII in H. destruct H. contradiction.
Qed.

(* 定义22  ∩x={z:对于每个y，如果y∈x，则z∈y} *) 

Definition Element_I x : Class := \{ λ z, forall y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x) (at level 66).


(* 定义23  ∪x={z:对于某个y，z∈y同时y∈x} *)

Definition Element_U x : Class := \{ λ z, exists y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x) (at level 66).

(* 定理24  ∩Φ=μ同时∪Φ=Φ *)

Theorem Theorem24 : ∩ Φ = μ.
Proof. 
  intros. apply AxiomI. split.
  - intros. apply Theorem19. Ens.
  - intros. apply AxiomII. split. Ens. intros. 
    generalize (Theorem16 y). intros. contradiction.
Qed.

Theorem Theorem24' : ∪ Φ = Φ.
Proof. 
  intros. apply AxiomI. split. 
  - intros. apply AxiomII in H. destruct H. destruct H0. destruct H0. 
    generalize (Theorem16 x). intros. contradiction.
  - intros. generalize (Theorem16 z). intros. contradiction.
Qed.

(* 定义25  x⊂y 当且仅当对于每个z，如果z∈x，则z∈y *)

Definition Included x y : Prop := forall z, z∈x -> z∈y.

Notation "x ⊂ y" := (Included x y) (at level 70).

(* 定理26  Φ⊂x同时x⊂μ *)

Theorem Theorem26 : forall x, Φ ⊂ x.
Proof. 
  intros. unfold Included. intros.
  generalize (Theorem16 z). contradiction.
Qed.

Theorem Theorem26' : forall x, x ⊂ μ.
Proof.
  intros. unfold Included. intros. apply Theorem19. Ens.
Qed.

(* 定理27  x=y当且仅当x⊂y同时y⊂x *)

Theorem Theorem27 : forall x y, (x ⊂ y /\ y ⊂ x) <-> x=y.
Proof. intros. split.
  - intros. destruct H. apply AxiomI. split.
    + unfold Included in H. auto.
    + unfold Included in H0. auto.
  - intros. rewrite H.  split; unfold Included; auto.
Qed.

(* 定理28  如果x⊂y且y⊂z，则x⊂z *)

Theorem Theorem28 : forall x y z, x ⊂ y /\ y ⊂ z -> x ⊂ z.
Proof.
  intros. destruct H. unfold Included.  auto.
Qed.

(* 定理29  x⊂y当且仅当x∪y=y *)

Theorem Theorem29 : forall x y, x ∪ y = y <-> x ⊂ y.
Proof. intros. split.
  - intros. unfold Included. intros. apply AxiomI with (z:=z) in H.
    apply H. apply Theorem4. auto.
  - intros. apply AxiomI. intros. split.
    + intros. apply Theorem4 in H0. destruct H0; auto.
    + intros. apply Theorem4. auto.
Qed.

(* 定理30  x⊂y当且仅当x∩y=x *)

Theorem Theorem30 : forall x y, x ∩ y = x <-> x ⊂ y.
Proof.
  intros. split.
  - intros. unfold Included. intros. apply AxiomI with (z:=z) in H.
    apply H in H0. apply Theorem4' in H0. destruct H0. auto.
  - intros. apply AxiomI. intros. split.
    + intros. apply Theorem4' in H0. destruct H0. auto.
    + intros. apply Theorem4'. split;  auto.
Qed.

(* 定理31  如果x⊂y,则∪x⊂∪y同时∩y⊂∩x *)

Theorem Theorem31 : forall x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  intros. split.
    - unfold Included in H. unfold Included. intros. apply AxiomII
      in H0. destruct H0, H1, H1. apply AxiomII. split. auto.
      exists x0. auto.
    - unfold Included in H. unfold Included. intros. apply AxiomII
      in H0. destruct H0. apply AxiomII. split. auto. intros.
      apply H1. apply  H in H2. auto.
Qed.


(* 定理32  如果x∈y,则x⊂∪y同时∩y⊂x *)

Theorem Theorem32 : forall x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof. intros. split.
  - unfold Included. intros. apply AxiomII. split. Ens. exists x.
    auto.
  - unfold Included. intros. apply AxiomII in H0. destruct H0.
    apply H1 in H. auto.
Qed.

(* Proper Subset *)

Definition ProperIncluded x y : Prop := x ⊂ y /\ x ≠ y.

Notation "x ⊊ y" := (ProperIncluded x y) (at level 70).

Corollary Property_ProperIncluded : forall (x y: Class),
  x ⊂ y -> (x ⊊ y) \/ x = y.
Proof.
  intros.
  generalize (classic (x = y)); intros.
  destruct H0; auto.
  left; unfold ProperIncluded; auto.
Qed.

Corollary Property_ProperIncluded' : forall (x y: Class),
  x ⊊ y -> exists z, z ∈ y /\ z ∉ x.
Proof.
  intros.
  unfold ProperIncluded in H; destruct H.
  generalize (Theorem27 x y); intros.
  apply Lemma_z with (B:= (x ⊂ y /\ y ⊂ x)) in H0; try tauto.
  apply not_and_or in H0; destruct H0; try tauto.
  unfold Included in H0. apply not_all_ex_not in H0. destruct H0.
  Check not_all_ex_not.
  apply imply_to_and in H0. Check imply_to_and. Ens.
Qed.

(* Property_Φ *)

Lemma Property_Φ : forall x y, y ⊂ x -> x ~ y = Φ <-> x = y.
Proof.
  intros; split; intros.
  - apply Property_ProperIncluded in H; destruct H; auto.
    apply Property_ProperIncluded' in H; destruct H as [z H], H.
    assert (z ∈ (x ~ y)).
    { unfold Setminus; apply Theorem4'; split; auto.
      unfold Complement; apply AxiomII; split; Ens. }
    rewrite H0 in H2; generalize (Theorem16 z); intros.
    contradiction.
  - rewrite <- H0; apply AxiomI; split; intros.
    + unfold Setminus in H1; apply Theorem4' in H1.
      destruct H1; unfold Complement in H2.
      apply AxiomII in H2; destruct H2; contradiction.
    + generalize (Theorem16 z); intros; contradiction.
Qed.


End A3.

Export A3.
