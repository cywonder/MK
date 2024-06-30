 Require Export A_3.

(*A.4 集的存在性 *)

Module A4.

(* 子集公理III 如果x是一个集，存在一个集y使得对于每个z，假定z⊂x，则z∈y *)

Axiom AxiomIII : forall (x: Class),
  Ensemble x -> exists y, Ensemble y /\ (forall z, z⊂x -> z∈y).



(* 定理33  如果x是一个集同时z⊂x，则z是一个集 *)

Theorem Theorem33 : forall x z,
  Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros. apply AxiomIII in H. destruct H.
  destruct H. apply H1 in H0. unfold Ensemble. exists x0.
  apply H0.
Qed.

(* 定理34  0=∩μ同时∪μ =μ *)

Theorem Theorem34 : Φ = ∩μ.
Proof.
  intros; apply AxiomI; split; intros.
  - generalize (Theorem16 z); contradiction.
  - apply AxiomII in H; destruct H; apply H0.
    apply Theorem19. generalize (Theorem26 z). intros.
    apply Theorem33 in H1. auto. auto.
Qed.

Theorem Theorem34' : μ = ∪μ.
Proof.
  apply Theorem27. split.
  - red. intros. apply AxiomII in H.
    destruct H as [H _]. double H. apply AxiomIII in H.
    repeat destruct H.
    apply AxiomII. split. auto.
    exists x. split. apply H1.
    unfold Included. auto. apply Theorem19.
    Ens.
  - apply Theorem26'.
Qed.

(* 用AxiomI去做的 *)
(* apply AxiomI. split. intros.
  - double H. apply AxiomII in H. destruct H. apply AxiomII.
    split. try auto. generalize (AxiomIII z H). intros.
    destruct H2; destruct H2; exists x; split.
    + apply H3; unfold Included; auto.
    + apply Theorem19; auto.
  - intros. apply AxiomII in H; destruct H; apply Theorem19; auto.
Qed. *)


(* 定理35  如果x≠0，则∩x是一个集 *)

Lemma Lemma35 : forall x, x ≠ Φ <-> exists z, z∈x.
Proof.
  intros. assert (x = Φ <-> ~ (exists y, y∈x)).
  { split; intros.
    - intro. destruct H0. rewrite H in H0.
      apply AxiomII in H0. destruct H0. contradiction.
    - apply AxiomI. split; intros.
      + elim H. exists z. auto.
      + generalize (Theorem16 z). contradiction. }
  split; intros.
  - apply Lemma_z with (B:= ~(exists y, y∈x)) in H0; auto;
    apply NNPP in H0; destruct H0. exists x0. auto.
  - apply Lemma_z with (A:=(~ (exists y, y∈x))); auto.
    destruct H; split; auto.
Qed.

Theorem Theorem35 : forall x, x ≠ Φ -> Ensemble (∩x).
Proof.
  intros; apply Lemma35 in H; destruct H. AssE x0.
  generalize (Theorem32 x0 x H); intros.
  destruct H1; apply Theorem33 in H2; auto.
Qed.

(* 定义36  pow(x)={y:y⊂x} *)

Definition PowerSet x : Class := \{ λ y, y ⊂ x \}.

Notation "pow( x )" := (PowerSet x) (at level 0, right associativity).

(* Hint Unfold PowerSet : set. *)


(* 定理37  u=pow(u) *)

Theorem Theorem37 : μ = pow(μ).
Proof.
  apply AxiomI; split; intros.
  - apply AxiomII; split; Ens; apply Theorem26'.
  - apply AxiomII in H; destruct H; apply Theorem19; auto.
Qed.

(* Hint Rewrite Theorem37 : set. *)


(* 定理38  如果x是一个集,则pow(x)是一个集*)

Theorem Theorem38 : forall x y,
  Ensemble x -> Ensemble pow(x) /\ (y ⊂ x <-> y ∈ pow(x)).
Proof.
  intros; split.
  - apply AxiomIII in H; destruct H, H.
    assert (pow(x) ⊂ x0).
    { unfold Included. intros. apply AxiomII in H1.
      destruct H1. apply H0 in H2. auto. }
    apply Theorem33 in H1; auto.
  - split; intros.
    + apply Theorem33 with (z:=y) in H; auto.
      apply AxiomII; split; auto.
    + apply AxiomII in H0; apply H0.
Qed.

(* 定理39  μ不是一个集 *)

(* 一个不是集的类 *)

Lemma Lemma_N : ~ Ensemble \{ λ x, x ∉ x \}.
Proof.
  pose proof (classic (\{ λ x, x ∉ x \} ∈ \{ λ x, x ∉ x \})).
  destruct H.
  - pose proof H. apply AxiomII in H. destruct H. contradiction.
  - intro. apply H. apply AxiomII. split. auto. auto.
Qed.

Theorem Theorem39 : ~ Ensemble μ.
Proof.
  unfold not. intros. generalize Lemma_N. intros.
  generalize (Theorem26' \{ λ x, x ∉ x \}); intros.
  apply Theorem33 in H1; auto.
Qed.

End A4.

Export A4.


