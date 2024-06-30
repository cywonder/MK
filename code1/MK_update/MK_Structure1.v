(** MK_Structure1 *)

(* MK_Definitions_Axioms *)

Require Export Pre_MK_Logic.

(* Class mk_structure := {
  Class : Type;
  In : Class -> Class -> Prop;
  Classifier : (Class -> Prop) -> Class }.

Parameter MKS: mk_structure. *)

Parameter Class : Type.

Parameter In : Class -> Class -> Prop.
Notation "x ∈ y" := (In x y) (at level 70).

Parameter Classifier : (Class -> Prop) -> Class.
Notation "\{ P \}" := (Classifier P) (at level 0).

(* Declare Scope mk_scope.
Delimit Scope mk_scope with MK.
Open Scope mk_scope. *)
Definition Ensemble x := ∃ y, x ∈ y.

Global Hint Unfold Ensemble : core.

(* 并 x∪y = {z:z∈x或者z∈y} *)
Definition Union x y := \{ λ z, z ∈ x \/ z ∈ y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

(* 定义3  交 x∩y = {z:z∈x同时z∈y} *)
Definition Intersection x y := \{ λ z, z ∈ x /\ z ∈ y \}.

Notation "x ∩ y" := (Intersection x y) (at level 60, right associativity).

(* 定义9  x∉y当且仅当x∈y不真 *)
Definition NotIn x y := ~ (x ∈ y).

Notation "x ∉ y" := (NotIn x y) (at level 10).

(* 定义10  ¬x={y：y∉x} *)
Definition Complement x := \{λ y, y ∉ x \}.

Notation "¬ x" := (Complement x) (at level 5, right associativity).

(* 定义13  x~y=x∩(¬ y) *)
Definition Setminus x y := x ∩ (¬ y).

Notation "x ~ y" := (Setminus x y) (at level 50, left associativity).

(* 定义85  x≠y 当且仅当 x=y 不真 *)
Notation "x ≠ y" := (~ (x = y)) (at level 70).

(* 定义15  Φ={x:x≠x} *)
Definition Φ := \{λ x, x ≠ x \}.

(* 定义18  全域 μ={x:x=x} *)
Definition μ := \{ λ x, x = x \}.

(* 定义22  ∩x={z:对于每个y，如果y∈x，则z∈y} *) 
Definition Element_I x := \{ λ z, ∀ y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x) (at level 66).

(* 定义23  ∪x={z:对于某个y，z∈y同时y∈x} *)
Definition Element_U x := \{ λ z, ∃ y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x) (at level 66).

(* 定义25  x⊂y 当且仅当对于每个z，如果z∈x，则z∈y *)
Definition Included x y := ∀ z, z ∈ x -> z ∈ y.

Notation "x ⊂ y" := (Included x y) (at level 70).

(* 定义36  pow(x)={y:y⊂x} *)
Definition PowerClass x := \{ λ y, y ⊂ x \}.

Notation "pow( x )" := (PowerClass x)
  (at level 0, right associativity).

Class MK_Axioms :Prop:= {
  A_I : ∀ x y, x = y <-> (∀ z, z ∈ x <-> z ∈ y);
  A_II : ∀ b P, b ∈ \{ P \} <-> Ensemble b /\ (P b);
  A_III : ∀ {x}, Ensemble x -> ∃ y, Ensemble y /\ (∀ z, z ⊂ x -> z ∈ y);
  A_IV : ∀ {x y}, Ensemble x -> Ensemble y -> Ensemble (x ∪ y) }.


Parameter MK_Axiom : MK_Axioms.

Notation AxiomI := (@ A_I MK_Axiom).
Notation AxiomII := (@ A_II MK_Axiom).
Notation AxiomIII := (@ A_III MK_Axiom).
Notation AxiomIV := (@ A_IV MK_Axiom).

Ltac eqext := apply AxiomI; split; intros.

Ltac appA2G := apply AxiomII; split; eauto.

Ltac appA2H H := apply AxiomII in H as [].
