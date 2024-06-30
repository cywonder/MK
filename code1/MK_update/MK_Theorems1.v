(** MK_Theorems1 *)

(*读入库文件*)
Require Export MK_Structure1.

(* A.1 分类公理图式 *)
(* 外延公理I 对于每个x与y，x=y成立之充分必要条件是对每一个z当且仅当z∈x时，z∈y *)
(* 定义1  集 x是集当且仅当∃ y, x ∈ y *)
(* A.2 分类公理图式续 *)
(* 分类公理II *)
(* A.3 类的初等代数 *)
(* 定义2  并集 x∪y = {z:z∈x或者z∈y} *)
(* 定义3  交集 x∩y = {z:z∈x同时z∈y} *)

(* 定理4  z∈x∪y当且仅当z∈x或者z∈y，而z∈x∩y当且仅当z∈x同时z∈y *)
Theorem MKT4 : ∀ x y z, z ∈ x \/ z ∈ y <-> z ∈ (x ∪ y).
Proof.
  split; intros; [destruct H; appA2G|appA2H H]; auto.
Qed.

Theorem MKT4' : ∀ x y z, z ∈ x /\ z ∈ y <-> z ∈ (x ∩ y).
Proof.
  split; intros; [destruct H; appA2G|appA2H H]; auto.
Qed.

Ltac deHun :=
  match goal with
   | H:  ?c ∈ ?a∪?b
     |- _ => apply MKT4 in H as [] ; deHun
   | _ => idtac
  end.

Ltac deGun :=
  match goal with
    | |-  ?c ∈ ?a∪?b => apply MKT4 ; deGun
    | _ => idtac
  end.

Ltac deHin :=
  match goal with
   | H:  ?c ∈ ?a∩?b
     |- _ => apply MKT4' in H as []; deHin
   | _ => idtac  
  end.

Ltac deGin :=
  match goal with
    | |- ?c ∈ ?a∩?b => apply MKT4'; split; deGin
    | _ => idtac
  end.

(* 定理5  x∪x=x同时x∩x=x *)
Theorem MKT5 : ∀ x, x ∪ x = x.
Proof.
  intros; eqext; deGun; deHun; auto.
Qed.

Theorem MKT5' : ∀ x, x ∩ x = x.
Proof.
  intros; eqext; deHin; deGin; auto.
Qed.

(* 定理6  x∪y=y∪x同时x∩y=y∩x *)
Theorem MKT6 : ∀ x y, x ∪ y = y ∪ x.
Proof.
  intros; eqext; deHun; deGun; auto.
Qed.

Theorem MKT6' : ∀ x y, x ∩ y = y ∩ x.
Proof.
  intros; eqext; deHin; deGin; auto.
Qed.

(* 定理7  (x∪y)∪z=x∪(y∪z)同时(x∩y)∩z=x∩(y∩z) *)
Theorem MKT7 : ∀ x y z, (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros; eqext; deHun; deGun; auto;
  [right|right|left|left]; deGun; auto.
Qed.

Theorem MKT7' : ∀ x y z, (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros; eqext; deGin; deHin; auto.
Qed.

(* 定理8  x∩(y∪z)=(x∩y)∪(x∩z)同时x∪(y∩z)=(x∪y)∩(x∪z) *)
Theorem MKT8 : ∀ x y z, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; eqext; deHin; deHun; deGun; deGin; [left|right|..];
  deHin; deHun; deGun; deGin; auto.
Qed.

Theorem MKT8' : ∀ x y z, x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  intros; eqext; deHin; deHun; deGin; repeat deGun; deHin; auto.
  right; deGin; auto.
Qed.

(* 定理11  ¬ (¬ x) = x *)
Theorem MKT11: ∀ x, ¬ (¬ x) = x.
Proof.
  intros; eqext.
  - appA2H H. Absurd. elim H0. appA2G.
  - appA2G. intro. appA2H H0; auto.
Qed.

(* 定理12  De Morgan   ¬(x∪y)=(¬x)∩(¬y)同时¬(x∩y)=(¬x)∪(¬y) *)
Theorem MKT12 : ∀ x y, ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros; eqext.
  - appA2H H; deGin; appA2G; intro; apply H0; deGun; auto.
  - deHin. appA2H H; appA2H H0. appA2G. intro. deHun; auto.
Qed.

Theorem MKT12' : ∀ x y, ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros. rewrite <-(MKT11 x),<-(MKT11 y),<-MKT12.
  repeat rewrite MKT11; auto.
Qed.

Fact setminP : ∀ z x y, z ∈ x -> ~ z ∈ y -> z ∈ (x ~ y).
Proof.
  intros. appA2G. split; auto. appA2G.
Qed.

Global Hint Resolve setminP : core.

Fact setminp : ∀ z x y, z ∈ (x ~ y) -> z ∈ x /\ ~ z ∈ y.
Proof.
  intros. appA2H H. destruct H0. appA2H H1; auto.
Qed.

(* 定理14  x∩(y ~ z)=(x∩y) ~ z *)
Theorem MKT14 : ∀ x y z, x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  intros; unfold Setminus; rewrite MKT7'; auto.
Qed.

(* 定理16  x∉Φ *)
Theorem MKT16 : ∀ {x}, x ∉ Φ.
Proof.
  intros; intro. apply AxiomII in H; destruct H; auto.
Qed.

Ltac emf :=
  match goal with
    H:  ?a ∈ Φ
    |- _ => destruct (MKT16 H)
  end.

Ltac eqE := eqext; try emf; auto.

Ltac feine z := destruct (@ MKT16 z).

(* 定理17  Φ∪x=x同时Φ∩x=Φ *)
Theorem MKT17 : ∀ x, Φ ∪ x = x.
Proof.
  intros; eqext; deHun; deGun; auto; emf.
Qed.

Theorem MKT17' : ∀ x, Φ ∩ x = Φ.
Proof.
  intros. eqE. deHin; auto.
Qed.

(* 定理19  x∈μ当且仅当x是一个集  *)
Theorem MKT19 : ∀ x, x ∈ μ <-> Ensemble x.
Proof.
  split; intros; eauto. appA2G.
Qed.

Theorem MKT19a : ∀ x, x ∈ μ -> Ensemble x.
Proof.
  intros. apply MKT19; auto.
Qed.

Theorem MKT19b : ∀ x, Ensemble x -> x ∈ μ.
Proof.
  intros. apply MKT19; auto.
Qed.

Global Hint Resolve MKT19a MKT19b : core.

(* 定理20  x∪μ=μ同时x∩μ=x *)
Theorem MKT20 : ∀ x, x ∪ μ = μ.
Proof.
  intros; eqext; deHun; deGun; eauto.
Qed.

Theorem MKT20' : ∀ x, x ∩ μ = x.
Proof.
  intros; eqext; deHin; deGin; eauto.
Qed.

(* 定理21  ¬Φ=μ同时¬μ=Φ *)
Theorem MKT21 : ¬ Φ = μ.
Proof.
  eqext; appA2G. apply MKT16.
Qed.

Theorem MKT21' : ¬ μ = Φ.
Proof.
  rewrite <-MKT11,MKT21; auto.
Qed.

Ltac deHex1 :=
  match goal with
    H: ∃ x, ?P 
    |- _ => destruct H as []
  end.

Ltac rdeHex := repeat deHex1; deand.

(* 定理24  ∩Φ=μ同时∪Φ=Φ *)
Theorem MKT24 : ∩Φ = μ.
Proof.
  eqext; appA2G; intros; emf.
Qed.

Theorem MKT24' : ∪Φ = Φ.
Proof.
  eqE. appA2H H. rdeHex. emf.
Qed.

(* 定理26  Φ⊂x同时x⊂μ *)
Theorem MKT26 : ∀ x, Φ ⊂ x.
Proof.
  unfold Included; intros; emf.
Qed.

Theorem MKT26' : ∀ x, x ⊂ μ.
Proof.
  unfold Included; intros; eauto.
Qed.

Theorem MKT26a : ∀ x, x ⊂ x.
Proof.
  unfold Included; intros; auto.
Qed.

Global Hint Resolve MKT26 MKT26' MKT26a : core.

Fact ssubs : ∀ {a b z}, z ⊂ (a ~ b) -> z ⊂ a.
Proof.
  unfold Included; intros. apply H in H0. appA2H H0; tauto.
Qed.

Global Hint Immediate ssubs : core.

Fact esube : ∀ {z}, z ⊂ Φ -> z = Φ.
Proof. intros. eqE. Qed.

(* 定理27  x=y当且仅当x⊂y同时y⊂x *)
Theorem MKT27 : ∀ x y, (x ⊂ y /\ y ⊂ x) <-> x = y.
Proof.
  split; intros; subst; [destruct H; eqext|split]; auto.
Qed.

(* 定理28  如果x⊂y且y⊂z，则x⊂z *)
Theorem MKT28 : ∀ {x y z}, x ⊂ y -> y ⊂ z -> x ⊂ z.
Proof.
  unfold Included; intros; auto.
Qed.

(* 定理29  x⊂y当且仅当x∪y=y *)
Theorem MKT29 : ∀ x y, x ∪ y = y <-> x ⊂ y.
Proof.
  split; unfold Included; intros;
  [rewrite <-H; deGun|eqext; deGun; deHun]; auto.
Qed.

(* 定理30  x⊂y当且仅当x∩y=x *)
Theorem MKT30 : ∀ x y, x ∩ y = x <-> x ⊂ y.
Proof.
  split; unfold Included; intros;
  [rewrite <-H in H0; deHin|eqext; deGin; deHin]; auto.
Qed.

(* 定理31  如果x⊂y,则∪x⊂∪y同时∩y⊂∩x *)
Theorem MKT31 : ∀ x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  split; red; intros; appA2H H0; rdeHex; appA2G.
Qed.

(* 定理32  如果x∈y,则x⊂∪y同时∩y⊂x *)
Theorem MKT32 : ∀ x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  split; red; intros; [appA2G|appA2H H0; auto].
Qed.

(*A.4 集的存在性 *)

(* 定理33  如果x是一个集同时z⊂x，则z是一个集 *)
Theorem MKT33 : ∀ x z, Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros. destruct (AxiomIII H) as [y []]; eauto.
Qed.

(* 定理34  0=∩μ同时∪μ =μ *)
Theorem MKT34 : Φ = ∩μ.
Proof.
  eqE. appA2H H. apply H0. appA2G. eapply MKT33; eauto.
Qed.

Theorem MKT34' : μ = ∪μ.
Proof.
  eqext; eauto. destruct (@ AxiomIII z) as [y []]; eauto. appA2G.
Qed.

(* 定理35  如果x≠0，则∩x是一个集 *)
Lemma NEexE : ∀ x, x ≠ Φ <-> ∃ z, z∈x.
Proof.
  split; intros.
  - Absurd. elim H; eqext; try emf. elim H0; eauto.
  - intro; subst. destruct H. emf.
Qed.

Ltac NEele H := apply NEexE in H as [].

Theorem MKT35 : ∀ x, x ≠ Φ -> Ensemble (∩x).
Proof.
  intros. NEele H. eapply MKT33; eauto. apply MKT32; auto.
Qed.

(* 定理37  u=pow(u) *)
Theorem MKT37 : μ = pow(μ).
Proof.
  eqext; appA2G; eauto.
Qed.

Ltac New H := pose proof H.

(* 定理38  如果x是一个集,则pow(x)是一个集*)
Theorem MKT38a : ∀ {x}, Ensemble x -> Ensemble pow(x).
Proof.
  intros. New (AxiomIII H). rdeHex. eapply MKT33; eauto.
  red; intros. appA2H H2; auto.
Qed.

Theorem MKT38b : ∀ {x}, Ensemble x -> (∀ y, y ⊂ x <-> y ∈ pow(x)).
Proof.
  split; intros; [appA2G; eapply MKT33; eauto|appA2H H0; auto].
Qed.

(* 定理39  μ不是一个集 *)

(* 一个不是集的类 *)
Lemma Lemma_N : ~ Ensemble \{ λ x, x ∉ x \}.
Proof.
  TF (\{ λ x, x ∉ x \} ∈ \{ λ x, x ∉ x \}).
  - New H. appA2H H; auto.
  - intro. apply H,AxiomII; auto.
Qed.

Theorem MKT39 : ~ Ensemble μ.
Proof.
  intro. apply Lemma_N. eapply MKT33; eauto.
Qed.


