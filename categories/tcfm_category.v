(* TCfM から圏論の定義の部分を抜き出す。 *)
(* "Type Classes for Mathematics in Type Theory" *)

(* Global Generalizable All Variables. *)

(* Set Implicit Arguments. *)

Require Import Arith.
Require Import Omega.
Require Import Relations.                   (* relation など *)
Require Import Morphisms.                   (* Proper *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Section Category_Class.
  Generalizable Variables O x y.
  
  Class Arrows (O : Type) : Type := arrow : O -> O -> Type.
  Class Equiv A := equiv : relation A.
  
  Notation "A == B" := (equiv A B) (at level 55, right associativity).
  Notation "A --> B" := (arrow A B) (at level 55, right associativity).
  
  Class CatId O `{Arrows O} := cat_id : `(x --> x).
  Class CatComp O `{Arrows O} :=
    comp : forall {x y z}, (y --> z) -> (x --> y) -> (x --> z).
  
  Notation "A \o B" := (comp A B) (at level 40, left associativity).
  
  Class Setoid A {Ae : Equiv A} : Prop :=
    setoid_eq :> Equivalence (@equiv A Ae).
  (* これは、Operational Class である。
     Prop. Class にした場合は、unfold Setoid を split に変える。 *)
  
  Section setoid_morphisms.
  Context {A B} {Ae : Equiv A} {Be : Equiv B} (f : A -> B).    
    Class Setoid_Morphism :=
      {
        setoidmor_a : Setoid A;
        setoidmor_b : Setoid B;
        sm_proper :> Proper (equiv ==> equiv) f
      }. 
  End setoid_morphisms.
  
  Class Category (O : Type)
        `{!Arrows O}
        `{forall x y : O, Equiv (x --> y)}
        `{!CatId O}
        `{!CatComp O} : Prop :=
    {
      (* Setid である。 *)
      arrow_equiv :> forall x y, Setoid (x --> y);
      (* comp で繋いだ項をequivでの書換の対象にできる。 *)
      comp_proper :> forall x y z, Proper (equiv ==> equiv ==> equiv) (@comp _ _ _ x y z);
      (* comp の結合性が成立する。 *)
      comp_assoc w x y z (a : w --> x) (b : x --> y) (c : y --> z) :
        c \o (b \o a) = (c \o b) \o a;
      (* comp の単位元が存在する。 *)
      id_l `(a : x --> y) : cat_id _ \o a = a;
      id_r `(a : x --> y) : a \o cat_id _ = a;
    }.
End Category_Class.

Notation "A == B" := (equiv A B) (at level 55, right associativity).
Notation "A --> B" := (arrow A B) (at level 55, right associativity).
Notation "A \o B" := (comp A B) (at level 40, left associativity).

(* *********** *)
(* シングルトン *)
(* *********** *)
(* 
対象の集合 : unit
対象（唯一） : tt
射の集合（唯一） : tt --> tt (= nat と定める)
射の例     : 0,1,2.....
射の合成   : natの加算
恒等射     : 0
 *)

Definition O0 : Type := unit.
Instance A0 : Arrows O0 := fun (x y : O0) => nat.
Instance E0 (x y : O0) : Equiv (A0 x y) := fun (m n : nat) => m = n. (* 射の等しさ *)
Instance I0 : CatId O0 := fun (_ : O0) => 0.
Instance C0 : CatComp O0 := fun (_ _ _ : O0) (m n : nat) => m + n.

Check Category O0 : Prop.
Check @Category O0 A0 E0 I0 C0 : Prop.
Program Instance SPLUS : @Category O0 A0 E0 I0 C0.
Obligation 1.                               (* Setoid (x --> y) *)
Proof.
  unfold Setoid.                            (* Equivalence equiv *)
  unfold equiv.                             (* Equivalence (E0 x y) *)
  unfold E0.                                (* Equivalence (fun m n : nat => m = n) *)
  split.
  + now unfold Reflexive.
  + now unfold Symmetric.
  + unfold Transitive.
    intros x' y' z' H1 H2.
    now rewrite H1, H2.
Qed.
Obligation 2.                               (* c \o (b \o a) = c \o b \o a *)
Proof.
  unfold comp, C0.
  (* c + (b + a) = c + b + a *)
  now apply plus_assoc.
Qed.

(* 例 *)
Check @arrow O0 A0 tt tt.                   (* 射の型 *)
Check tt --> tt.                            (* 上記の構文糖 *)
Check 1 : tt --> tt.                        (* 1 は射の例 *)
Check 0 : tt --> tt.                        (* 0 は射の例 *)

(* 射 2 と 3 の合成は 5 になる。 *)
Check comp 3 2 : tt --> tt.
Compute comp 3 2.                           (* 5 *)
Check @comp O0 A0 C0 tt tt tt 3 2 : tt --> tt.
Compute @comp O0 A0 C0 tt tt tt 3 2.        (* 5 *)

Check cat_id tt : tt --> tt.
Compute cat_id tt.                          (* 0 *)
Check @cat_id O0 A0 I0 tt : tt --> tt.
Compute @cat_id O0 A0 I0 tt.                (* 0 *)


(* ******** *)
(* 集合の圏 *)
(* ******** *)
(* 
対象の集合 : Set
対象の例   : nat など
射の集合の例 : nat -> nat  など
射の例     : plus 0 (= id_nat), plus 1, plus 2,.... (関数)
射の合成   : 関数の合成
恒等射     : id_nat など

注意：対象は自然数の集合natである。0,1,2,..は対象ではない。
 *)

Definition O1 : Type := Set.
Instance A1 : Arrows O1 := fun (x y : O1) => x -> y.
Instance E1 (x y : O1) : Equiv (A1 x y) := (* x -> y *)
  fun (f g : A1 x y) => forall (a : x), f a = g a.
(*
Instance E1 (x y : O1) : Equiv (A1 x y) := (* x -> y *)
  fun (f g : A1 x y) => f = g.
*)
Instance I1 : CatId O1 := fun (a : O1) (x : a) => x.
Instance C1 : CatComp O1 :=
  fun (x y z : O1) (f : A1 y z) (g : A1 x y) (a : x) => f (g a).

Check Category O1 : Prop.
Check @Category O1 A1 E1 I1 C1 : Prop.
Program Instance SETS : @Category O1 A1 E1 I1 C1.
Obligation 1.
Proof.                                      (* Setoid (x --> y) *)
  unfold Setoid, equiv, E1.
  split.
  + now unfold Reflexive.
  + now unfold Symmetric.
  + unfold Transitive.
    intros x' y' z' H1 H2 a.
    rewrite H1.
    rewrite <- H2.
    easy.
Qed.
Obligation 2.            (* Proper (equiv ==> equiv ==> equiv) comp *)
Proof.
  unfold equiv, E1, comp, C1.
  intros yz yz' H1 xy xy' H2 a.
  rewrite <- H2.
  rewrite <- H1.
  (* yz (xy a) = yz (xy a) *)
  easy.
Qed.

(* 例 *)
Check @arrow O1 A1 nat nat.                 (* 射の型のひとつ *)
Check nat --> nat.                          (* 上記の構文糖 *)
Check plus 1 : nat --> nat.                 (* plus 1 は射の例 *)
Check plus 0 : nat --> nat.                 (* plus 0 は射の例 *)

(* 射 plus 2 と plus 3 の合成は plus 5 になる。 *)
Check comp (plus 3) (plus 2) : nat --> nat.
Compute comp (plus 3) (plus 2).             (* plus 5 *)
Check @comp O1 A1 C1 nat nat nat (plus 3) (plus 2) : nat --> nat.
Goal plus 5 = @comp O1 A1 C1 nat nat nat (plus 3) (plus 2).
Proof.
  unfold comp, C1.
  easy.
Qed.
Compute @comp O1 A1 C1 nat nat nat (plus 3) (plus 2). (* plus 5 *)

Check cat_id nat : nat --> nat.
Compute cat_id nat.                        (* id *)
Check @cat_id O1 A1 I1 nat : nat --> nat.  (* cat_id は射のひとつ *)
Goal id = @cat_id O1 A1 I1 nat.            (* cat_id は id に等しい *)
Proof.
  unfold cat_id, I1.
  easy.
Qed.
Compute @cat_id O1 A1 I1 nat.               (* id *)


(* ************* *)
(* 半順序集合の圏 *)
(* ************* *)
(* 
対象の集合 : nat
対象の例   : 0,1,2,....
射の集合の例 : 0 --> 0, 0 --> 1,...
射の例     : 0≦0, 0≦1,.. (対象が決まると唯一決まる)
射の合成   : 不等号の遷移性
恒等射     : 0≦0, 1≦1,..
 *)

Definition O2 : Type := nat.
Instance A2 : Arrows O2 := fun (x y : O2) => x <= y.
Instance E2 (x y : O2) : Equiv (A2 x y) := (* x <= y *)
  fun (H1 H2 : A2 x y) => H1 = H2.
Instance I2 : CatId O2 := le_n.
Instance C2 : CatComp O2 :=
  fun (x y z : O2) H1 H2 => le_trans x y z H2 H1.

Check @Category O2 A2 E2 I2 C2 : Prop.
Program Instance LE : @Category O2 A2 E2 I2 C2.
Obligation 1.                               (* Setoid (x --> y) *)
  unfold Setoid, equiv, E2.
  split.
  + now unfold Reflexive.
  + now unfold Symmetric.
  + unfold Transitive.
    intros x' y' z' H1 H2.
    now rewrite H1, H2.
Qed.
Obligation 2.                               (* c \o (b \o a) = c \o b \o a *)
Proof.
  unfold comp, C2.
  unfold arrow, A2 in *.
  (* Nat.le_trans w y z (Nat.le_trans w x y a b) c =
     Nat.le_trans w x z a (Nat.le_trans x y z b c) *)
  
  (* 普段ゴールには、定理（型）が出現するはずなのに、
     証明（値）であるle_transが出てきてしまった！ *)
  
  (* (w <= x -> x <= y) -> y <= z -> w <= z *)
  Check Nat.le_trans w y z (Nat.le_trans w x y a b) c : w <= z.
  (* w <= x -> (x <= y -> y <= z) -> w <= z *)
  Check Nat.le_trans w x z a (Nat.le_trans x y z b c) : w <= z.
  
  (* 公理：型が同じ値は同じ。
     …こんなことはありえない。irrelevence は 見当違い、無関係 の意味。
     しかし、証明する定理（型）が同じなら、証明（値）は同じ。
     …といえば納得できる。つまり、定理に対する証明の一意性を公理として導入する。 *)
  Check proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.
  now apply proof_irrelevance.
Qed.
Obligation 3.
  unfold comp, C2.                          (* cat_id y \o a = a *)
  unfold arrow, A2 in *.
  (* Nat.le_trans x y y a (cat_id y) = a *)
  (* x <= y -> y <= y -> x <= y *)
  Check Nat.le_trans x y y a (cat_id y).
  now apply proof_irrelevance.
Qed.
Obligation 4.
  unfold comp, C2.                          (* a \o cat_id x = a *)
  unfold arrow, A2 in *.
  (* Nat.le_trans x x y (cat_id x) a = a *)
  (* x <= x -> x <= y -> x <= y *)
  now apply proof_irrelevance.
Qed.

(* 例 *)
Check @arrow O2 A2 3 3.                     (* 射の型のひとつ *)
Check 3 --> 3.                              (* 上記の構文糖 *)
Check 3 --> 4.                              (* 射の型のひとつ *)
Check 4 --> 5.                              (* 射の型のひとつ *)
Check 3 --> 5.                              (* 射の型のひとつ *)

Definition le33 : 3 <= 3. Proof. easy. Defined.
Definition le34 : 3 <= 4. Proof. omega. Defined.
Definition le45 : 4 <= 5. Proof. omega. Defined.
Definition le35 : 3 <= 5. Proof. omega. Defined.

Check le33 : 3 --> 3.                       (* この型の射は唯一 *)
Check le34 : 3 --> 4.                       (* この型の射は唯一 *)
Check le45 : 4 --> 5.                       (* この型の射は唯一 *)
Check le35 : 3 --> 5.                       (* この型の射は唯一 *)

(* 3≦4 と 4≦5 を 合成すると 3≦5 になる。 *)
Check comp le45 le34 : 3 --> 5.
Compute comp le45 le34.
Check @comp O2 A2 C2 3 4 5 le45 le34 : 3 --> 5.
Compute @comp O2 A2 C2 3 4 5 le45 le34.
Goal le35 = @comp O2 A2 C2 3 4 5 le45 le34.
Proof.
  unfold comp, C2.
  apply proof_irrelevance.
Qed.

Check cat_id 3  : 3 --> 3.           (* cat_id は射のひとつ *)
Compute cat_id 3.                    (* le_n 3 *)
Check @cat_id O2 A2 I2 3  : 3 --> 3. (* cat_id は射のひとつ *)
Compute @cat_id O2 A2 I2 3.                 (* le_n 3 *)
Goal le_n 3 = @cat_id O2 A2 I2 3.    (* cat_id 3 は 3≦3 に等しい。 *)
Proof.
  unfold cat_id, I2.
  easy.
Qed.


(* *********** *)
(* しりとりの圏 *)
(* *********** *)
(* 
対象の集合 : ひらがな
対象の例   : こ,ぶ,た,ぬ,き,い,や,...
射の集合の例 : た --> き
射の例     : たぬき, たいやき
射の合成   : しりとりをした文字列の連結
恒等射     : こ,た,... (1文字語)
 *)

Inductive O3 : Type := こ | ぶ | た | ぬ | き | つ | ね | い | や.
Inductive A3 : Arrows O3 :=
  | single : forall A, A3 A A
  | cons : forall {A' B : O3} (A : O3) (tl : A3 A' B), A3 A B.

Check cons こ (cons ぶ (single た)) : A3 こ た.
Goal cons こ (cons ぶ (single た)) = cons こ (cons ぶ (single た)).
Proof. reflexivity. Qed.                    (* 普通に = が成り立つ。 *)

Instance E3 (x y : O3) : Equiv (A3 x y) :=
  fun (s t : A3 x y) => s = t.
Definition I3 : CatId O3 := single.
Definition C3 (x y z : O3) (t : A3 y z) (s : A3 x y) : A3 x z.
Proof.
  induction s.
  + easy.
  + now apply (cons A (IHs t)).
Defined.
Check C3 : CatComp O3.

Check @Category O3 A3 E3 I3 C3 : Prop.
Program Instance SIRI : @Category O3 A3 E3 I3 C3.
Obligation 1.                               (* Setoid (x --> y) *)
  unfold Setoid, equiv, E3.
  split.
  + now unfold Reflexive.
  + now unfold Symmetric.
  + unfold Transitive.
    intros x' y' z' H1 H2.
    now rewrite H1, H2.
Qed.
Obligation 2.                               (* c \o (b \o a) = c \o b \o a *)
Proof.
  unfold comp, C3.
  induction a; simpl.
  - easy.
  - now rewrite IHa.
Qed.
Obligation 3.                               (* cat_id y \o a = a *)
Proof.
  unfold comp, C3, cat_id, I3.
  induction a; simpl.
  - easy.
  - now rewrite IHa.
Qed.

(* 例 *)
Check @arrow O3 A3 ね こ.                   (* 射の型のひとつ *)
Check ね --> こ.                            (* 上記の構文糖衣 *)
Check こ --> こ.                            (* 射の型のひとつ *)
Check た --> き.                            (* 射の型のひとつ *)
Check き --> ね.                            (* 射の型のひとつ *)
Check た --> ね.                            (* 射の型のひとつ *)

Definition neko := cons ね (single こ).
Definition ko := single こ.
Definition koneko := cons こ (cons ね (single こ)).
Definition tanuki := cons た (cons ぬ (single き)).
Definition taiyaki := cons た (cons い (cons や (single き))).
Definition kitune := cons き (cons つ (single ね)).
Definition tanukitune := cons た (cons ぬ (cons き (cons つ (single ね)))).

Check neko    : ね --> こ.                  (* この型の射の例 *)
Check ko      : こ --> こ.                  (* この型の射の例 *)
Check koneko  : こ --> こ.                  (* この型の射の例、別の例 *)
Check tanuki  : た --> き.                  (* この型の射の例 *)
Check taiyaki : た --> き.                  (* この型の射の例、別の例 *)
Check kitune  : き --> ね.                  (* この型の射の例 *)
Check tanukitune : た --> ね.               (* この型の射の例 *)

(* たぬき と きつね を 合成すると たぬきつね になる。 *)

Check comp kitune tanuki : た --> ね.
(* Compute comp kitune tanuki. *)
Check @comp O3 A3 C3 た き ね kitune tanuki : た --> ね.
Goal tanukitune = @comp O3 A3 C3 た き ね kitune tanuki.
Compute @comp O3 A3 C3 た き ね kitune tanuki.
Proof.
  unfold comp, C3.
  easy.
Qed.

Check cat_id こ : こ --> こ.
(* Compute cat_id こ. *)
Check @cat_id O3 A3 I3 こ : こ --> こ.      (* cat_id は射のひとつ *)
Goal ko = @cat_id O3 A3 I3 こ. (* cat_id こ は single こ に等しい。 *)
Compute @cat_id O3 A3 I3 こ.                 (* single こ *)
Proof.
  unfold cat_id, I3.
  easy.
Qed.

(* こねこ は cat_id ではないことに注意してください。 *)
Compute @comp O3 A3 C3 ね こ こ ko neko.     (* ねこ と こ の連結は ねこ *)
Compute @comp O3 A3 C3 ね こ こ koneko neko. (* ねこ と こねこ の連結は ねこねこ *)


(* 始対象 *)
Section initiality.
  Generalizable Variables X.
  Context `{Category X}.
  
  Class InitialArrow (x : X) : Type := initial_arrow: forall y, x --> y.

  Class Initial (x : X) `{InitialArrow x}: Prop :=
    initial_arrow_unique : forall y f', initial_arrow y = f'.
End initiality.

Program Definition IA0 (x : O0) : @InitialArrow O0 A0 x := fun (y : O0) => _.
Obligation 1.
Admitted.

Program Instance ISNGL : @Initial O0 A0 tt (IA0 tt).
Obligation 1.
Proof.
  unfold initial_arrow, IA0.
  Admitted.

(* 関手 *)

Section functor_class.
  Generalizable Variables C D x y z a.
  
  Context `{Category C} `{Category D} (M : C -> D).
  
  Class Fmap : Type := fmap : forall {v w : C}, (v --> w) -> (M v --> M w).
  
  Class Functor `(Fmap) : Prop :=
    {
      functor_from : Category C;
      functor_to : Category D;
      functor_morphism :> forall a b : C, Setoid_Morphism (@fmap _ a b);
      preserves_id : `(fmap (cat_id _ : a --> a) = cat_id _);
      preserves_comp `(f : y --> z) `(g : x --> y) : fmap (f \o g) = fmap f \o fmap g
    }.
End functor_class.

Definition M01 (a : unit) : O1 := nat.

Check @Fmap.
Check @Fmap O0 A0 O1 A1 M01 : Type.
Check Fmap M01 : Type.

Definition f01 (x y : O0) (n : nat) := fun (x : nat) => x + n.
Definition F01 : @Fmap O0 A0 O1 A1 M01 := f01.

Check @Functor O0 A0 E0 I0 C0 O1 A1 E1 I1 C1 M01 F01.
Check Functor M01 F01.
Program Instance FUN01 : Functor M01 F01.
Obligation 1.
Proof.
  split.
  - split.                                  (* Setoid (a --> b) *)
    + unfold Reflexive.
      now unfold equiv, E0.
    + unfold Symmetric.
      now unfold equiv, E0.
    + unfold Transitive.
      unfold equiv, E0.
      intros.
      now subst.
  - split.                                  (* Setoid (M a --> M b) *)
    + unfold Reflexive.
      now unfold equiv, E1.
    + unfold Symmetric.
      now unfold equiv, E1.
    + unfold Transitive.
      unfold equiv, E1.
      intros.
      erewrite H.
      erewrite <- H0.
      easy.
  - intro x.                                (* Proper (equiv ==> equiv) (fmap M01) *)
    intros y H.
    unfold equiv, E0 in H.
    rewrite H.
    easy.
Qed.

Check Fmap M01.
Check F01.
Check @fmap O0 A0 O1 A1 M01 F01 tt tt : tt --> tt -> nat --> nat.
Check @fmap O0 A0 O1 A1 M01 F01 tt tt   1         :  nat --> nat.

Goal @fmap O0 A0 O1 A1 M01 F01 tt tt   1 = fun x => x + 1.
Proof.
  unfold fmap, M01, F01, f01.
  easy.
Qed.

Goal forall n : nat, @fmap O0 A0 O1 A1 M01 F01 tt tt   n = fun x => x + n.
Proof.
  unfold fmap, M01, F01, f01.
  easy.
Qed.

(* END *)
