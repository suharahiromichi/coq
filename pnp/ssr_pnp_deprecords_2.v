(** Programs and Proofs Ilya Sergey *)
(* http://ilyasergey.net/pnp/ *)

(**
「数学構造のコード化」DepRecords.v から抜粋し、Mathcomp ライブラリに命名規則をあわせた。
 *)

(**
7 Encoding Mathematical Structures
 *)
Module DepRecords.
  From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun.
  
  Set Implicit Arguments.
  Unset Strict Implicit.
  Unset Printing Implicit Defensive.

(**
7.1 Encoding partial commutative monoids

ひとつめのモジュール、可換モノイド。
 *)
  Module PCM.

(**
Mixinの定義
*)
    Record mixin_of (T : Type) :=
      Mixin {
          valid_op : T -> bool;
          join_op : T -> T -> T;
          unit_op : T;
          _ : commutative join_op;
          _ : associative join_op;
          _ : left_id unit_op join_op;
          _ : forall x y, valid_op (join_op x y) -> valid_op x; 
          _ : valid_op unit_op 
        }.
    Notation class_of := mixin_of (only parsing). (* not used *)
    
    Lemma r_unit T (m : mixin_of T) (t : T) : (join_op m t (unit_op m)) = t.
    Proof.
      case: m => _ join unit Hc _ Hlu _ _ /=.
        by rewrite Hc Hlu.
    Qed.
    
(**
7.1.3 Packaging the structure from mixins
 *)
(**
Packの定義
*)
    Section Packing.
      Structure type : Type :=
        Pack {
            sort : Type;
            _ : mixin_of sort
          }.
      Local Coercion sort : type >-> Sortclass.
(**
packのインスタンスは任意のsortの要素
（typeフィールドを経由して参照される、型Typeのこと）
にコアーションされる。コアーションのために

``type :  pack_type -> Type``

が挿入される。原文：

an instance of pack type should be coerced into an element of an arbitrary sort,
it should be done via referring to is type field.

``Coercion F : A >-> B.``

Aのインスタンスは任意のB要素（Fフィールドを経由して参照される）
にコアーションされる。次と比較せよ。
コアーションのために ``is_true`` が挿入される。

``Coercion is_true : bool >-> Sortclass. (* Prop *)``
 *)
      Check type.
      
      Variable cT : type.
      Definition class : mixin_of cT := (* Coercion cT *)
        let: Pack _ c := cT return mixin_of cT in c.
      Definition valid := valid_op class.
      Definition join := join_op class.
      Definition unit := unit_op class.
    End Packing.

(**
Exports の宣言
*)    
    Module Exports.
      Notation pcmMixin := mixin_of.        (* not used *)
      Notation pcmType := type.
      Notation PcmMixin := Mixin.
      Notation PcmType T m := (@Pack T m).
      Notation "x \+ y" := (join x y) (at level 43, left associativity). (* join_opではない。 *)
      Notation valid := valid.
      Notation Unit := unit.
      Coercion sort : type >-> Sortclass.

(**
7.2 Properties of partial commutative monoids

可換則や結合則を証明しておく。これらはexportされる。
*)      
      Section PCMLemmas.
        Variable U : pcmType.

        Lemma joinC (x y : U) : x \+ y = y \+ x. (* Coercion U *)
        Proof.
            by case: U x y => tp [v j z Cj *]; apply Cj.
        Qed.

        Lemma joinA (x y z : U) : x \+ (y \+ z) = x \+ y \+ z.
        Proof. 
            by case: U x y z => tp [v j z Cj Aj *]; apply: Aj. 
        Qed.
(**
Exercices 7.1
*)
        Lemma joinAC (x y z : U) : x \+ y \+ z = x \+ z \+ y.
        Proof.
          rewrite -[x \+ z \+ y]joinA.
          rewrite [z \+ y]joinC.
          rewrite [x \+ (y \+ z)]joinA.
          by [].
        Qed.
        
        Lemma joinCA (x y z : U) : x \+ (y \+ z) = y \+ (x \+ z).
        Proof.
          rewrite [y \+ (x \+ z)]joinA.
          rewrite [y \+ x]joinC.
          rewrite -[x \+ y \+ z]joinA.
          by [].
        Qed.
        
        Lemma validL (x y : U) : valid (x \+ y) -> valid x.
        Proof.
          case: U x y => tp [v j z Cj Aj H1 H2 H3 x y] => H.
          by apply: (H2 x y).
        Qed.

        Lemma validR (x y : U) : valid (x \+ y) -> valid y.
        Proof.
          case: U x y => tp [v j z Cj Aj H1 H2 H3 x y].
          rewrite [x \+ y]Cj.
          by apply: (H2 y x).
        Qed.
        
        Lemma unitL (x : U) : (@Unit U) \+ x = x.
        Proof.
          case: U x => tp [v j z Cj Aj H1 H2 H3 x].
          by apply H1.
        Qed.
        
        Lemma unitR (x : U) : x \+ (@Unit U) = x.
        Proof.
          case: U x => tp [v j z Cj Aj H1 H2 H3 x].
          rewrite [x \+ _]Cj.
          by apply H1.
        Qed.
        
        Lemma valid_unit : valid (@Unit U).
        Proof.
          case: U => tp [v j z Cj Aj H1 H2 H3].
          by apply H3.
        Qed.
(**
End of Exercices 7.1
 *)
      End PCMLemmas.
    End Exports.
  End PCM.
  Export PCM.Exports.                      (* Exportsをexportする。 *)
(**
ひとつめのモジュール、可換モノイドの終了。
 *)

(**
7.3 Implementing inheritance hierarchies

ふたつめのモジュール、簡約可換モノイド。
(mathcompの命名法では、cancelPcmType)
 *)
  Module CancelPCM.
(**
Mixin -- PCMに簡約法則を追加する。
 *)
    Record mixin_of (U : pcmType) :=
      Mixin {
          _ : forall a b c : U, valid (a \+ b) -> a \+ b = a \+ c -> b = c
        }.
    Notation class_of := mixin_of (only parsing). (* not used *)
    
(**
Packing -- Struture pack_type ... の定義は前のモジュールと同じ。

Section Packing. と End Packing. の有無は関係なく、
Variableなどの宣言の必要に応じて、Section にすればよい。
 *)
    Structure type : Type :=
      Pack {
          sort : pcmType;
          _ : mixin_of sort
        }.
    
(**
Exports の宣言
*)    
    Module Exports.
      Notation cancelPcmMixin := mixin_of.  (* not used *)
      Notation cancelPcmType := type.
      Notation CancelPcmMixin := Mixin.
      Notation CancelPcmType T m:= (@Pack T m).
      Coercion sort : type >-> pcmType.
(**
可換則を証明しておく。
 *)
      Lemma cancel (U : cancelPcmType) (x y z : U) : (* Coecion U *)
        valid (x \+ y) -> x \+ y = x \+ z -> y = z.
      Proof.
          by case: U x y z => Up [Hc] x y z; apply: Hc.
      Qed.
    End Exports.
  End CancelPCM. 
  Export CancelPCM.Exports.                 (* Exportsをexportする。 *)
(**
ふたつめのモジュール、簡約可換モノイドの終了。
 *)
  
  Lemma cancelC (U : cancelPcmType) (x y z : U) :
    valid (y \+ x \+ z) -> y \+ x = x \+ z -> y = z.
  Proof.
      by move/validL; rewrite ![y \+ _]joinC; apply: cancel.
  Qed.

(**
7.4 Instantiation and canonical structures

簡約モノイドを整数についてインスタンスを作る。
(mathcompの命名法では、nat_pcmType)
 *)
  Definition nat_pcmMixin := 
    PcmMixin
      addnC                                 (* commutative *)
      addnA                                 (* associative *)
      add0n                                 (* left_id *)
      (fun x y => @id true)                 (* valid_op join_op *)
      (erefl _).                            (* valid_op unit_op *)
  
  Canonical nat_pcmType := PcmType nat nat_pcmMixin.
  Print Canonical Projections.
(**
nat <- PCMDef.type ( natPCM )
が追加される。typeはCoercionであることに注意！
 *)

(**
natPCM が Canonical でないと、add_perm の定義がエラーになる。
natPCM を Canonical にすると、add_perm の nat を natPCM として扱える。
 *)
  Lemma add_perm (a b c : nat) : a \+ (b \+ c) = a \+ (c \+ b).
  Proof.
      by rewrite [c \+ b]joinC.
  Qed.
  
(** 可換簡約モノイドを整数についてインスタンスを作る。 *)
(**
簡約規則を証明しておく。
 *)
  Lemma nat_cancelP : forall a b c : nat, true -> a + b = a + c -> b = c.
  Proof.
    move=> a b c; elim: a => // n /(_ is_true_true) Hn _ H.
      by apply: Hn; rewrite !addSn in H; move/eq_add_S: H.
  Qed.
  
  (**
natPCM が Canonicalでないと、cancelNat が使用できない。
natPCM を Canonical にすると、cancelNat の nat を natPCM として扱える。
 *)
  Definition nat_cancelPcmMixin :=
    CancelPcmMixin
      nat_cancelP.                          (* 簡約規則 *)
  
  Canonical nat_cancelPcmType := CancelPcmType nat_pcmType nat_cancelPcmMixin.
  Print Canonical Projections.
(**
natPCM <- CancelPCM.pcmT ( cancelNatPCM )
が追加される。pcmTはCoercionであることに注意！
 *)
  
  Section PCMExamples.
    Variables a b c : nat.

    Check PCM.join_op : forall T : Type, PCM.mixin_of T -> T -> T -> T.
    Check PCM.join : forall cT : pcmType, cT -> cT -> cT.
    About "_ \+ _".                         (* PCM.join  *)
    
    Goal a \+ (b \+ c) =  c \+ (b \+ a).
      by rewrite joinA [c \+ _]joinC [b \+ _]joinC.
    Qed.
    
    Goal c \+ a = a \+ b -> c = b.
      by rewrite [c \+ _]joinC; apply: cancel.
    Qed.
    
    Lemma addn_join (x y : nat) : x + y = x \+ y. 
    Proof.
        by [].
    Qed.
  End PCMExamples.

(** 
Exercise 7.2 Partially-ordered sets
(see. ssr_pnp_poset.v)
*)
  
(**
Exercise 7.3 Canonical instances of partially ordered sets
*)

(**
7.4.2 Types with decidable equalities
 *)
  Module Equality.
    Definition axiom T (e : rel T) := forall x y, reflect (x = y) (e x y).
    
(**
Mixinの定義
*)
    Structure mixin_of T :=
      Mixin {
          op : rel T;
          _ : axiom op
        }.
    
(**
Packの定義
*)
    Structure type :=
      Pack {
          sort;
          _ : mixin_of sort
        }.
    
(**
Exports の宣言
*)    
    Module Exports.
      Notation eqMixin := mixin_of.
      Notation eqType := type.
      Notation EqMixin := Mixin.
      Notation EqType T m := (@Pack T m).     (* "@"が必要。 *)

      Definition eq_op {T : eqType} := op.
      Notation "x == y" := (eq_op x y) (at level 70, no associativity).
    End Exports.

  End Equality.
  Export Equality.Exports.       (* 他に習って、Exportsをexportする。 *)

End DepRecords.

(* END *)
