(** Programs and Proofs Ilya Sergey *)
(* http://ilyasergey.net/pnp/ *)

(**
「数学構造のコード化」DepRecords.v から抜粋した。
 *)

(**
7 Encoding Mathematical Structures
 *)
Module DepRecords.
  Require Import ssreflect ssrbool ssrnat ssrfun.
  
  Set Implicit Arguments.
  Unset Strict Implicit.
  Unset Printing Implicit Defensive.

(**
7.1 Encoding partial commutative monoids

ひとつめのモジュール、可換モノイド。
 *)
  Module PCMDef. 

(**
Mixinの定義
*)
    Record mixin_of (T : Type) :=
      Mixin
        {
          valid_op : T -> bool;
          join_op : T -> T -> T;
          unit_op : T;
          _ : commutative join_op;
          _ : associative join_op;
          Hu : left_id unit_op join_op;
          H : forall x y, valid_op (join_op x y) -> valid_op x; 
          Hv : valid_op unit_op 
        }.

    Lemma r_unit T (pcm: mixin_of T) (t: T) :
      (join_op pcm t (unit_op pcm)) = t.
    Proof.
      case: pcm => _ join unit Hc _ Hlu _ _ /=.
                  by rewrite Hc Hlu.
    Qed.
    
(**
7.1.3 Packaging the structure from mixins
 *)

(**
Packの定義
*)
    Section Packing.
      Structure pack_type : Type :=
        Pack {
            type : Type;
            _ : mixin_of type
          }.
      Local Coercion type : pack_type >-> Sortclass.
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
      Variable cT: pack_type.
      Definition pcm_struct : mixin_of cT := (* Coercion cT *)
        let: Pack _ c := cT return mixin_of cT in c.
      Definition valid := valid_op pcm_struct.
      Definition join := join_op pcm_struct.
      Definition unit := unit_op pcm_struct.
    End Packing.

(**
Exports の宣言
*)    
    Module Exports.
      Notation pcm := pack_type.
      Notation PCMMixin := Mixin.
      Notation PCM T m := (@Pack T m).
      Notation "x \+ y" := (join x y) (at level 43, left associativity).
      Notation valid := valid.
      Notation Unit := unit.
      Coercion type : pack_type >-> Sortclass.

(**
可換則や結合則を証明しておく。これらはexportされる。
*)      
      Section PCMLemmas.
        Variable U : pcm.

        Lemma joinC (x y : U) : x \+ y = y \+ x. (* Coercion U *)
        Proof.
            by case: U x y => tp [v j z Cj *]; apply Cj.
        Qed.

        Lemma joinA (x y z : U) : x \+ (y \+ z) = x \+ y \+ z.
        Proof. 
            by case: U x y z => tp [v j z Cj Aj *]; apply: Aj. 
        Qed.
(**
Exercices 1
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
          Check (@Pack U).
          Check (@Mixin U (@valid U) (@join U) (@unit U)).
          apply: H.
        Qed.

(**
Mixin の lowの部分を使うにはどうすればよいのだろうか。
ここでは、Mixinの定義を変えて、名前を付与している。
*)        
        Lemma validR (x y : U) : valid (x \+ y) -> valid y.
        Proof.
          rewrite joinC.
          apply: H.
        Qed.
        
        Lemma unitL (x : U) : (@Unit U) \+ x = x.
        Proof.
          apply: Hu.
        Qed.

        Lemma unitR (x : U) : x \+ (@Unit U) = x.
        Proof.
          rewrite joinC.
          apply: Hu.
        Qed.
        
        Lemma valid_unit : valid (@Unit U).
        Proof.
          apply: Hv.
        Qed.
(**
End of Exercices 1
 *)
      End PCMLemmas.
    End Exports.
  End PCMDef.
  Export PCMDef.Exports.                    (* Exportsをexportする。 *)
(**
ひとつめのモジュール、可換モノイドの終了。
 *)

(**
7.3 Implementing inheritance hierarchies

ふたつめのモジュール、簡約可能モノイド。
 *)
  Module CancelPCM.
(**
Mixin -- PCMに簡約法則を追加する。
 *)
    Record mixin_of (U : pcm) :=
      Mixin
        {
          _ : forall a b c: U, valid (a \+ b) -> a \+ b = a \+ c -> b = c
        }.

(**
Packing -- Struture pack_type ... の定義は前のモジュールと同じ。

Section Packing. と End Packing. の有無は関係なく、
Variableなどの宣言の必要に応じて、Section にすればよい。
 *)
    Structure pack_type : Type :=
      Pack {
          pcmT : pcm;
          _ : mixin_of pcmT
        }.
    
(**
Exports の宣言
*)    
    Module Exports.
      Notation cancel_pcm := pack_type.
      Notation CancelPCMMixin := Mixin.
      Notation CancelPCM T m:= (@Pack T m).
      Coercion pcmT : pack_type >-> pcm.
(**
可換則を証明しておく。
 *)
      Lemma cancel (U: cancel_pcm) (x y z: U): (* Coecion U *)
        valid (x \+ y) -> x \+ y = x \+ z -> y = z.
      Proof.
          by case: U x y z => Up [Hc] x y z; apply: Hc.
      Qed.
    End Exports.
  End CancelPCM. 
  Export CancelPCM.Exports.                 (* Exportsをexportする。 *)
(**
ふたつめのモジュール、簡約可能モノイドの終了。
 *)
  
  Lemma cancelC (U: cancel_pcm) (x y z : U) :
    valid (y \+ x \+ z) -> y \+ x = x \+ z -> y = z.
  Proof.
      by move/validL; rewrite ![y \+ _]joinC; apply: cancel.
  Qed.

(**
7.4 Instantiation and canonical structures
 *)

  Definition natPCMMixin := 
    PCMMixin addnC addnA add0n (fun x y => @id true) (erefl _).
  
  Definition NatPCM := PCM nat natPCMMixin.
  Canonical natPCM := NatPCM.               (* 原文では、PCM nat natPCMMixin. *)
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
  
  Lemma cancelNat : forall a b c:
                             nat, true -> a + b = a + c -> b = c.
  Proof.
    move=> a b c; elim: a => // n /(_ is_true_true) Hn _ H.
      by apply: Hn; rewrite !addSn in H; move/eq_add_S: H.
  Qed.
  
(**
natPCM が Canonicalでないと、cancelNat が使用できない。
natPCM を Canonical にすると、cancelNat の nat を natPCM として扱える。
 *)
  Definition cancelNatPCMMixin := CancelPCMMixin cancelNat.
  Canonical cancelNatPCM := CancelPCM natPCM cancelNatPCMMixin.
  Print Canonical Projections.
(**
natPCM <- CancelPCM.pcmT ( cancelNatPCM )
が追加される。pcmTはCoercionであることに注意！
 *)
  
  Section PCMExamples.
    Variables a b c: nat.

    Goal a \+ (b \+ c) =  c \+ (b \+ a).
      by rewrite joinA [c \+ _]joinC [b \+ _]joinC.
    Qed.
    
    Goal c \+ a = a \+ b -> c = b.
      by rewrite [c \+ _]joinC; apply: cancel.
    Qed.
    
    Lemma addn_join (x y: nat): x + y = x \+ y. 
    Proof.
        by [].
    Qed.
  End PCMExamples.

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
      Pack
        {
          sort;
         _ : mixin_of sort
        }.
    
(**
Exports の宣言
*)    
    Module Exports.
      Notation EqMixin := Mixin.
      Notation EqType T m := (@Pack T m).     (* "@"が必要。 *)
    End Exports.
  End Equality.
  Export Equality.Exports.       (* 他に習って、Exportsをexportする。 *)
  
(**
Exercices 2
 *)

(** 
---------------------------------------------------------------------
Exercise [Partially-ordered sets]
---------------------------------------------------------------------

A partially ordered set order is a pair (T, <==), where T is a carrier
set and <== is a relation on T, such that

- forall x in T, x <== x (reflexivity);

- forall x, y in T, x <== y /\ y <== x \implies x = y (antisymmetry);

- forall x, y, z in T, x <== y /\ y <== z \implies x <== z (transitivity).

Implement a data structure for partially-ordered sets using mixins and
packed classes. Prove the following laws:

Lemma poset_refl (x : T) : x <== x.
Lemma poset_asym (x y : T) : x <== y -> y <== x -> x = y.
Lemma poset_trans (y x z : T) : x <== y -> y <== z -> x <== z.
*)

(**
---------------------------------------------------------------------
Exercise [Canonical instances of partially ordered sets]
---------------------------------------------------------------------

Provide canonical instances of partially ordered sets for the
following types:

- [nat] and [<=];

- [prod], whose components are posets;

- functions [A -> B], whose codomain (range) [B] is a partially
  ordered set.

In order to provide a canonical instance for functions, you will need
to assume and make use of the following axiom of functional
extensionality:

*)

Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x), 
               (forall x, f1 x = f2 x) -> f1 = f2.

(**
End of Exercices 2
*)
End DepRecords.

(* END *)
