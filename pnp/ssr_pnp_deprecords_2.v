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
          valid : T -> bool;
          join : T -> T -> T;
          unit : T;
          _ : commutative join;
          _ : associative join;
          _ : left_id unit join;
          _ : forall x y, valid (join x y) -> valid x; 
          _ : valid unit 
        }.
    Notation class_of := mixin_of (only parsing). (* not used *)
    
    Lemma r_unit T (m : mixin_of T) (t : T) : (join m t (unit m)) = t.
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
    Section ClassDef.
      Structure type : Type :=
        Pack {
            sort : Type;
            _ : mixin_of sort
          }.
      Local Coercion sort : type >-> Sortclass.
      Print Graph.                          (* [sort] : type >-> Sortclass *)
(**
packのインスタンスは任意のsortの要素
（typeフィールドを経由して参照される、型Typeのこと）
にコアーションされる。コアーションのために

``sort :  type -> Type``

が挿入される。原文：

an instance of pack type should be coerced into an element of an arbitrary sort,
it should be done via referring to is type field.

``Coercion F : A >-> B.``

Aのインスタンスは任意のB要素（Fフィールドを経由して参照される）
にコアーションされる。次と比較せよ。
コアーションのために ``is_true`` が挿入される。

``Coercion is_true : bool >-> Sortclass. (* Prop *)``
 *)
      Variable T : Type.
      Variable cT : type.
      
      Definition class : mixin_of cT := (* Coercion cT *)
        let: Pack _ c := cT return mixin_of cT in c.
      
      Definition pack c := @Pack T c.
      Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.
      
      Definition valid_op := valid class.
      Definition join_op := join class.
      Definition unit_op := unit class.
    End ClassDef.

(**
Exports の宣言
*)    
    Module Exports.
      Notation pcmMixin := mixin_of.        (* not used *)
      Notation pcmType := type.
      Notation PcmMixin := Mixin.
      Notation PcmType T m := (@Pack T m).
      Notation "x \+ y" := (join_op x y) (at level 43, left associativity).
      Notation Valid := valid_op.
      Notation Unit := unit_op.
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
        
        Lemma validL (x y : U) : Valid (x \+ y) -> Valid x.
        Proof.
          case: U x y => tp [v j z Cj Aj H1 H2 H3 x y] => H.
          by apply: (H2 x y).
        Qed.
        
        Lemma validR (x y : U) : Valid (x \+ y) -> Valid y.
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
        
        Lemma valid_unit : valid_op (@Unit U).
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
          _ : forall a b c : U, Valid (a \+ b) -> a \+ b = a \+ c -> b = c
        }.
    Notation class_of := mixin_of (only parsing). (* not used *)
    
(**
Packing -- Struture pack_type ... の定義は前のモジュールと同じ。

Section ClassDef. と End ClassDef. の有無は関係なく、
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
        Valid (x \+ y) -> x \+ y = x \+ z -> y = z.
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
    Valid (y \+ x \+ z) -> y \+ x = x \+ z -> y = z.
  Proof.
      by move/validL; rewrite ![y \+ _]joinC; apply: cancel.
  Qed.
  
(**
7.4 Instantiation and canonical structures

簡約モノイドを整数についてインスタンスを作る。
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
nat <- PCM.sort ( nat_pcmType )
が追加される。typeはCoercionであることに注意！
 *)

(**
nat_pcmType が Canonical でないと、nat_add_perm の定義がエラーになる。
nat_pcmType を Canonical にすると、nat_add_perm の nat を nat_pcmType として扱える。
 *)
  Lemma nat_add_perm (a b c : nat) : a \+ (b \+ c) = a \+ (c \+ b).
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
nat_pcmType が Canonical でないと、nat_cancelP が使用できない。
nat_pcmType を Canonical にすると、nat_cancelP の nat を nat_pcmType として扱える。
 *)
  Definition nat_cancelPcmMixin :=
    CancelPcmMixin
      nat_cancelP.                          (* 簡約規則 *)
  
  Canonical nat_cancelPcmType := CancelPcmType nat_pcmType nat_cancelPcmMixin.
  Print Canonical Projections.
(**
nat_pcmType <- CancelPCM.sort ( nat_cancelPcmType )
が追加される。sortはCoercionであることに注意！
 *)
  
  Section PCMExamples.
    Variables a b c : nat.

    Check PCM.join : forall T : Type, PCM.mixin_of T -> T -> T -> T.
    Check PCM.join_op : forall cT : pcmType, cT -> cT -> cT.
    About "_ \+ _".                         (* PCM.join_op  *)
    
    Goal a \+ (b \+ c) =  c \+ (b \+ a).
      by rewrite joinA [c \+ _]joinC [b \+ _]joinC.
    Qed.
    
    Goal c \+ a = a \+ b -> c = b.
      by rewrite [c \+ _]joinC; apply: cancel.
    Qed.
    
    Lemma nat_add_join (x y : nat) : x + y = x \+ y. 
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
    End Exports.

  End Equality.
  Export Equality.Exports.       (* 他に習って、Exportsをexportする。 *)

End DepRecords.

(* END *)
