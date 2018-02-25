(** Programs and Proofs Ilya Sergey *)
(* http://ilyasergey.net/pnp/ *)

(**
「数学構造のコード化」DepRecords.v から抜粋し、Mathcomp ライブラリに命名規則をあわせた。
ModuleとSectionの階層を削除して、シンプルな構成にする。
pcmType と cancelPcmType で、メンバ名 sort が重複してしまった。
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

可換モノイド
 *)
  Record pcmMixin (T : Type) :=
    PcmMixin {
        valid : T -> bool;
        join : T -> T -> T;
        unit : T;
        _ : commutative join;
        _ : associative join;
        _ : left_id unit join;
        _ : forall x y, valid (join x y) -> valid x; 
        _ : valid unit 
      }.
  
  Lemma r_unit T (m : pcmMixin T) (t : T) : (join m t (unit m)) = t.
  Proof.
    case: m => _ join unit Hc _ Hlu _ _ /=.
      by rewrite Hc Hlu.
  Qed.
    
(**
7.1.3 Packaging the structure from mixins
 *)
  Structure pcmType : Type :=
    PcmType {
        sort : Type;
        m : pcmMixin sort
      }.
  Local Coercion sort : pcmType >-> Sortclass.
  Print Graph.                       (* [sort] : type >-> Sortclass *)
  
  Definition valid_op {T : pcmType} := @valid (sort T) (m T).
  Notation Valid := valid_op.
  
  Definition join_op {T : pcmType} := @join (sort T) (m T).
  Notation "x \+ y" := (join_op x y) (at level 43, left associativity).
  
  Definition unit_op {T : pcmType} := @unit (sort T) (m T).
  Notation Unit := unit_op.
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
(**
ひとつめのモジュール、可換モノイドの終了。
 *)

(**
7.3 Implementing inheritance hierarchies

簡約可換モノイド。
 *)
  (**
Mixin -- PCMに簡約法則を追加する。
 *)
  Record cancelPcmMixin (U : pcmType) :=
    CancelPcmMixin {
        _ : forall a b c : U, Valid (a \+ b) -> a \+ b = a \+ c -> b = c
      }.
  
  Structure cancelPcmType : Type :=
    CancelPcmType {
        sort2 : pcmType;
        m2 : cancelPcmMixin sort2
      }.
  Coercion sort2 : cancelPcmType >-> pcmType.
  Print Graph.                       (* [sort2] : cancelPcmType >-> pcmType *)
(**
可換則を証明しておく。
 *)
  Lemma cancel (U : cancelPcmType) (x y z : U) : (* Coecion U *)
    Valid (x \+ y) -> x \+ y = x \+ z -> y = z.
  Proof.
      by case: U x y z => Up [Hc] x y z; apply: Hc.
  Qed.
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
  
  Canonical nat_pcmType := @PcmType nat nat_pcmMixin.
  Print Canonical Projections.
(**
nat <- sort ( nat_pcmType )
nat_pcmMixin <- m ( nat_pcmType )
が追加される。
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
  
  Canonical nat_cancelPcmType := @CancelPcmType nat_pcmType nat_cancelPcmMixin.
  Print Canonical Projections.
(**
nat_pcmType <- sort2 ( nat_cancelPcmType )
nat_cancelPcmMixin <- m2 ( nat_cancelPcmType )
が追加される。
 *)

  
  Section PCMExamples.
    Variables a b c : nat.
    
    Check join : forall T : Type, pcmMixin T -> T -> T -> T.
    Check @join_op : forall cT : pcmType, cT -> cT -> cT.
    About "_ \+ _".                         (* join_op  *)
    
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

End DepRecords.

(* END *)
