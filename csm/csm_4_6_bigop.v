(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.6 bigop.v --- 総和、相乗のライブラリ

======

2018_12_10 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/bigop.v
*)

(**
# bigop とは

*)

(**
## モノイドによる定義

Check や Print だと、読み難い。
 *)

Check big_distrl                            (* 係数を括り出す *)
  : forall (R : Type) (zero : R) (times : Monoid.mul_law zero)
           (plus : Monoid.add_law zero times) (I : Type) (r : seq I) 
           (a : R) (P : pred I) (F : I -> R),
    times (\big[plus/zero]_(i <- r | P i) F i) a =
    \big[plus/zero]_(i <- r | P i) times (F i) a.

(**
ソースコードでは、ローカルに +, 0, -, 1 を定義して使っている：

Lemma big_distrl I r a (P : pred I) F :
  \big[+%M/0]_(i <- r | P i) F i * a = \big[+%M/0]_(i <- r | P i) (F i * a).


あるいは、数学記号（Σ、Π）を使った説明：

https://staff.aist.go.jp/reynald.affeldt/ssrcoq/bigop_doc.pdf
 *)

(**
## レンジはリスト

iota で範囲からリストを作る、または、finType の enum を取り出す。
 *)

Goal \big[addn/0]_(0 <= i < 5) i = 10.
Proof.
    by rewrite unlock.
Qed.

Goal \big[addn/0]_(i <- [:: 0; 1; 2; 3; 4]) i = 10.
Proof.
    by rewrite unlock.
Qed.

Compute index_enum (ordinal_finType 5).

Goal \big[addn/0]_(i : 'I_5) i = 10.
Proof.
  rewrite unlock.
  rewrite /reducebig.
Admitted.  

Goal \big[addn/0]_(i < 5) i = 10.           (* Ordinal の意味になる。 *)
Proof.
  rewrite unlock.
  rewrite /reducebig.
Admitted.

Goal \big[addn/0]_(i in 'I_5) i = 10.
Proof.
  rewrite unlock.
  rewrite /reducebig.
Admitted.  


(**
## bigA_distr_bigA
 *)

Check bigA_distr_bigA.

Goal \prod_(i < 2) (\sum_(j < 3) (10*i+j)) = 10. (* 右辺はいい加減 *)
Proof.
  rewrite bigA_distr_bigA /=.
  (* \sum_f \prod_(i < 2) (10 * i + f i) = 10 *)
  rewrite unlock /reducebig.
Admitted.

(* ここで、f は、 定義域 {0, 1}、値域 {0, 1, 2} である関数(finfun)のすべて。
   全部で 3^2 = 9 個ある。 *)
Check {ffun 'I_2 -> 'I_3}.    (* ('I_3 ^ 'I_2) と書いてもいいかも。 *)
Check finfun_finType (ordinal_finType 2) (ordinal_finType 3).

Definition p0 : 'I_3. Proof. by apply: (@Ordinal 3 0). Defined.
Definition p1 : 'I_3. Proof. by apply: (@Ordinal 3 1). Defined.
Definition p2 : 'I_3. Proof. by apply: (@Ordinal 3 2). Defined.

Check [ffun i : 'I_2 => p0] : {ffun 'I_2 -> 'I_3}.
Check [ffun i : 'I_2 => p1] : finfun_finType (ordinal_finType 2) (ordinal_finType 3).

(* END *)
