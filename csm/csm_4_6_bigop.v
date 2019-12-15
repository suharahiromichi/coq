(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.6 bigop.v --- 総和、相乗のライブラリ

======

2018_12_10 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import bigop matrix.

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
*)

Check \big[addn/0]_(i < 5) i.               (* \sum_(i < 5) i *)
Check \big[maxn/0]_(i < 5) i.               (* \mux_(i < 5) i *)
Check \big[muln/1]_(i < 5) i.               (* \prod_(i < 5) i *)

(* finset *)
Check \big[@setU _/set0]_(i <- [:: set0]) i. (* \bigcup_(i <- [:: set0]) i *)
Check \big[@setI _/setT]_(i <- [:: set0]) i. (* \bigcap_(i <- [:: set0]) i *)

Check \big[andb/true]_(i : bool) i.
Check \big[orb/false]_(i : bool) i.
Check \big[addb/false]_(i : bool) i.
Check \big[gcdn/0]_(i < 5) i.
Check \big[lcmn/1]_(i < 5) i.
Check \big[cat/[::]]_(i <- [:: [:: 0]; [::1]; [:: 2]]) i.


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
## モノイドによる定義 (その2)

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
## 総和と相乗の分配規 bigA_distr_bigA
 *)

Definition F (i j : nat) := 10 * i + j.

Check bigA_distr_bigA.

Goal \prod_(i < 2) (\sum_(j < 3) F i j) = 10. (* 右辺はいい加減 *)
Proof.
  rewrite bigA_distr_bigA /=.
  (* \sum_f \prod_(i < 2) F i (f i) = 10 *)
  rewrite unlock /reducebig.
Admitted.

(**
F(i, j) が F(i, f(i)) になっている。

こで、f は、 定義域 {0, 1}、値域 {0, 1, 2} である関数(finfun)のすべて。
全部で 3^2 = 9 個ある。
 *)

(**
Π_i=1,2 Σ_j=1,3 Fij
= (F00 + F01 + F02)(F10 + F11 + F12)
= F00 F10 + F00 F11 + F00 F12
+ F01 F10 + F01 F11 + F01 F12
+ F02 F10 + F02 F11 + F02 F12
= Σ_f F0(f0)F1(f1)
= Σ_f Π_i=1,2 Fi(fi)
*)

Check {ffun 'I_2 -> 'I_3}.    (* ('I_3 ^ 'I_2) と書いてもいいかも。 *)
Check finfun_finType (ordinal_finType 2) (ordinal_finType 3).

Definition p0 : 'I_3. Proof. by apply: (@Ordinal 3 0). Defined.
Definition p1 : 'I_3. Proof. by apply: (@Ordinal 3 1). Defined.
Definition p2 : 'I_3. Proof. by apply: (@Ordinal 3 2). Defined.

Check [ffun i : 'I_2 => p0] : {ffun 'I_2 -> 'I_3} : predArgType.
Check [ffun i : 'I_2 => p1]
  : finfun_finType (ordinal_finType 2) (ordinal_finType 3) : finType.
(* ordinal は predArgType *)
(* sort がコアーションで略されている。 *)

(**
これは行列式の積 |A B| = |A||B| の証明に使われる。matrix.v
*)

Check det_mulmx
  : forall (R : ssralg.GRing.ComRing.type) (n : nat) (A B : 'M_n),
    @determinant (ssralg.GRing.ComRing.ringType R) n (A *m B) =
    @ssralg.GRing.mul (ssralg.GRing.ComRing.ringType R) (\det A) (\det B).

(* END *)
