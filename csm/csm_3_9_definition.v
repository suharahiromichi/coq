(**
ProofCafe 名古屋 補足資料

萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版

[http://www.morikita.co.jp/books/book/3287]

3.9 コマンド Definition, Lemma ... Qed ... 補足説明

@suharahiromichi

2019_08_17
*)

From mathcomp Require Import all_ssreflect.
Require Import Ascii String.
Open Scope string_scope.

(**
# 3.9.1 Definition
 *)

(**
# 3.9.2 Lemma ... Qed

Lemma/Defined による定義（QedでなくDefinedで終わる）についての補足説明

Ordinal型（0から4までの5個の自然数からなる型）の値の定義が解り易く、実用的だろう。

'I_5型の、0〜4 をそれぞれ定義してみた。
 *)

Definition p0 := @Ordinal 5 0 is_true_true.
Definition p1 : 'I_5. Proof. by apply: (@Ordinal 5 1). Defined.
Lemma      p2 : 'I_5. Proof. by apply: (@Ordinal 5 2). Defined.
Definition p3 : 'I_5. Proof. by apply: (@Ordinal 5 3). Qed.
Lemma      p4 : 'I_5. Proof. by apply: (@Ordinal 5 4). Qed.

(**
自然数のサブタイプなので、自然数と加算して自然数が得られるはずである。
 *)

Compute 0 + p0.                 (* = 0 : nat *)
Compute 0 + p1.                 (* = 1 : nat *)
Compute 0 + p2.                 (* = 2 : nat *)
Compute 0 + p3.                 (* = let '@Ordinal _ m _ := p3 in m : nat *)
Compute 0 + p4.                 (* = let '@Ordinal _ m _ := p4 in m : nat *)

(**
「:=」で定義する場合、または Defined で終わる定義の値については、
自然数の値が求められていることがわかる。

両方が、「:=」または「Defined」の場合だけ、
自然数の値が求められていることがわかる。
  *)

Compute p0 + p1.                            (* 1 *)
Compute p1 + p0.                            (* 1 *)
Compute p2 + p1.                            (* 3 *)
Compute p1 + p2.                            (* 3 *)

Compute p0 + p4.                (* = let '@Ordinal _ m _ := p4 in m *)
Compute p4 + 0.
(*
  = (fix Ffix (x x0 : nat) {struct x} : nat :=
  match x with
  | 0 => x0
  | x1.+1 => (Ffix x1 x0).+1
  end) (let '@Ordinal _ m _ := p4 in m) 0
*)

(**
ただし、Print した結果を見ても、判らない。   
 *)

Print p0.            (* = Ordinal (n:=5) (m:=0) is_true_true : 'I_5 *)
Print p1.            (* = Ordinal (n:=5) (m:=1) is_true_true : 'I_5 *)
Print p2.            (* = Ordinal (n:=5) (m:=2) is_true_true : 'I_5 *)
Print p3.            (* = Ordinal (n:=5) (m:=3) is_true_true : 'I_5 *)
Print p4.            (* = Ordinal (n:=5) (m:=4) is_true_true : 'I_5 *)

(**
なお、「:=」で定義する場合は、
Lemma や Theorem, Corollay, Fact, Proposition, Remark
は使えない。
*)

(**
証明のなかで simpl を実行してみるとよく判る。

CRM : Controlling the reduction strategies and the conversion algorithm

https://coq.inria.fr/refman/proof-engine/vernacular-commands.html#controlling-the-reduction-strategies-and-the-conversion-algorithm

- 「:=」やDefined で定義したqualidを transparent と呼ぶ。unfold（δ簡約）できる。

- Qed で定義したqualidを opaque と呼ぶ。unfold（δ簡約）できる。
 *)

(**
p0 は transparent である。
*)

Goal 0 + p0 = 0.
Proof.
    by rewrite /p0 /=.
Qed.

(**
transparent と opaque を切り替えるコマンドがある。
*)

Goal 0 + p0 = 0.
Proof.
  Opaque p0.
  Fail rewrite /p0.                         (* p0 is opaque *)
  
  Transparent p0.
  rewrite /p0.
  done.
Qed.

(**
p4 は opaque である。
opaque なものを transparent にはできない。
*)

Goal 0 + p4 = 4.
Proof.
  Fail rewrite /p4.                         (* p4 is opaque *)
  Fail Transparent p4. (* Cannot make p4 transparent because it was declared opaque. *)
Admitted.

Print Strategy p4.                          (* transparent と表示された。。。 *)

(* END *)
