Require Import ssreflect.

(**
# 第8回

http://qnighy.github.io/coqex2014/ex8.html

## 課題32 (種別:A / 締め切り : 2014/05/25)

半群とは、結合的な二項演算を持つ集合のことである。

次のソースを埋めて、自然数の乗算のなす半群と、自然数の最大値関数のなす半群を定義せよ。また、
半群の直積を定義せよ。

G0とG1の(半群としての)直積とは、G0とG1の(集合としての)直積を台集合とし、二項演算は単に左側
をG0の二項演算、右側をG1の二項演算で計算するものを入れたものである。
*)

Require Import Arith.

Module Type SemiGroup.
  Parameter G : Type.
  Parameter mult : G -> G -> G.
  Axiom mult_assoc :
    forall x y z : G, mult x (mult y z) = mult (mult x y) z.
End SemiGroup.

(**
https://github.com/mzp/coq/blob/master/gallina.txt
- ParameterにはDefinitionで定義を与える
- AxiomにはTheoremで証明を与える。
*)

Module NatMult_SemiGroup <: SemiGroup.      (* 乗算のなす半群 *)
  Definition G := nat.
  Definition mult := mult.                  (* Peano.mult, Arith/Mult.v *)
  Theorem mult_assoc :
    forall x y z : G, mult x (mult y z) = mult (mult x y) z.
  Proof.
    apply mult_assoc.                       (* Mult.mult_assoc *)
  Qed.
End NatMult_SemiGroup.

Module NatMax_SemiGroup <: SemiGroup.       (* 最大値関数のなす半群 *)
  Definition G := nat.
  Definition mult := max.                   (* Max.max *)
  Theorem mult_assoc :
    forall x y z : G, mult x (mult y z) = mult (mult x y) z.
  Proof.
    apply Max.max_assoc.                    (* Arith.Max.v *)
  Qed.
End NatMax_SemiGroup.

Module SemiGroup_Product (G0 G1 : SemiGroup) <: SemiGroup. (* 半群の直積 *)
  Definition G := (G0.G * G1.G)%type.       (* natの掛け算ではない。prod G0.G G1.G と同じ。 *)
  Definition mult :=
    fun (a b : G) =>                        (* G は (G0.G * G1.G) と同じ。 *)
      match a, b with
        | (a0, a1), (b0, b1) => (G0.mult a0 b0, G1.mult a1 b1)
      end.
  Theorem mult_assoc :
    forall (x y z : G) , mult x (mult y z) = mult (mult x y) z.
  Proof.
    move=> x y z.
    case: x => [a0 a1].
    case: y => [b0 b1].
    case: z => [c0 c1].
    rewrite /mult.
    f_equal.
    apply G0.mult_assoc.
    apply G1.mult_assoc.
  Qed.
End SemiGroup_Product.

(**
ヒント

モジュールの練習です。モジュールは、名前空間としての用途の他に、このように構造の入った型を
抽象化する働きもあります。

CoqのモジュールシステムはほぼOCamlのモジュールシステムと同じものです。OCamlのモジュールシス
テムは有用ですが、Coqのモジュールシステムは他のCoqの機能(ClassやCanonical Structure)で代替
できることが多く、OCamlのそれと比べるとやや存在感が薄いかもしれません。

なお、Module Type中で用いられているParameterやAxiomは公理扱いではありません。
*)

(* END *)
