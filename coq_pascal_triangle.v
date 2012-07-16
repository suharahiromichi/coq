(** Pascal' Triangel *)

(** 「パスカルの三角形の奇数のみを塗りつぶすと、シェルピンスキーのギャ
スケットが出現する」と簡単に説明されることがあるが、このガスケットが
cellular automaton rule 90を指すのは、多少無理がある。なぜなら、k番目の
セルは、パスカルの三角形（二項定理）は上の段のk-1とkで決まるのに対して、
rule 90は、k-1とk+1で決まるからである。また、rule 90は左側（負の方向）
にも伸びるので、kを負数に対しても定義しないといけない。rule 60とすると
話しは易しい。
*)

(**
[[
rule 60                          rule 90
   1                                1                     
   1 1                            1 0 1
   1 0 1                        1 0 0 0 1
   1 1 1 1                    1 0 1 0 1 0 1
   1 0 0 0 1                1 0 0 0 0 0 0 0 1
   1 1 0 0 1 1            1 0 1 0 0 0 0 0 1 0 1
   1 0 1 0 1 0 1        1 0 0 0 1 0 0 0 1 0 0 0 1
   1 1 1 1 1 1 1 1    1 0 1 0 1 0 1 0 1 0 1 0 1 0 1
]]
*)

(*
[[
二項係数の定義：
nCk = (n - 1)C(k - 1) + (n - 1)Ck

rule 60の定義：
60 = 0x3c = 00111100

111 110 101 100 011 010 001 000
 0   0   1   1   1   1   0   0
最右のセルは無視できるので、それを捨てると自然に二項係数に対応する。
11      10      01      00
 0       1       1       0

rule 90の場合は：
90 = 0x5a = 01011010

111 110 101 100 011 010 001 000
 0   1   0   1   1   0   1   0
真中のセルは無視できるので、それを捨てる。
二項定理と対応つかないわけではないが。
1_1 1_0         0_1 0_0
 0   1           1   0
]]

ew.wikipedia.orgにはちゃんと書いてあって、The pattern produced by an
elementary cellular automaton using rule 60 is exactly Pascal's
triangle of binomial coefficients reduced modulo 2（中略）.

Rule 90 produces the same pattern but with an empty cell separating
each entry in the rows.しかし列の中の各エントリーを空のセルで分離すると
*)

Require Import Arith.
Require Import Bool.

Fixpoint binomial (n k : nat) : nat :=
  match n, k with
    | _, O => 1                             (* 左端 *)
    | O, S k' => 0                          (* 頂上の空欄 *)
    | S n', S k' => binomial n' (S k') + binomial n' k'
  end.

Fixpoint ca60 (n k : nat) : bool :=
  match n, k with
    | _, O => true                          (* 左端 *)
    | O, S k' => false                      (* 頂上の空欄 *)
    | S n', S k' =>
      match (ca60 n' k'), (ca60 n' (S k')) with
        | true,  true  => false
        | true,  false => true
        | false, true  => true
        | false, false => false
      end
  end.

(* END *)
