(**
Coq/SSReflect で bool 変数ひとつの命題を b または ~~b に変形する方法

http://www.a-k-r.org/d/2023-03.html#a2023_03_01_1
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

(**
# 一般的な変換

書き方が長くても、証明項が大きくても構わない、というなら、一般的に変形できるのではないか、
扱いたい命題を一般的に定義してみよう。

BNF で、対象の命題を表現する。 P が命題、B が bool 式、V が bool 変数である

```
P = is_true B
  | B = B
  | not P
B = V
  | B == true
  | true == B
  | B == false
  | false == B
  | negb B
```

ここで、二重否定命題 not (not P) は扱わないことにすると以下のようになる 

```
P = is_true B
  | B = B
  | not (is_true B)
  | not (B = B)
B = V
  | B == true
  | true == B
  | B == false
  | false == B
  | negb B
```

これを ``is_true V`` もしくは ``is_true (negb V)`` に変形するのは以下のようにできる。

(1) 外側が (B = B), (not (B = B)) の場合は move/eqP あるいは apply/eqP して、
is_true (B == B), is_true (negb (B == B)) に変形する

(2) 外側が (not (is_true B)) の場合は move/negP あるいは apply/negP して、is_true (negb B) に変形する

(3) 外側が is_true B の場合はすでに外側が is_true なのでそのままにする

(1)(2)(3)で、外側が is_true B になるので、

(4) B 内部の bool な式を

``rewrite ?[true == _]eq_sym ?[false == _]eq_sym ?eqb_id ?eqbF_neg ?negbK.``

と書き換える。これは、

- ?[true == _]eq_sym で true == B を B == true に
- ?[false == _]eq_sym で false == B を B == false に
- ?eqb_id で B == true を B に
- ?eqbF_neg で B == false を negb B に
- ?negbK で negb (negb B) を B に

書き換える。

ぜんぶ ? がついているので、0回以上、書き換えられなくなるまで繰り返す。
まぁ、convertible で済むものも rewrite するので、証明項は必要以上に大きくなるかもしれないけれど。

そうすると、以下が残るはずである。

```
P = is_true B
B = V
  | negb V
```

つまり ``is_true V`` と ``is_true (negb V)`` だけになるはず、というわけである。
 *)

Goal forall b : bool, true = b.
Proof.
  move=> b.
  apply/eqP.
  (* true == b *)
  rewrite ?[true == _]eq_sym ?[false == _]eq_sym ?eqb_id ?eqbF_neg ?negbK.
  (* Goal : b *)
Admitted.

Goal forall b : bool, ~ (~~ b).
Proof.
  move=> b.
  apply/negP.
  (* Goal : ~~ ~~ b *)
  rewrite ?[true == _]eq_sym ?[false == _]eq_sym ?eqb_id ?eqbF_neg ?negbK.
  (* Goal : b *)
Admitted.

(**
# convertible な命題

convertible な命題はchengeタクティクで書き換えると、証明項は小さくなる。
*)

Goal forall b, false == b.
Proof.
  move=> b.
  rewrite -[false == b]/(~~ b).
  (* Goal : ~~ b *)
  Undo 1.
  
  change (false == b) with (~~ b).
  Undo 1.
  
  (* Ltac を使用することで、変換前後の命題を書かずに済ます。 *)
  repeat match goal with
         | |- context C [true == ?b] => let t := context C [b] in change t
         | |- context C [false == ?b] => let t := context C [negb b] in change t
         end;
    rewrite ?eqb_id ?eqbF_neg ?negbK.
Admitted.

(* END *)
