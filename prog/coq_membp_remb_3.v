(**
The Little Prover の memb?/remb をCoqで解いてみる（サブリスト改訂版）
 *)

Require Import Bool.
Require Import List.
Require Import Program.
Set Implicit Arguments.

(** * はじめに *)

(**
The Little Prover (TLP) の第6章では、memb?/remb という定理が扱われています。
これは、リニアなリストの要素から、文字 '?' を削除する関数 remb と、
これは、リニアなリストの要素に、文字 '?' が含まれるかを判定する関数 memb? が
定義されているとき、
任意のリスト xs に対して、(memb? (remb xs)) が必ず False になるというものです。

オリジナルはLisp系の言語なので、リストの要素は任意のデータでよいのですが、
Coqの場合は、自然数のリストとし、もじ '?' の代わりに 0 とします。
  *)

(**
ソースコードは、
#<a href="https://github.com/suharahiromichi/coq/blob/master/prog/coq_membp_remb_3.v">
ここ
</a>
にあります。
 *)

(**
まず、membp (memb? に対応する) の自然数のリストに 0 が含まれていることを判定する関数を定義ましす。
リストの先頭から見ていき 0 が含まれていたらそこで True を返します。
*)

Fixpoint membp (xs : list nat) : Prop :=
  match xs with
  | nil => False
  | 0 :: xs' => True
  | _ :: xs' => membp xs'
  end.

Compute membp (1 :: 0 :: 2 :: nil).         (** ==> [True] *)

Compute membp (1 :: 2 :: 3 :: nil).         (** ==> [False] *)

Compute membp nil.                          (** ==> [False] *)

(**
ついで、remb のリストから 0 を削除する関数を定義します。
リストの先頭から見ていき 0 なら、それを含まない結果を返し
false なら、それを含む結果を返します。
*)

Fixpoint remb (xs : list nat) : list nat :=
  match xs with
  | nil => nil
  | 0 :: xs' => remb xs'
  | x :: xs' => x :: remb xs'
  end.

Compute remb (0 :: 1 :: 0 :: nil).         (** ==> [[1]] *)

(** * memb?/remb の証明 *)

(**
memb?/remb に対応する membp_remb は、文字通りの定義です。
結果は偽であるため、「~」がついています。
 *)

Definition membp_remb (xs : list nat) := ~ membp (remb xs).

(** 以下に、membp_remb を証明します。線形リスト xs に対する帰納法と、
要素 x に対する場合分けだけで証明されています。
なお、帰納法の仮定IHxsは、ふたつめとみっつめのnowでトリビアルに使われます。
 *)
  
Lemma le_membp_remb : forall (xs : list nat), membp_remb xs.
Proof.
  unfold membp_remb.
  induction xs as [|x xs IHxs].
  - now simpl.
  (** x が 0 か 0 でないかで場合分けする。 *)
  - case x as [| x']; simpl.
    (** ここで帰納法の仮定を使う。 *)
    + now trivial.
    + now trivial.

  Restart.
  unfold membp_remb.
  intros xs.
  induction xs as [|x xs IHxs]; try auto.
  now case x.
Qed.

(**
memb?/remb は定理としては自明ですが、 0 が含まれないことをチェックする関数membpによって、
 0 を削除する関数rembが正しく動作していることを証明する、と考えることができます。

これは、関数の定義とその証明を同時におこなう証明駆動開発の一例となります。
Coqにはそれをサポートする「Program」コマンドがあります。
これを使って remb を再定義してみましょう。

remb' の値は、単なる list nat ではなく、
[{ys : list nat | ~ membp ys}]
すなわち、
[~ membp ys] を満たす [ys] の集合の要素、
となります。

これだと、最初に想定した型と違うので困ると思うかもしれませんが、
「Program」コマンドの中では、そのサブタイプ・コアーションの機能によって、
list boot 型と同一視されます。

remb' の結果が普通にconsされていることに気づいてください。

「Program」コマンドの中では、そのサブタイプ・コアーションは、
再帰呼び出しのみならず、他の（定義済みの）任意な関数に適用されます。
 *)

Program Fixpoint remb' (xs : list nat) : {ys : list nat | ~ membp ys} :=
  match xs with
  | nil => nil
  | 0 :: xs' => remb' xs'
  | x :: xs' => x :: remb' xs'
  end.
Obligation 2.
Proof.
  case x as [| x']; simpl.
  - generalize (H xs'); intro H'.
    exfalso.
    now apply H'.
  - now trivial.
Defined.

Compute ` (remb' (0 :: 1 :: 0 :: nil)).     (** ==> [[1]] *)

Extraction remb'.
(**
生成されたコードには、rembp は含まれていない。

[[
val remb' : nat list -> nat list,

let rec remb' = function
| Nil -> Nil
| Cons (x, xs') ->
  (match x with
   | O -> remb' xs'
   | S n -> let x0 = S n in Cons (x0, (remb' xs')))
]]
*)

(** * 証明駆動開発 *)

(** ** remb 条件を Inductive に定義する *)

(** remb を Inductive に定義した、Listwo0 (List without 0 のつもり) を定義します。 *)

Inductive Listwo0 : list nat -> Prop :=
| Wo0_nil      : Listwo0 nil
| Wo0_skip   l : Listwo0 l -> Listwo0 (0 :: l)
| Wo0_cons x l : x <> 0 -> Listwo0 l -> Listwo0 (x :: l).

Hint Constructors Listwo0.

Program Fixpoint remb'' (xs : list nat) : {ys : list nat | Listwo0 ys} :=
  match xs with
  | nil => nil
  | 0 :: xs' => remb'' xs'
  | x :: xs' => x :: remb'' xs'
  end.
Obligation 2.
Proof.
  apply Wo0_cons.
  - case x as [| x']; simpl.
    + generalize (H xs'); intro H'.
      exfalso.
      now apply H'.
    + now trivial.
  - now trivial.
Defined.

Compute ` (remb'' (0 :: 1 :: 0 :: nil)).    (** ==> [[1]] *)

(**
remb' の定義を「リストから 0 を除去する関数」の証明付き定義と考えると問題があります。
 *)

(** 0を抜いたサブリストの関係を定義します。  *)

Inductive Sublist0 : list nat -> list nat -> Prop :=
| SL0_nil         : Sublist0 nil nil
| SL0_skip   l' l : Sublist0 l' l -> Sublist0 l' (0 :: l)
| SL0_cons x l' l : x <> 0 -> Sublist0 l' l -> Sublist0 (x :: l') (x :: l).

Hint Constructors Sublist0.

Program Fixpoint remb''' (xs : list nat) :
  {ys : list nat | Sublist0 ys xs} :=
  match xs with
  | nil => nil
  | 0 :: xs' => remb''' xs'
  | x :: xs' => x :: remb''' xs'
  end.
Obligation 3.
Proof.
  apply SL0_cons.
  - case x as [| x']; simpl.
    + generalize (H xs'); intro H'.
      exfalso.
      now apply H'.
    + now trivial.
  - now trivial.
Defined.

Compute ` (remb''' (0 :: 1 :: 0 :: nil)).    (** ==> [[1]] *)

Extraction remb'''.

(**
生成されたコードには、Sublist0 は含まれていません。

[[
val remb'' : nat list -> nat list

let rec remb'' = function
| Nil -> Nil
| Cons (b, xs') ->
  (match b with
   |  0  -> remb'' xs'
   | False -> Cons (False, (remb'' xs')))
]]
 *)

(** * 帰納法の公理 *)

(**
TLPにもどって、帰納法による証明について考えてみましょう。
TLPでは、（例によって、天から降ってきた）「inductive claim」を証明しています。
これの導きかたは第6章の最後に記載されていますが、Coqの場合は、
リストの型定義にもとづく「公理」を使います。
 *)

Check list_ind : forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (a : A) (l : list A), P l -> P (a :: l)) ->
    forall l : list A, P l.

(**
これを membp_remb に適用すると次を得ます。
繰り返しますが、これは証明するべきものではなく、「公理」です。
 *)

Check list_ind membp_remb :
  membp_remb [] ->
  (forall (a : nat) (l : list nat), membp_remb l -> membp_remb (a :: l)) ->
  forall l : list nat, membp_remb l.

(**
この公理を使うなら、

[forall l : list nat, membp_remb l]

を証明するには、

[membp_remb []]

と

[forall (a : nat) (l : list nat), membp_remb l -> membp_remb (a :: l)]

とを証明すればよいことになります。後者は、TLPでは、l は nil でないことを条件に、
[(cdr l)] をとっていて、つまり、

[forall (l : list nat  ), membp_remb (tl l) -> membp_remb l]

となっています。おなじですね。
 *)

(**
実際の証明は、以下の通りです。
 *)

Goal forall xs, membp_remb xs.
Proof.
  intros xs.
  apply (list_ind membp_remb).
  - now simpl.
  - intros x' xs' IHxs.
    case x'; simpl.
    + now trivial.
    + now trivial.
Qed.

(**
最初の証明では、

[induction xs] というタクティクを使いましたが、

この公理を

[apply (list_ind membp_remb)]

として、適用することと同じです。
 *)

(* END *)
