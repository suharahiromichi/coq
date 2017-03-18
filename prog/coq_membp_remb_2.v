(**
The Little Prover の memb?/remb をCoqで解いてみる
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
Coqの場合は、false と true からなる bool型のリストとし、もじ '?' の代わりに true とします。
  *)

(**
ソースコードは、
#<a href="https://github.com/suharahiromichi/coq/blob/master/prog/coq_membp_remb_2.v">
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
  - generalize (H xs').
    intro H'.
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

(**
これからは、TLP の範囲を越える事項ですが、
remb' の定義を「リストから 0 を除去する関数」の証明付き定義と考えると問題があります。

membp は 0 の有無しかチェックしていませんから、
remb の本体が「つねにnil」を返すような定義であっても問題なくパスします。これではだめです。

remb の厳密な定義は、(1)に加えて(2)も満たさないといけません。

(1) 結果のリストに 0 が含まれないこと。

(2) 結果のリストがもとのリストのサブリストであること。
 *)

(** サブリストを定義します。  *)

Section Sublist.
  Variable A : Type.
  Variable f : A -> bool.

  (** Sublist l' l <==> l' ⊆ l *)
  
  Inductive Sublist : list A -> list A -> Prop :=
  | SL_nil l : Sublist nil l
  | SL_skip x l' l : Sublist l' l -> Sublist l' (x :: l)
  | SL_cons x l' l : Sublist l' l -> Sublist (x :: l') (x :: l).
  
End Sublist.

Hint Constructors Sublist.

(**
定理を直接証明します。
(1) と (2) を連言(/\)でつなぎます。
また let ... in は普通の意味で、ys は構文的な意味しかもちません。
*)

Goal forall (xs : list nat),
    let ys := remb xs in
    ~ membp (remb xs) /\ Sublist ys xs.
Proof.
  intros xs.
  split.
  - apply le_membp_remb.
  - induction xs as [| x' xs' IHxs]; simpl.
    + now auto.                             (** SL_nil を使う。 *)
    + case x' as [|x''].
      * now auto.                           (** SL_Skip を使う。 *)
      * now auto.                           (** SL_cons を使う。 *)
Qed.

(**
「Program」コマンドでの定義に条件を追加します。
*)

Program Fixpoint remb'' (xs : list nat) :
  {ys : list nat | ~ membp (remb xs) /\ Sublist ys xs} :=
  match xs with
  | nil => nil
  | 0 :: xs' => remb'' xs'
  | x :: xs' => x :: remb'' xs'
  end.
Obligation 3.
Proof.
  split.
  - case x as [| x']; simpl.
    + generalize (H xs').
      intro H'.
      exfalso.
      now apply H'.
    + now trivial.
  -  now auto.                             (* SL_nil *)
Defined.

Compute ` (remb'' (0 :: 1 :: 0 :: nil)).    (** ==> [[1]] *)

Extraction remb''.

(**
生成されたコードには、Sublist は含まれていません。

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
