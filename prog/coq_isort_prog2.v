(**
挿入ソートの証明駆動開発
 *)

(** * はじめに *)

(**
挿入ソート (Insertion Sort) を Coq の 「Programコマンド」を使って証明駆動開発してみます。

プログラムの定義や検証の方法は以下のサイトに基づいていますから、併読してください。
ただし、証明そのものは少し違うところがあります。

#<a href="http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt8.html">
プログラミング Coq 証明駆動開発入門(1)
</a>#
*)

Require Import List.
Require Import Arith.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Import Program.

(** * 準備 *)

(** 証明に perm と sort のコンストラクタを使いますから、
これらをHintデータベースに追加します。 *)

Hint Resolve perm_nil perm_skip perm_swap perm_trans Permutation_cons : perm.

Hint Resolve LSorted_nil LSorted_cons1 LSorted_consn : sort.

(** さらに不等号についての補題

[n < m -> n <= m]

をHintデータベースに追加します。*)
  
Hint Resolve lt_le_weak : lt_le.

(** * insert の定義と証明 *)

(**
最初に挿入関数 [insert] を証明付きで定義します。
定義自体は最初の参考文献とおなじです。

この関数では、リスト [l] に [a] を挿入した結果が関数の値 [l'] になるので、
これらをソートのために使う場合は次の関係を満たす必要があります。

(1) [a] と [l] を結合(cons)したものと、[l'] が Permutation の関係にあること。

(2) [l] がソートされているなら、[l'] もソートされていること。

のふたつです。これに加えて

(3) [a] と リスト [l] と [l'] との関係として、

(3.1) [a] は [l'] の先頭である（[a]が[l]の先頭に置かれる場合）、または、

(3.2) [l] と [l'] の先頭が同じ（[a]が[l]の途中以降に挿入される場合）

を追加しておきます。以上を連言でつないでいます。
それを関数の値に記載して、証明することになります。

関数の定義では、サブタイプコアーションが働くので、insert の再帰呼び出しでは、
証明の部分を無視して、リストだけを返す関数として使うことができます。
*)

Program Fixpoint insert (a : nat) (l : list nat) {struct l} : 
  {l' : list nat | Permutation (a :: l) l' /\
                   (LocallySorted le l -> LocallySorted le l') /\
                   (hd a l' = a \/ hd a l' = hd a l)} := 
  match l with
  | nil => a :: nil
  | x :: l' => 
    if le_gt_dec a x then
      a :: x :: l'
  else
    x :: (insert a l')
  end.
Obligation 1.
Proof.
  now auto with sort.
Defined.
Obligation 2.
  now auto with sort.
Defined.
Obligation 3.
Proof.
  split.
  - rewrite perm_swap.
    now auto with perm.
  - split.
    + intros Hxl'.
      assert (LocallySorted le l') as H1 by (inversion Hxl'; auto with sort).
      assert (LocallySorted le x0) as H2 by auto.
      destruct x0.
      * now auto with sort.
      * inversion Hxl'; simpl in o; destruct o; subst;
          now auto with sort lt_le.
    + now auto.
Defined.

(**
rewrite では、通常の [=] ではなく、
Permutation に対する rewrite が行われていることに注意してください。

ゴール [Permutation (a :: x :: l') (x :: x0)] に対して、
[[
perm_swap : forall (A : Type) (x y : A) (l : list A),
       Permutation (y :: x :: l) (x :: y :: l)
]]
でrewriteすることで、ゴールのPermutationの左側が書き換えられ、

[Permutation (x :: a :: l') (x :: x0)]

が得られます。
それができるのは、Import している [Sorting/Permutation.v] のなかで、
[Instance Permutation_Equivalence] が定義されているからですが、
このあたりについては、

#<a href="http://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf">
A Gentle Introduction to Type Classes and Relations in Coq
</a>#

を参照してください。
 *)

(**
また、[auto with sort lt_le] では、
[apply LSorted_consn] と [apply lt_le] が実行されています。
 *)

(**
実行してみます。証明の部分を取り除いて値だけを取り出すために、
[proj1_sig] の演算子 [`] を使います。
*)

Compute ` (insert 1 [2; 3]).             (** ==> [[1; 2; 3]]  *)

Compute ` (insert 2 [1; 3]).             (** ==> [[1; 2; 3]]  *)

(**
OCaml のコードを生成してみます。証明の部分のコードは含まれていません。
 *)

Extraction insert.
(**
[[
val insert : nat -> nat list -> nat list

let rec insert a = function
| Nil -> Cons (a, Nil)
| Cons (x, l') ->
  (match le_gt_dec a x with
   | Left -> Cons (a, (Cons (x, l')))
   | Right -> Cons (x, (insert a l')))
]]
*)


(** * Insertion Sort の定義と証明  *)

(**
最後にソート関数 isort を証明付きで定義します。
定義自体は最初の参考文献とおなじです。

また、その正しさの証明も同じで、ソート前の引数 [l] と、ソート結果の関数値 [l'] に対して、

(1) [l] と [l'] が Permutation の関係であること。

(2) [l'] がソートされていること。

のふたつで、それらを連言でつないでいます。
それを関数の値に記載して、証明することになります。

関数の定義では、サブタイプコアーションが働くので、isort の再帰呼び出しのみならず、
下位処理として呼び出す insert もリストだけを返す関数として使うことができます。
  *)

Program Fixpoint isort l {struct l} :  
  {l' : list nat | Permutation l l' /\ LocallySorted le l'} := 
  match l with 
  | nil => nil
  | a :: l' => insert a (isort l')
  end.
Obligations.
Obligation 1.
Proof.
  now auto with sort perm.
Defined.
Obligation 2.
Proof.
  remember (insert a x).
  destruct s; subst.
  destruct a0; subst.
  simpl.
  split.
  - eauto with perm.
  - destruct a0; now auto.
Defined.

(**
実行してみます。証明の部分を取り除いて値だけを取り出すために、
[proj1_sig] の演算子 [`] を使います。
*)

Compute ` (isort [0; 2; 1; 3]).             (** ==> [[0; 1; 2; 3]]  *)


(**
OCaml のコードを生成してみます。証明の部分のコードは含まれていません。
 *)

Extraction isort.
(**
[[
val isort : nat list -> nat list

let rec isort = function
| Nil -> Nil
| Cons (a, l') -> insert a (isort l')
]]
*)

(* END *)
