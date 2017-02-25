(**
挿入ソートの証明駆動開発
 *)

(** * はじめに *)

(**
挿入ソート (Insertion Sort) を Coq の 「Programコマンド」を使って証明駆動開発してみます。

プログラムの定義や検証の方法は以下のサイトに基づいていますから、併読してください。
ただし、証明そのものは少し違うところがあります。

#<a href="http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt8.html">#
プログラミング Coq 証明駆動開発入門(1)
*)

Require Import List.
Require Import Arith.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.

(** * 準備 *)

(** 証明に perm と sort のコンストラクタを使いますから、
これらをHintデータベースに追加します。 *)

Hint Resolve perm_nil perm_skip perm_swap perm_trans Permutation_cons : perm.

Hint Resolve LSorted_nil LSorted_cons1 LSorted_consn : sort.

(** さらに不等号についての補題

[n < m -> n <= m]

をHintデータベースに追加します。*)
  
Hint Resolve lt_le_weak : lt_le.

(** * insert の証明 *)

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
    
    (** Permutation で rewrite する。 *)
    
    now auto with perm.
  - split.
    + intros Hxl'.
      assert (LocallySorted le l') as H1 by (inversion Hxl'; auto with sort).
      assert (LocallySorted le x0) as H2 by auto.
      destruct x0.
      * now auto with sort.
      * inversion Hxl'; simpl in o; destruct o; subst;
          now auto with sort lt_le.
        
    (** apply LSorted_consn と apply lt_le が実行される。 *)
        
    + now auto.
Defined.

(** OCaml のコード *)

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


(** * Insertion Sort の証明  *)

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

(** OCaml のコード *)

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
