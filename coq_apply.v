(******************************************)
(* apply で証明することとはどういうことか *)
(******************************************)


(** 帰納型のチュートリアル **)
(** A Tutorial on [Co-]Inductive Types in Coq **)


(* 発展的内容 *)
(* 2.5 Relations as inductive types. *)


Print le.


(* 以下の証明は、coq内部的にはすべて同じ、Printで同じ結果になる。 *)
Theorem zero_leq_three: 0 <= 3.
  (* 普通の証明 *)
  constructor.
  constructor.
  constructor.
  constructor.
  Restart.


  (* applyを使った証明 *)
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n.
  Restart.


  (* applyにおける変数置き換えを省略せずに書いた証明 *)
  apply le_S with (n := 0) (m := 2).
  apply le_S with (n := 0) (m := 1).
  apply le_S with (n := 0) (m := 0).
  apply le_n with (n := 0).
  Restart.


  (* applyより先に、定数を適用しておく方法もある *)
  apply (le_S 0 2).
  apply (le_S 0 1).
  apply (le_S 0 0).
  apply (le_n 0).
Qed.


(* 0 <= 3 の証明 (Prop) を返す関数が定義された *)
Print zero_leq_three.                       (* 0 <= 3 *)


Lemma zero_leq_n (n : nat) : 0 <= n.
  intros n.
  elim n.                                   (* nat_indによる帰納の場合分け。 *)
  apply le_n.
  
  intros n0 H.
  apply le_S.
  apply H.
Qed.


Print zero_leq_n.
Eval compute in zero_leq_n 3.


(* 0 <= 3 の証明 (Prop) を返す関数が定義する。 *)
(* 直接定義する場合は、グローバルな定義として、Definitionを使う。 *)
Definition zero_leq_three' := zero_leq_n 3.
Print zero_leq_three'.                      (* 0 <= 3 *)


(* このような、別の定義もある。*)
Lemma zero_leq_three'' : 0 <= 3.
  apply zero_leq_n with (n := 3).           (* apply (zero_leq_n 3). でもよい。 *)
Qed.
Print zero_leq_three''.                     (* 0 <= 3 *)


(* このような、別の定義もある。*)
Lemma zero_leq_three''' : 0 <= 3.
  Proof zero_leq_n 3.
Print zero_leq_three'''.                     (* 0 <= 3 *)


(* Lemma を Defined、Qed を Defined としてもよい。 *)




Lemma zero_leq_four : 0 <= 4.
  apply le_S with (n := 0) (m := 3).
  apply zero_leq_n with (n := 3).
Qed.
Print zero_leq_four.                        (* 0 <= 4 *)


(* これは以下の定義と同じ *)
Definition zero_leq_four' := le_S 0 3 (zero_leq_n 3). (* 0 <= 4 *)


(* END *)