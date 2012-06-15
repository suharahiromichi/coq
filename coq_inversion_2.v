(*
   inversion_clearタクティクと、Derive Inversion_clearコマンド、は、
   どちらも、（不要となった）補題を消すこと(clear)をおこなう。
   なお、inversion_clearタクティクは、usingを使うことができない
   (Derive Inversion とも Derive Inversion_clearとも、組み合わせることができない)。
   
   coq_prolog_inversion.v も参考にすること。
   
   なお、なぜclearするのかは、よくわからない。
*)


(* LE *)


Inductive LE (n : nat) : nat -> Prop :=
| le_n : LE n n
| le_S : forall m : nat, LE n m -> LE n (S m).


(**********************)
(* 補題を使わない場合 *)
(**********************)


Goal forall n : nat, LE n 0 -> n = 0.
Proof.
  intros n H.
  inversion H as [ H1 | ].
  clear H H1.                               (* 不要だが、説明の都合上から *)
  reflexivity.
Qed.


Goal forall n:nat, LE n 0 -> n = 0.
  intros n H.
  inversion_clear H as [ H1 | ].
  (* H と H1が自動的に消える。 *)
  reflexivity.
Qed.




(******************)
(* 補題を使う場合 *)
(******************)


(* Derive Inversion コマンドで作成した補題 ident2 を使用して inversion ident1 を行う。*)
Derive Inversion le_0_inv with (forall n, LE n 0) Sort Prop.
Check le_0_inv.
(*
   forall (n : nat) (P : nat -> Prop),
   (LE n 0 -> n = 0 -> P 0) -> LE n 0 -> P n
   
   Pは、forall n のnを引数にとる述語。P n。
   LEの定義(Inductive)から、n = 0 となる。これから、LE n 0 -> n = 0 -> P 0。
   以上を組み合わせて、上記の項が定義される。
   Inductiveの定義がいくら複雑になっても、これは変わらない。
*)


Goal forall n, LE n 0 -> n = 0.
Proof.
  intros n H.
  inversion H using le_0_inv.
  (* LE n 0 -> n = 0 -> 0 = 0 *)
  intros H1 H2.                           (* 不要だが、 *)
  clear H1 H2.                            (* 説明の都合上から *)
  reflexivity.
Qed.


Goal forall n, LE n 0 -> n = 0.
Proof.
  intros n H.
  pattern n.
  apply le_0_inv.
  (* LE n 0 -> n = 0 -> 0 = 0 *)
  intros H1 H2.                             (* 不要だが、 *)
  clear H1 H2.                              (* 説明の都合上から *)
  reflexivity.
  apply H.
Qed.


(* なお、info invers とすると、refineを使った証明を出力するが、
   refine (le_0_inv n (fun n : nat => n = 0) _ H).
   これは項を直接与えているから、あまり参考にならないだろう。
*)




(* Derive Inversion_clear コマンドで補題を作成した場合 *)
Derive Inversion_clear le_0_inv' with (forall n, LE n 0) Sort Prop.
Check le_0_inv'.
(*
   forall (n : nat) (P : nat -> Prop),
   P 0 -> LE n 0 -> P n
   その補題は、条件がよりすくない。結果としてclearするのと同じ。
*)


Goal forall n, LE n 0 -> n = 0.
Proof.
  intros n H.
  inversion H using le_0_inv'.
  (* 0 = 0 *)
  reflexivity.
Qed.


Goal forall n, LE n 0 -> n = 0.
Proof.
  intros n H.
  pattern n.
  apply le_0_inv'.
  (* 0 = 0 *)
  reflexivity.
  apply H.
Qed.


(* END *)