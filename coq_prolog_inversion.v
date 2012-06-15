(*
   10/12/30
   Inductiveで定義するものにはコンストラクタとPropがある。
   前者はスコーレム関数で、後者はPrologのルール（公理）だと思うとする。
   導出原理を実行するのが、inversionタクティクスである。
   ただし、inductionを併用する必要がある。（使い分けについて要補足）
   コンストラクタの場合はinversionとinductionが同じ結果になる場合もある。
   
   とりあえず、Propを値とするInductiveに関係する証明のためには、inversionが有効であると覚えておく。
*)


Require Import List.


(* APPEND *)
Inductive append : list nat -> list nat -> list nat -> Prop :=
| append0 : forall l : list nat,
  append nil l l
| append1 : forall (a : nat) (l1 l2 l3 : list nat),
  append l1 l2 l3 -> append (a :: l1) l2 (a :: l3).
Hint Resolve append0 append1 : append.


(* LENGTH *)
Inductive length : list nat -> nat -> Prop :=
| length0 :
  length nil 0
| length1 : forall (l : list nat) (n : nat) (z : nat),
  length l n -> length (z :: l) (S n).
Hint Resolve length0 length1 : length.


Lemma append_123 : append (1::nil) (2::3::nil) (1::2::3::nil).
Proof.
  info auto with append.
Qed.


Lemma append_1_23_L : exists A : list nat, append (1::nil) (2::3::nil) A.
Proof.
  info eauto with append.
Qed.
Lemma append_1_23_L' : exists A : list nat, append (1::nil) (2::3::nil) A.
Proof.
  eapply ex_intro.                          (* eapply *)
  simple apply append1.
  simple apply append0.
Qed.
Print append_1_23_L.


Lemma append_1_L_123 : exists A : list nat, append A (2::3::nil) (1::2::3::nil).
Proof.
  info eauto with append.
Qed.
Print append_1_L_123.


Lemma append_L_L_123 :
  exists A : list nat, exists B : list nat , append A B (1::2::3::nil).
Proof.
  info eauto with append.
Qed.
Print append_L_L_123.


Definition app_len (a b : list nat) (l : nat) :=
  forall c : list nat,
    append a b c -> length c l.
Check app_len.


Lemma lem_app_len :
  app_len (1::nil) (2::3::nil) 3.
Proof.
  unfold app_len.
  intros.
  inversion H.
  inversion H4.
  info auto with length.
Qed.


(* LIST_IN *)
Inductive list_in {A : Type} : A -> list A -> Prop :=
| in_hd : forall a l, list_in a (a :: l)
| in_tl : forall a b l, list_in a l -> list_in a (b :: l).


Goal forall l, list_in 0 (1 :: l) -> list_in 0 l.
Proof.
  intros l H.
  inversion H as [ | a b l' H' H1 [H2 H3] ].
  exact H'.
Qed.


Goal forall l, list_in 0 (1 :: l) -> list_in 0 l.
Proof.
  intros l H.
  inversion_clear H as [ | a b l' H' ].
  exact H'.
Qed.


Inductive twoEls : list nat -> Prop :=
| TwoEls : forall x y, twoEls (x :: y :: nil).


(* -> False でなくても、-> True でもなんでもよい。 *)
Theorem twoEls_nil : twoEls nil -> False.
Proof.
  intros H.
  inversion H.                              (* H : twoEls nil を成立させれず、終了 *)
Qed.


Theorem twoEls_two : forall ls, twoEls ls -> length ls 2.
Proof.
  intros ls H.
  inversion H.
  info auto with length.
Qed.




(* EVEN *)


Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).
Hint Resolve EvenO EvenSS : even.


Goal forall n, even (S (S n)) -> even n.
Proof.
  intros n H.
  inversion H.
  apply H1.
Qed.


Lemma even_inv :  forall n, even n -> even (S (S n)).
Proof.
  intros n H.
  inversion H as [H1|H2].
  auto with even.
  auto with even.
Qed.
(* even_inv と EvenSS は似ているが「逆」である。
   これがthe reason for the tactic name, inversion *)


Goal even 1 -> False.
Proof.
  intros H.
  inversion H.                              (* even 1 を成立させられない。 *)
Qed.


Goal even 3 -> False.
Proof.
  intros H.
  inversion H as [H1|H2].                   (* even 3 から even 1 を導く。 *)
  inversion H1.                             (* even 1 を成立させられない。 *)
Qed.




(* LE *)


Inductive LE (n : nat) : nat -> Prop :=
| le_n : LE n n
| le_S : forall m : nat, LE n m -> LE n (S m).


Goal forall n : nat, LE n 0 -> n = 0.
Proof.
  intros n H.
  inversion H as [ H1 | H2].
  reflexivity.
Qed.


Goal forall n:nat, LE n 0 -> n = 0.
  intros n H.
  inversion_clear H as [H1|].               (* inversion_clearとしても同じ。 *)
  reflexivity.
Qed.


(* Derive Inversion コマンドで作成した補題 ident2 を使用して inversion ident1 を行う。*)
Derive Inversion le_0_inv with (forall n, LE n 0) Sort Prop.
Check le_0_inv.


Goal forall n, LE n 0 -> n = 0.
Proof.
  intros n H.
  info inversion H using le_0_inv.
  (* LE n 0 -> n = 0 -> 0 = 0 *)
  intros H1 H2.
  reflexivity.
Qed.


(* 上の例で inversion H using le_0_inv がしていることは、
   pattern n; apply le_0_inv, H に等しい。*)
Goal forall n, LE n 0 -> n = 0.
Proof.
  intros n H.
  pattern n.
  Check le_0_inv.
  apply le_0_inv.
  intros H1 H2.
  reflexivity.
  apply H.
Qed.


(* 4.3.1 Interactive mode *)


Theorem not_le_Sn_0' : forall n : nat, ~ (LE (S n) 0).
Proof.
  red.
  intros n H.
  inversion H.                              (* Hを成立させられないので、証明終了 *)
Qed.




Derive Inversion le_Sn_0_inv with (forall n :nat, LE (S n) 0) Sort Prop.
Check le_Sn_0_inv.


Goal forall n p : nat, ~ (LE (S n)  0).
Proof.
  intros n p H.
  inversion H using le_Sn_0_inv.            (* Hを成立させられないので、証明終了 *)
Qed.


Theorem le_reverse_rules :
  forall n m : nat, LE n m ->
    n = m \/ exists p, LE n p /\ m = S p.
Proof.
  intros n m H.
  inversion H.
  left.
  trivial.
  right.
  exists m0.
  split.
  apply H0.
  reflexivity.
Qed.






(***********************************)




(* 19/25 inversion *)
(*
   inversion は仮定に対して帰納的な定義を適用し、その仮定が成立する為の前提を導き出すか、
   あるいはそもそもそのような前提が存在しない（＝仮定が間違っている）ので証明終了、
   を導いてくれます。
   ある種の証明では inversion を使うと証明が非常に簡単なのですが、
   中で何をしているのかは簡単には説明するのは難しいです。
*)


(* inversionが役に立つ例というとsmall-stepの決定性の証明とかです。*)
Inductive term : Set :=
| TmTrue : term
| TmFalse : term
| TmIf : term -> term -> term -> term.


Inductive eval : term -> term -> Prop :=
| EvIfTrue : forall t2 t3, eval (TmIf TmTrue t2 t3) t2 
| EvIfFalse : forall t2 t3, eval (TmIf TmFalse t2 t3) t3
| EvIf : forall t1 t1' t2 t3, eval t1 t1' ->
  eval (TmIf t1 t2 t3) (TmIf t1' t2 t3).


(* 上記の様にsmall-stepの規則を定義して、下記を証明します。*)


Theorem eval_deterministic : forall t t' t'', (eval t t') -> (eval t t'') -> (t' = t'').
Proof.
  intros t t' t'' tEt' tEt''.
  
  (* まず tEt' について induction で場合分けをします。*)
  induction tEt' as [t2 t3|t2 t3|t1 t1' t2 t3 t1Et1'] in t'', tEt'' |-*.
  (*
     最初の場合は、t' = TmIf TmTrue t2 t3 の場合です。
     ここで tEt'' については induction ではなくinversion を使うと、
     tEt'' が成立するような t'' の場合分けを自動で行ってくれます。
     *)
  inversion tEt'' as [t2_ t3_| t2_ t3_| t1_ t1'_ t2_ t3_ t1Et1'_].
  reflexivity.
  (*
     ここでinversion t1Et1'_を行います。
     TmTrueが何かにevalされる規則はevalに無いので、仮定が不成立となり、
     goalの証明が終わります。
     *)
  inversion t1Et1'_.
  
  (* t' = TmIfFalse t2 t3 の場合は同様の証明をすればOKです。*)
  inversion tEt'' as [t2_ t3_| t2_ t3_| t1_ t1'_ t2_ t3_ t1Et1'_].
  reflexivity.
  inversion t1Et1'_.
  
  (*
     最後は、t' = TmIf t1 t2 t3 の場合についてです。
     やはりtEt''についてinversionします。
     *)
  inversion tEt'' as [t2_ t3_| t2_ t3_| t1_ t1'_ t2_ t3_ t1Et1'_].
  (*
   ここでも、H0とt1Et1'から、eval TmTrue t1'を作って
   inversionして仮定が成立しない事を使って証明します。
   *)
  rewrite <- H0 in t1Et1'.
  inversion t1Et1'.


  (* 同様にして、TmFalse の場合も証明出来ます。*)
  rewrite <- H0 in t1Et1'.
  inversion t1Et1'.
  
  (* 最後はIHt1Et1'のt''をt1'_にして、t1Et1'_と組み合わせてゴールを導きます。*)
  rewrite (IHt1Et1' t1'_ t1Et1'_).
  reflexivity.
Qed.


(* END *)