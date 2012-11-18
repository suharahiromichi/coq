(*
   Maybeモナド と Listモナドの証明
   2012_11_18
   
   「わかめモナ化」mzpさんの発表をもとに、独自にList Monadを追加した。
   >>= オペレータの優先順位を低くしているので、括弧の位置が違う。
   *)

(*
   (復習)モナドとは
   Haskell風モナドの定義。 ただし `return` はCoqでは予約語なので、
   `ret` に変更してある。

   ret x >>= f = f x
   m >>= ret = m
   m >>= f >>= g = m >>= (fun x => f x >>= g)

   括弧を補った表記：
   ((ret x) >>= f) = (f x)
   (m >>= ret) = m
   ((m >>= f) >>= g) = (m >>= (fun x => f x >>= g))
   *)

Module MaybeMonad.
  (* bindとreturnの定義 *)
  Definition bind {A B : Type} (m : option A) (f : A -> option B) : option B :=
    match m with
      | None => None
      | Some v => f v
    end.
  (* 中置演算子を割り当てる *)
  Infix ">>=" := bind (left associativity, at level 61).
  
  Definition ret {A : Type} (v : A) : option A :=
    Some v.
  
  (* Evalしてみる *)
  Eval compute in ret 1.
  Eval compute in Some 1 >>= (fun x => ret (1 + x)).
  
  (* モナド則 その1 *)
  Theorem monad_1: forall A B (f : A -> option B) x,
    ret x >>= f = f x.
  Proof.
    intros A B f x.
    simpl.
    reflexivity.
  Qed.
  
  (* モナド則 その2 *)
  Theorem monad_2: forall A (m : option A),
    m >>= ret = m.
  Proof.
    intros A m.
    destruct m.
    (* Some a >>= ret = Some a *)
    simpl.
    unfold ret.
    reflexivity.
    (* None >>= ret = None *)
    simpl.
    reflexivity.
  Qed.
  
  (* モナド則 その3 *)
  Theorem monad_3: forall A B C (f : A -> option B) (g : B -> option C) m,
    m >>= f >>= g = m >>= (fun x => f x >>= g).
  (* >>= は右結合で、最低優先度とする。 *)
  Proof.
    intros A B C f g m.
    destruct m.
    (* Some a >>= f >>= g = Some a >>= (fun x : A => f x >>= g) *)
    simpl.
    reflexivity.
    (* None >>= f >>= g = None >>= (fun x : A => f x >>= g) *)
    simpl.
    reflexivity.
  Qed.
  
  (* Extractしよう。OCamlに変換しましょう。*)
  Require Import ExtrOcamlBasic.
  Extraction "maybeMonad.ml" bind ret.
End MaybeMonad.

Module ListMonad.
  Require Import List.
  (* bindとreturnの定義 *)
  Fixpoint bind {A B : Type} (m : list A) (f : A -> list B) : list B :=
    match m with
      | nil => nil
      | x :: xs => (f x) ++ (bind xs f)
    end.
  (* :: と ++ は right assoc level 60 *)
  (* 中置演算子を割り当てる *)
  Infix ">>=" := bind (left associativity, at level 61).
  
  Definition ret {A : Type} (v : A) : list A :=
    v :: nil.
  
  (* Evalしてみる *)
  Eval compute in ret 1.
  Eval compute in (fun x => ret (1+x)) 1.
  Eval compute in bind (ret 1) (fun x => ret (1+x)).
  Eval compute in (ret 1) >>= (fun x => ret (1+x)).
  Eval compute in ret 1 >>= fun x => ret (1+x).
  (* op.の優先順位に注意 *)
  Eval compute in (1 :: nil) >>= fun x => ret (1+x). 
  
  Check List.app_nil_r.
  Check List.app_assoc.
  
  (* モナド則 その1 *)
  Theorem monad_1: forall A B (f : A -> list B) x,
    ret x >>= f = f x.
  Proof.
    intros A B f x.
    simpl.
    apply app_nil_r.
  Qed.
  
  (* モナド則 その2 *)
  Theorem monad_2: forall A (m : list A),
    m >>= ret = m.
  Proof.
    intros A m.
    induction m.
    (* nil >>= ret = nil *)
    simpl.
    reflexivity.
    (* a :: m >>= ret = a :: m *)
    simpl.
    rewrite IHm.
    reflexivity.
  Qed.
  
  (* bind の app に対する分配則を証明しておく。 *)
  Lemma bind_distro : forall {A B : Type} (m n : list A) (f : A -> list B),
    m ++ n >>= f = (m >>= f) ++ (n >>= f).
  Proof.
    intros A B m n f.
    induction m.
    (* nil ++ n >>= f = nil >>= f ++ n >>= f *)
    simpl.
    reflexivity.
    (* (a :: m) ++ n >>= f = a :: m >>= f ++ n >>= f *)
    induction n.
    simpl.
    rewrite app_nil_r.
    rewrite app_nil_r.
    reflexivity.
    (* (a :: m) ++ a0 :: n >>= f = (a :: m >>= f) ++ (a0 :: n >>= f) *)
    simpl.
    rewrite IHm.
    simpl.
    apply app_assoc.
  Qed.
  
  (* モナド則 その3 *)
  Theorem monad_3: forall A B C (f : A -> list B) (g : B -> list C) m,
    m >>= f >>= g = m >>= (fun x => f x >>= g).
  (* >>= は右結合とする。 *)
  Proof.
    intros A B C f g m.
    induction m.
    (* nil >>= f >>= g = nil >>= (fun x : A => f x >>= g) *)
    simpl.
    reflexivity.
    (* a :: m >>= f >>= g = a :: m >>= (fun x : A => f x >>= g) *)
    simpl.
    rewrite <- IHm.
    apply bind_distro.
  Qed.
  
  (* Extractしよう。OCamlに変換しましょう。*)
  Require Import ExtrOcamlBasic.
  Extraction "listMonad.ml" bind ret.
End ListMonad.

(*    
   参考文献
   * [Maybe monad is monad — Gist]
   (https://gist.github.com/306417 "Maybe monad is monad — Gist")
   * [Coq](http://coq.inria.fr/)
   * [プログラミング Coq](http://www.iij-ii.co.jp/lab/techdoc/coqt/ "プログラミング Coq")
   * [ソフトウェアの基礎](http://proofcafe.org/sf/ "ソフトウェアの基礎")
   *)

(* END *)
