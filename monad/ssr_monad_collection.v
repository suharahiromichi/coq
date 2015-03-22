(**
モナド・コレクション
Monad Collection

2015_03_21 @suharahiromichi

モナドのretやbindとモナド則を型クラスで定義する場合、Maybeとかの個々のモナドはそのインスタンスとなる。
インスタンスを生成するとき、Programコマンドを使って "Program Instance" とすると証明が自動化され便利なことがある。
ここでは、"Program Instance" を使っていろいろなモナドを定義してみる。

なお、Programコマンド他に、Program Definiton, Program Fixpoint, Program Lemma などもある。
(Coq Manual, Chapter 23 Program)

ただし、Program Fixpoint よりも Function のほうがよい場合もある。
https://github.com/suharahiromichi/coq/blob/master/gitcrc/coq_program_binary_power.v
*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "c >>= f"
         (at level 42, left associativity).      (* 文献1. *)

Class Monad (M : Type -> Type) :=
  {
    ret {A} : A -> M A;
    bind {A B} : M A -> (A -> M B) -> M B
      where "x >>= f" := (bind x f);
    monad_1 : forall (A : Type) (a : A) (f : A -> M A),
                ret a >>= f = f a;
    monad_2 : forall (A : Type) (m : M  A),
                m >>= ret = m;
    monad_3 : forall (A : Type) (f g : A -> M A) (m : M A),
                (m >>= f) >>= g = m >>= fun x => f x >>= g
  (* 左結合なので、最初の括弧は不要である。 *)
}.

Class Functor (F: Type -> Type) :=
  {
    fmap : forall {A B}, (A -> B) -> (F A -> F B)
  }.

(* Id Monad *)
Section Monad_Id.
  Definition MId (A : Type) : Type :=  A.
  Check MId : (Type -> Type).
  
  Check @bind.
  Program Instance : Monad MId :=
    {|
      ret A a := a;
      bind A B ma f := f ma
    |}.
  
  Program Instance : Functor MId :=
    {|
      fmap A B F := F
    |}.
End Monad_Id.

(* Maybe Monad *)
Section Monad_Maybe.
  Definition MMaybe := option.
  Check option : (Type -> Type).
  
  Program Instance : Monad MMaybe :=
    {|
      ret A a := Some a;
      bind A B ma f :=
        match ma with
          | None => None
          | Some a => f a
        end
    |}.
  Obligation 2.
  Proof.
    by case: m.
  Qed.
  Obligation 3.
  Proof.
    by case: m.
  Qed.
  
  Program Instance : Functor MMaybe :=
    {|
      fmap A B F := option_map F
    |}.
End Monad_Maybe.

(* List Monad *)
Section Monad_List.
  Definition MList := seq.
  
  Program Instance : Monad MList :=
    {|
      ret A a := a :: [::];
      bind A B ma f := List.flat_map f ma
    |}.
  Obligation 1.
  Proof.
    by rewrite List.app_nil_r.
  Qed.
  Obligation 2.
  Proof.
    elim: m.
    - by [].
    - move=> a l IH //=.
      by rewrite IH.
  Qed.
  Obligation 3.
  Proof.
    (* 
   List.flat_map g (List.flat_map f m) =
   List.flat_map (fun x : A => List.flat_map g (f x)) m
     *)
    admit.
  Qed.
  
  Program Instance : Functor MList :=
    {|
      fmap A B F := map F
    |}.
End Monad_List.

Section Monad_Stack.
  Definition S := nat.                      (* nat のスタック *)
  Definition MStack (T : Type) :=
    seq S -> (T * seq S).
  Check MStack : (Type -> Type).
  
  Program Instance : Monad MStack :=
    {|
      ret A n := fun q : seq S => (n, q);
      bind A B s :=
        fun c : A -> MStack B =>
          fun q : seq S =>
            let (n, q') := s q in c n q'
    |}.
  Obligation 2.
  Proof.
    admit.
  Qed.
  Obligation 3.
  Proof.
    admit.
  Qed.

  Check @bind : (forall M : Type -> Type,
                   Monad M -> forall A B : Type, M A -> (A -> M B) -> M B).
  
  Program Instance : Functor MStack :=
    {|
      fmap T S f := fun (mx : MStack T) =>
                      bind mx (fun x => ret (f x))
    |}.
End Monad_Stack.

  
Section Monad_State.
  Definition s := nat.                      (* 状態はnatひとつで持つ。 *)
  Definition MState (T : Type) := s -> T * s.
  Check MState : (Type -> Type).
  
  Program Instance : Monad MState :=
    {|
      ret A a := fun s => (a, s);
      bind A B s :=
        fun c =>
          fun q =>
            let (n, q') := s q in c n q'
    |}.
  Obligation 2.
  Proof.
    admit.
  Qed.
  Obligation 3.
  Proof.
    admit.
  Qed.
End Monad_State.

Section Monad_Cont.
  Definition MCont R A := (A -> R) -> R.
  Check MCont : (Type -> (Type -> Type)).

  Program Instance : Monad MCont :=
    {|
      bind R A c f :=
        fun (k : A -> R) => c (fun (a : A) => f a k);
      ret R A a :=
        fun k => k a
    |}.
End Monad_Cont

(*
Inductive MFree f a :=
  | Pure : a
  | Free : f (MFree f a).

Definition ret := Pure.

Definition bind c k :=
  match c with
    | Pure a => k a
    | Free f m => Free (fmap (bind k) f m)
  end.

*)
