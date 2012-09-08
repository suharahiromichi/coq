(*
   Coqの等号とLeibnitz equalityが等価であることについて。
   
   http://d.hatena.ne.jp/m-a-o/touch/20110325/p1
   (2)equalityの話 を参考にした。
*)

(* Coq の equality *)
Inductive eq (A : Type) (x : A) : A -> Prop :=
  eq_refl : eq A x x.

(* Leibnitz equality *)
Definition leibnitz_eq (A : Type) (a b : A) : Prop :=
  forall P : A -> Prop, P a -> P b.

(* Agdaだと、Leibnitz equalityは、以下の型を持つ。
   {A : Set} -> A -> A -> Set1
*)

(* Leibnitz equality と coqのequality が等価であることを証明する。 *)
Theorem eq_leibnitz_eq : forall (A : Type) (a b : A),
  leibnitz_eq A a b <-> a = b.
Proof.
  intros A a b.
  split.
  
  (* leibnitz_eq A a b -> a = b *)
  intros H1.
  apply H1.
  reflexivity.
  
  (* a = a -> leibnitz_eq A a b *)
  unfold leibnitz_eq.
  intros H2.
  rewrite H2.
  intros P Hpb.
  apply Hpb.
Qed.

(* eq_ind の leibnitz_eq 版を定義する。 *)
Definition leibnitz_eq_ind : forall (A : Type) (x : A) (P : A -> Prop),
  P x ->forall y : A, leibnitz_eq A x y -> P y.
Proof.
  unfold leibnitz_eq.
  intros A x P H y H0.
  Check (H0 P H).
  apply (H0 P H).
Defined.
Print leibnitz_eq_ind.

Definition leibnitz_eq_ind' : forall (A : Type) (x : A) (P : A -> Prop),
  P x -> forall y : A, leibnitz_eq A x y -> P y :=
    fun (A : Type) (x : A) (P : A -> Prop) (H : P x) (y : A)
      (H0 : forall P0 : A -> Prop, P0 x -> P0 y) => H0 P H.

(* 参考：eq_indも同様な形で定義できる。 *)
Print eq_ind.
Print eq_rect.

Definition eq_ind_me : forall (A : Type) (x : A) (P : A -> Prop),
  P x -> forall y : A, eq A x y -> P y.
Proof.
  intros A x P H y H0.
  destruct H0.
  apply H.
Defined.
Print eq_ind_me.

Definition eq_ind_me' : forall (A : Type) (x : A) (P : A -> Prop),
  P x -> forall y : A, eq A x y -> P y :=
    fun (A : Type) (x : A) (P : A -> Prop) => eq_rect A x P.

Definition eq_ind_me'' : forall (A : Type) (x : A) (P : A -> Prop),
  P x -> forall y : A, eq A x y -> P y :=
    fun (A : Type) (x : A) (P : A -> Prop) (H : P x) (y : A) (H0 : eq A x y) =>
      match H0 in (eq _ _ y0) return (P y0) with
        | eq_refl => H
      end.

(*
ちなみに、Leibnitz equalityが関数の外延的等価性
forall (A B : Type) (f g  :  A -> B) , (forall x,  f x = g x) -> f = g.
を持つことをCoqでは証明できないよう。

http : //coq.inria.fr/stdlib/Coq.Logic.FunctionalExtensionality.html
とかいうライブラリがあるので。具体例として、

forall (A1 A2 : Type), (fun x : prod A1 A2=>(fst x, snd x))=(fun x=>x)
は外延的等価性の仮定なしには、Coqでは証明できない気がする。これが言えな
いと、CoqのTupleは圏論的な意味での直積にはなっていることが証明できない。
*)

(* END *)
