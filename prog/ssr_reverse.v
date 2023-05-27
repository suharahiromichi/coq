(**
初心に戻ってリストのappendとreverseを解き直してみる。
*)

From mathcomp Require Import all_ssreflect.
Require Import Program.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section List.
  
  Variable A : Type.
  
  (* append 命題 *)
  Inductive append : seq A -> seq A -> seq A -> Prop :=
  | app_nil (b : seq A) : append [::] b b
  | app_cons (h : A) (a b c : seq A) : append a b c -> append (h :: a) b (h :: c).
  Hint Constructors append.
  
  (* append 関数 *)
  Fixpoint app (a b : seq A) : seq A :=
    match a with
    | [::] => b
    | h :: a => h :: app a b
    end.
  
  (* 命題と関数の同値の証明 *)
  Lemma appapp : forall (a b c : seq A), append a b c <-> app  a b = c.
  Proof.
    split.
    - elim=> b'' //= a' b' c' H IH.
      by rewrite IH.
    - elim: a b c => //=.
      + by move=> b c ->.
      + move=> n' a' IH b' c' <-.
        apply: app_cons.
        by apply: IH.
  Qed.
  
  (* Program コマンドで定義する。 *)
  Program Fixpoint app' (a b : seq A) : {c | append a b c} :=
    match a with
    | [::] => b
    | h :: a => h :: app' a b
    end.
  (* Obligation なし *)
  
  (* ******************************* *)
  (* うしろに append する (snoc) の例 *)
  (* ******************************* *)
  
  (* reverse1 命題 *)
  Inductive reverse1 : seq A -> seq A -> Prop :=
  | rev_nil : reverse1 [::] [::]
  | rev_cons (h : A) (a b c : seq A) :
      reverse1 a b -> append b [:: h] c -> reverse1 (h :: a) c.
  Hint Constructors reverse1.
  
  (* rev1 関数 *)  
  Fixpoint rev1 (a : seq A) : seq A :=
    match a with
    | [::] => [::]
    | h :: a => app (rev1 a) [:: h]
    end.

  (* 命題と関数の同値の証明 *)  
  Lemma revrev1l (a b : seq A) : reverse1 a b <-> rev1 a = b.
  Proof.
    split.
    - elim=> //= n a' b' c' H1 H2 H3.
      apply/appapp.
      by rewrite H2.
  - elim: a b => [b' H | n a IH c H].
    + by rewrite -H.
    + apply: rev_cons.
      * by apply: IH.
      * by apply/appapp.
  Qed.
  
  (* ************* *)
  (* 末尾再帰 の例 *)
  (* ************* *)
  
  (* reverse2 命題 *)
  Inductive reverse2 : seq A -> seq A -> seq A -> Prop :=
  | rev2_nil (b : seq A) : reverse2 [::] b b
  | rev2_cons (h : A) (a b c : seq A) :
      reverse2 a (h :: b) c -> reverse2 (h :: a) b c.
  Hint Constructors reverse2.
  
  (* rev2 関数 *)  
  Fixpoint rev2 (a b : seq A) : seq A :=
    match a with
    | [::] => b
    | h :: a => rev2 a (h :: b)
    end.
  
  (* 命題と関数の同値の証明 *)
  Lemma revrev2 (a b c : seq A) : reverse2 a b c <-> rev2 a b = c.
  Proof.
    split.
    - by elim=> //=.
    - elim: a b c => [b c | h a IH b c H].
      + rewrite /rev2 => <-.
        by apply: rev2_nil.
      + apply: rev2_cons.
        by apply: IH.
  Qed.

  (* Program コマンドを使用する。 *)
  
  Program Fixpoint rev2' (a b : seq A) : {c : seq A | reverse2 a b c} :=
    match a with
    | [::] => b
    | h :: a => rev2' a (h :: b)
    end.
  (* Obligation なし *)

End List.
  
Goal reverse2 [:: 1;2;3] [::] [:: 3;2;1].
Proof.
  apply: rev2_cons.
  apply: rev2_cons.
  apply: rev2_cons.
  apply: rev2_nil.
Qed.

Compute rev2 [:: 1;2;3] [::].               (* [:: 3;2;1] *)

Compute proj1_sig (rev2' [:: 1;2;3] [::]).  (* [:: 3;2;1] *)


(**
   依存型Vectorの定義：
   https://www.math.nagoya-u.ac.jp/~garrigue/lecture/2011_AW/coq7.pdf
 *)
Section Vector.

  Variable A : Set.
  
  (* 依存型Vectorの定義 *)
  Inductive vector : nat -> Set :=
  | Vnil : vector 0
  | Vcons : forall n, A -> vector n -> vector n.+1.
  
  Check Vnil : vector 0.
  Check fun (h : A) => Vcons h Vnil : vector 1.
  
  (* vappend命題 *) 
  Inductive vappend : forall (n m : nat),
      vector n -> vector m -> vector (n + m) -> Prop :=
  | vapp_nil : forall (n : nat) (b : vector n), vappend Vnil b b
  | vapp_cons : forall (h : A) (n m : nat)
                       (a : vector n) (b : vector m) (c : vector (n + m)),
      vappend a b c -> vappend (Vcons h a) b (Vcons h c).
  Hint Constructors vappend.

  (* vappend関数 *)
  Fixpoint vapp (n m : nat) (a : vector n) (b : vector m) : vector (n + m) :=
    match a with
    | Vnil => b
    | Vcons n h t => Vcons h (vapp t b)
  end.
  
  (* 命題と関数の同値の証明 *)
  Lemma vappapp (n m : nat) (a : vector n) (b : vector m) (c : vector (n + m)) :
    vappend a b c <-> vapp a b = c.
  Proof.
    split.
    - elim=> //= h n' m' a' b' c' H1 H2.
      by subst.
    - elim: a b c => //= [b c H | n' m' a IHa b c H]; subst.
      + done.
      + apply: vapp_cons.
        by apply: IHa.
  Qed.
  
  (* Program コマンドで定義する。 *)
  Program Fixpoint vapp' (n m : nat) (a : vector n) (b : vector m)
    : {c | vappend a b c} :=
  match a with
  | Vnil => b
  | Vcons n h t => Vcons h (vapp' t b)
  end.

  (* reverse の命題はうまく定義できない。 *)
  Fail Inductive vreverse : forall (n m : nat),
      vector nat n -> vector nat m -> vector nat (n + m) -> Prop :=
  | vrev_nil : forall (n : nat) (b : vector nat n), vreverse (Vnil nat) b b
  | vrev_cons : forall (h : nat) (n m : nat)
                       (a : vector nat n) (b : vector nat m) (c : vector nat (n + m).+1),
    vreverse a (Vcons h b) c -> vreverse (Vcons h a) b c.
  Fail Hint Constructors vreverse.
  
  Fail Inductive vreverse : forall (n : nat), vector nat n -> vector nat n -> Prop :=
  | vrev_nil : vreverse (Vnil nat) (Vnil nat)
  | vrev_cons (h : nat) (n : nat) (a b : vector nat n) (c : vector nat n.+1) :
      vreverse a b -> vappend b (Vcons h (Vnil nat)) c -> vreverse (Vcons h a) c.
  
  Fail Fixpoint vrev (n : nat) (a : vector nat n) : vector nat n :=
  match a with
  | Vnil => Vnil nat
  | Vcons n h t => vapp (vrev a) (Vcons h (Vnil nat))
  end.
  
  (* vreverse関数 *)
  Program Fixpoint vrev (n m : nat) (a : vector n) (b : vector m)
    : (vector (n + m)) :=
  match a with
  | Vnil => b
  | Vcons n h t => vrev t (Vcons h b)
  end.
  Next Obligation.
  Proof.
    by rewrite addSnnS.
  Defined.

End Vector.

Check Vnil nat : vector nat 0.
Check Vcons 100 (Vnil nat).

Definition data1 := Vcons 1 (Vcons 2 (Vnil nat)).
Definition data2 := Vcons 3 (Vcons 4 (Vnil nat)).
Definition data12 := Vcons 1 (Vcons 2 (Vcons 3 (Vcons 4 (Vnil nat)))).

Goal vappend data1 data2 data12.
Proof.
  apply: vapp_cons.
  apply: vapp_cons.
  apply: vapp_nil.
Qed.

Compute vapp data1 data2. (* = Vcons 1 (Vcons 2 (Vcons 3 (Vcons 4 (Vnil nat)))) *)
Compute proj1_sig (vapp' data1 data2).
(* (* = Vcons 1 (Vcons 2 (Vcons 3 (Vcons 4 (Vnil nat)))) *) *)

Compute vrev data1 (Vnil nat).              (* XXX *)

Require Import Extraction.
Extraction vapp.
(** val vapp : nat -> nat -> 'a1 vector -> 'a1 vector -> 'a1 vector **)
(*
let rec vapp _ m a b =
  match a with
  | Vnil -> b
  | Vcons (n, h, t) -> Vcons ((addn n m), h, (vapp n m t b))
 *)

Extraction vrev.
(** val vrev : nat -> nat -> 'a1 vector -> 'a1 vector -> 'a1 vector **)
(* 
let rec vrev _ m a b =
  match a with
  | Vnil -> b
  | Vcons (n, h, t) -> vrev n (S m) t (Vcons (m, h, b))
 *)

(* END *)
