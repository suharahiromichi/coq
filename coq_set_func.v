(* 集合型関数 と タクティクによる関数定義 *)
(* 2011_01_22 *)


(*
   述語判定関数は、集合型関数の特別な形。
   Nat の <や<= は、sumbool型の述語判定関数である。
   coq_sumbool.v
   *)
(*
   DefinitionやLemmaなど、定義の開始は何を使っても同じである。
   違いが出るのは閉じるところだけである。


   DefinedとQedは、どちらも証明を閉じ、
   作成されたGallina項を変数に束縛するものである（変数定義）。
   但し以下のような違いがある。


   ・Defined：変数定義は透過的(Transparent)である。
   即ち、変数に関連付けた項を参照するおとはできる。したがって、計算することができる。


   ・Qed：変数定義は非透過的(Opaque)である。変数に関連付けた項は参照できない。
   （従って計算することはできない。）変数の型のみを参照できる。
   *)


Require Import List.
Inductive app : forall T, list T -> list T -> list T -> Prop :=
| app_nil : forall T xs, app T nil xs xs
| app_one : forall T a xs ys zs, app T xs ys zs -> app T (a :: xs) ys (a :: zs).


(**************)
(* 集合型関数 *)
(**************)
Definition                                  (* Lamma でもよい *)
  safe_append (T : Type) (xs ys : list T) :
  {zs : list T | app T xs ys zs}.
Proof.
  intros.
  induction xs.
  exists ys.
  apply app_nil.


  case IHxs.
  intros zs H.
  exists (a :: zs).
  apply app_one.
  apply H.
Defined.                                    (* Qed で閉じると計算されない *)


Definition append (T : Type) (a b : list T) := proj1_sig (safe_append T a b).
Eval cbv in append nat (1::2::3::nil) (4::5::6::nil).
(*
   safe_append自体をEvalても、引数が展開されるだけで、計算（簡約）されない。
   Qedで閉じると、safe_append が見えてしまい、やはり計算されない。
*)
(* coq_safety_prog.v も参照のこと。*)


(****************************)
(* タクティクによる関数定義 *)
(****************************)
Definition                                  (* Lamma でもよい *)
  append2 (T : Type) (xs ys : list T) : list T.
Proof.
  intros.
  induction xs.
  apply ys.
  apply cons.
  apply a.
  apply IHxs.
Defined.                                    (* Definedで閉じること *)
Eval cbv in append2 nat (1::2::3::nil) (4::5::6::nil).
Print append2.


(* 上と同じ定義を refine で書いた *)


Definition                                  (* Lamma でもよい *)
  append3 (T : Type) (xs ys : list T) : list T.
Proof.
  refine
    (fun (T : Type) (xs ys : list T) =>
      list_rect (fun _ : list T => list T) ys
      (fun (a : T) (_ IHxs : list T) => a :: IHxs) xs).
Defined.                                    (* Definedで閉じること *)
Eval cbv in append3 nat (1::2::3::nil) (4::5::6::nil).


(******************)
(* 通常の関数定義 *)
(******************)
Fixpoint append4 (T : Type) (xs ys: list T) : list T :=
  match xs with
    | nil => ys
    | x :: xs => x :: (append4 T xs ys)
  end.
Eval cbv in append4 nat (1::2::3::nil) (4::5::6::nil).


(* END *)