(**
ProofCafe 名古屋 補足資料

萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版

[http://www.morikita.co.jp/books/book/3287]

3.9 コマンド Definition, Lemma ... Qed ... 補足説明

@suharahiromichi

2019_08_17
*)

From mathcomp Require Import all_ssreflect.
Require Import Ascii String.
Open Scope string_scope.

(**
# 3.9.1 Definition
 *)

(**
# 3.9.2 Lemma ... Qed
 *)

Definition p0 := @Ordinal 5 0 is_true_true.
Definition p1 : 'I_5. Proof. by apply: (@Ordinal 5 1). Defined.
Lemma      p2 : 'I_5. Proof. by apply: (@Ordinal 5 2). Defined.
Definition p3 : 'I_5. Proof. by apply: (@Ordinal 5 3). Qed.
Lemma      p4 : 'I_5. Proof. by apply: (@Ordinal 5 4). Qed.

Compute p0 + p1.                (* = 1 *)
Compute p0 + p2.                (* = 2 *)
Compute p0 + p3.                (* = let '@Ordinal _ m _ := p3 in m *)
Compute p0 + p4.                (* = let '@Ordinal _ m _ := p4 in m *)


Definition p0' : 'I_4. Proof. by apply: (@Ordinal 4 0). Qed.
Definition p1' : 'I_4. Proof. by apply: (@Ordinal 4 1). Qed.
Print p1'.                  (* = Ordinal (n:=4) (m:=1) is_true_true *)

Compute p0' + p1'.
(*
= (fix Ffix (x x0 : nat) {struct x} : nat :=
  match x with
  | 0 => x0
  | x1.+1 => (Ffix x1 x0).+1
  end) (let '@Ordinal _ m _ := p0' in m) (let '@Ordinal _ m _ := p1' in m)
 *)

Definition p0 : 'I_4. Proof. by apply: (@Ordinal 4 0). Defined.
Definition p1 : 'I_4. Proof. by apply: (@Ordinal 4 1). Defined.
Print p1.                   (* = Ordinal (n:=4) (m:=1) is_true_true *)

Compute p0 + p1.                            (* = 1 *)


Definition string_dec_qed : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.
Proof.
 decide equality; apply ascii_dec.
Qed.
Print string_dec_qed.


Definition string_dec : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.
Proof.
 decide equality; apply ascii_dec.
Defined.
Print string_dec.

Definition eqString (s t : string) : bool :=
  match string_dec_qed s t with
  | left _ => true
  | right _ => false
  end.

Definition eqString (s t : string) : bool :=
  match string_dec s t with
  | left _ => true
  | right _ => false
  end.

Goal "ABC" = "ABC".
destruct (@string_dec_qed "ABC" "ABC").
Admitted.

Lemma transparent_proof_qed : 1 + 2 = 3.
Proof.
  apply/eqP.
  apply: eq_refl.
  Show Proof.
Qed.
Print transparent_proof_qed.                (* = eq_refl. *)
(* transparent_proof_qed = [eta eqP] (eqxx (T:=nat_eqType) (1 + 2)) *)

Lemma transparent_proof_defined : 1 + 2 = 3.
Proof.
  apply/eqP.
  apply: eq_refl.
  Show Proof.
Defined.
Print transparent_proof_defined.            (* = eq_refl. *)
(* transparent_proof_defined = [eta eqP] (eqxx (T:=nat_eqType) (1 + 2)) *)


Definition f_qed : nat.
  refine (1 + 2).



Definition transparent_proof_def : 1 + 2 = 3 := eq_refl.
Print transparent_proof_def.                (* = eq_refl. *)

Definition pred_strong4 : forall (n : nat), n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n with
      | O => fun _ => False_rec _ _
      | S n' => fun _ => exist _ n' _
    end).
Defined.
Print pred_strong4.
