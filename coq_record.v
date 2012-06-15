(*
   Coq Record
   2010_10_21
*)


(****************************************)
(* Inductive を使うコンストラクタの定義 *)
(****************************************)


Inductive zero : Set :=                     (* 0要素 *)
| Zero : zero.
Check zero.                                 (* Set *)
Check zero_rec.
Definition zero0 : zero -> nat :=
  zero_rec (fun z:zero => nat)
  0.
Eval cbv in zero0 (Zero).                   (* 0 *)


Inductive one : Set :=                      (* 1要素 *)
| One : nat -> one.
Check one.                                  (* Set *)
Check one_rec.
Definition one1 : one -> nat :=
  one_rec (fun o:one => nat)
  (fun n:nat => n).
Eval cbv in one1 (One 1).                   (* 1 *)


Inductive two : Set :=                      (* 2要素 *)
| Two : nat -> nat -> two.
Check two.                                  (* Set *)
Check two_rec.
Definition two1 : two -> nat :=             (* 第一要素 *)
  two_rec (fun t:two => nat)
  (fun n m:nat => n).
Eval cbv in two1 (Two 1 2).                 (* 1 *)
Definition two2 : two -> nat :=             (* 第二要素 *)
  two_rec (fun t:two => nat)
  (fun n m:nat => m).
Eval cbv in two2 (Two 1 2).                 (* 2 *)




Inductive o12 : Set :=
| Zero' : o12
| One' : nat -> o12
| Two' : nat -> nat -> o12.


Check o12.                                  (* Set *)
Check o12_rec.


Definition o12012 : o12 -> nat :=
  o12_rec (fun o:o12 => nat)
  0
  (fun n:nat => n)
  (fun n m:nat => m).                       (* 第二要素 *)


Eval cbv in o12012 (Zero').                 (* 0 *)
Eval cbv in o12012 (One' 1).                (* 1 *)
Eval cbv in o12012 (Two' 1 2).              (* 2 *)


Definition o12011 : o12 -> nat :=
  o12_rec (fun o:o12 => nat)
  0
  (fun n:nat => n)
  (fun n m:nat => n).                       (* 第一要素 *)


Eval cbv in o12011 (Zero').                 (* 0 *)
Eval cbv in o12011 (One' 1).                (* 1 *)
Eval cbv in o12011 (Two' 1 2).              (* 1 *)




(*******************************)
(* Record を使うコンストラクタ *)
(*******************************)


Record pair : Set :=
  mkpair {first : nat; second : bool}.


Check pair.                                 (* Set *)
Check mkpair.                               (* nat -> bool -> pair *)
Check mkpair 1 true.                        (* pair *)


(* セレクタは要素名を使えばよい *)
Eval cbv in first (mkpair 1 true).          (* 1 *)
Eval cbv in second (mkpair 1 true).         (* true *)


Check pair_rec.


Definition fst : pair -> nat :=
  pair_rec (fun p:pair => nat)
  (fun n:nat => (fun b:bool => n)).
Definition snd : pair -> bool :=
  pair_rec (fun p:pair => bool)
  (fun n:nat => (fun b:bool => b)).


(* 型の宣言は省略できる。 *)
Definition fst' : pair -> nat :=
  pair_rec (fun p => nat)
  (fun n b => n).
Definition snd' : pair -> bool :=
  pair_rec (fun p => bool)
  (fun n b => b).


Eval cbv in fst (mkpair 1 true).            (* 1 *)
Eval cbv in snd (mkpair 1 true).            (* true *)


(* END *)