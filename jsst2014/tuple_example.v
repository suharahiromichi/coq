(* Standard Coq *)
(* 扱いにくい, リストに既にある定義や補題等の再開発が必要 *)

Inductive vec (A : Set) : nat -> Set :=
| vnil : vec A 0
| vcons : A -> forall n : nat, vec A n -> vec A (S n).

Require Import List.

(* コンストラクタ vnilとvcons で組み上げてみる。  *)
Definition a : vec (list nat) 0 := vnil (list nat).
Definition b : vec (list nat) 1 := vcons (list nat) (1::nil) 0 a.
Definition c : vec (list nat) 2 := vcons (list nat) (1::2::nil) 1 b.

Section Vapp.
  
  Variable A : Set.
  
  Fixpoint vapp n (vn : vec A n) m (vm : vec A m) : vec A (n + m) :=
    match vn with
      | vnil => vm
      | vcons hd _ vn' => vcons _ hd _ (vapp _ vn' _ vm)
    end.
  
  Lemma vapp_nil n (vn : vec A n) : 
    vapp _ vn _ (@vnil A) = eq_rect _ _ vn _ (plus_n_O n).
  Proof.
    induction vn.
    simpl.                                  (* n = 0 *)
    Require Import Eqdep.
    rewrite <- eq_rect_eq.
    reflexivity.
    simpl.                                    (* n = S n *)
  Abort.
  
End Vapp.

Compute vapp (list nat) 1 b 2 c.            (* 実際にリストをappendしてはいない。 *)

(* Record を利用して、リストのライブラリを再利用 *)
Record vec2 (A : Set) (n : nat) :=
  (* Vec2 とここに書くと、値コンストラクタの名前になる。
     これは、Class や Structure でも同じである。 *)
  {
    lst : list A ;                          (* 中身 *)
    Hlst : length lst = n                   (* 証明 *)
  }.
Print vec2.
(* 型コンストラクタ :vec2
   値コンストラクタ : Build_vec2、Vec2と指定可能
   ディストラクタ : lst と Hlst
 *)

(* Buildで組み立ててみる。 *)
Check eq_refl.                              (* forall x, x = x *)
Definition a' : vec2 nat 0 := Build_vec2 nat O nil eq_refl.
Definition b' : vec2 nat 1 := Build_vec2 nat 1 (1::nil) eq_refl.
Definition c' : vec2 nat 2 := Build_vec2 nat 2 (1::2::nil) eq_refl.
(* see also. class_record.v *)

Lemma vec2_inj (A : Set) (n : nat) (v1 v2 : vec2 A n) :
  lst A n v1 = lst A n v2 -> v1 = v2.       (* A n は _ _ でもよい。 *)
Proof.
  destruct v1.
  destruct v2.
  simpl.
  intro.
  subst lst1.
  f_equal.
  Require Import ProofIrrelevance.
  apply proof_irrelevance.
Qed.

Require Import List.

Section Vapp2.
  
  Variable A : Set.
  
  Definition vapp2 n (vn : vec2 A n) m (vm : vec2 A m) : vec2 A (n + m).
    apply Build_vec2 with (app (lst _ _ vn) (lst _ _ vm)).
    rewrite app_length.
    rewrite (Hlst _ _ vn).
    rewrite (Hlst _ _ vm).
    reflexivity.
  Defined.
  
  Lemma vapp2_nil n (vn : vec2 A n) : 
    vapp2 _ vn _ (Build_vec2 A O nil eq_refl) = eq_rect _ _ vn _ (plus_n_O n).
  Proof.
    apply vec2_inj.
    simpl.
    rewrite <- app_nil_end.
    rewrite <- plus_n_O.
    simpl.
    reflexivity.
  Qed.
  
End Vapp2.



(* SSReflect では, リストのライブラリを再利用 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

Module TupleExample.
  
  Structure tuple_of (n : nat) (T : Type) : Type := 
    Tuple {
        tval :> seq T;                      (* :> でなくても同じ？ *)
        Hval : size tval == n
      }. 
  
  Print tuple_of.                           (* tuple_of と Tuple *)
  Check isT.                                (* true *)
  
  Definition emp := Tuple O nat [::] isT       : tuple_of 0 nat. (* a'' *)
  Definition one1 := Tuple 1 nat [:: 1] isT    : tuple_of 1 nat. (* b'' *)
  Definition two2 := Tuple 2 nat [:: 1; 2] isT : tuple_of 2 nat. (* c'' *)
  Print two2.
  Definition one2 := Tuple 1 nat [:: 2] isT    : tuple_of 1 nat.


  Goal one1 = one2.
  rewrite /one1 /one2.
  Fail apply val_inj.
  Abort.
  
  Fail Check (val one1).
  
  Canonical tuple_subType (n : nat) (T : Type) := [subType for (@tval n T)].
  
  Check (val one1).
  Check (@val _ _ _ (* (@tuple_subType 1 nat)*) one1).
  
  Goal one1 = one2.
  rewrite /one1 /one2.
  apply val_inj => /=.
  Abort.
  
  Fail Check (one1 == one2).
  
  Fail Check (@eq_op _ one1 one2).
  
  Definition tuple_eqMixin (n : nat) (T : eqType) :=
    [eqMixin of (@tuple_of n T) by <:]. 
  
  Canonical tuple_eqType n (T : eqType) :=
    EqType (tuple_of n T) (tuple_eqMixin n T).
  
  Check (@eq_op _ (*(tuple_eqType 1 nat_eqType)*) one1 one2).
  
  Check (one1 == one2).
  
  Fail Check (emp == one1).
  
End TupleExample.

(* 出来合いのtupleを使う。 *)
Require Import tuple.

Check 0.-tuple nat.                         (* tuple_of 型コンストラクタ *)
Check [tuple].                              (* Tuple 値コンストラクタ *)
Definition a''' := [tuple] : 0.-tuple nat.
Definition b''' := [tuple of [:: 1]] : 1.-tuple nat.
Definition c''' := [tuple of [:: 1; 2]] : 2.-tuple nat.

Check [tuple of [:: 1; 2; 3]].
Check [seq x * 2 | x <- [:: 1; 2; 3]].
Check [tuple of [seq x * 2 | x <- [:: 1; 2; 3]]].

(* 証明での扱いかた。 *)
Goal forall a : 1.-tuple nat, True.
Proof.
  case=> v H.                               (* 値と証明に分解できる。 *)
(* 
  v : seq nat
  H : size v == 1
  ============================
  True.
 *)
  done.
Qed.  

(* END *)

