(**
- Coq/SSReflectでperm_eqが不変条件であるような命題を証明するための帰納原理

https://qiita.com/nekonibox/items/233d23bf0fb7cad79e01
 *)

From mathcomp Require Import all_ssreflect.

Lemma ubnP m : {n | m < n}.     (* 最新の ssrnat.v で導入された。 *)
Proof. by exists m.+1. Qed.

(**
# perm_eq
*)
(**
## perm_eq (in seq.v)

perm_eq は seq.v で定義されている。
*)
Check @perm_eq : forall T : eqType, seq T -> seq T -> bool.
Compute perm_eq [:: 1; 2; 3] [:: 2; 1; 3].  (* true *)

(**
## perm_eq についての帰納法
*)

Lemma perm_ind (T : eqType) (P : seq T -> seq T -> Prop) :
  P [::] [::] ->
  (forall u s t, P s u -> P u t -> P s t) ->
  (forall a s t, P s t -> P (a :: s) (a :: t)) ->
  (forall a b s t, P [:: a, b & s] t -> P [:: b, a & s] t) ->
  forall s t, perm_eq s t -> P s t.
Proof.
    move=> Hnil Htrans Hcons Hcons2 s.
    have [n] := ubnP (size s).
    elim: n s => [|n IHn][|a s] //=.
    Check permP.
    - by move=> _ [|b t] // /permP /(_ predT).
    - rewrite ltnS => Hs [/permP /(_ predT)|b t] // Hperm.
      move: (perm_mem Hperm b) (Hperm).
      rewrite !in_cons eq_refl => /= /orP[/eqP -> | Hb _].
      + rewrite perm_cons => /(IHn _ Hs). exact: Hcons.
      + apply: Htrans (Hcons a _ _ (IHn _ Hs _ (perm_to_rem Hb))) _.
        apply: Hcons2 (Hcons _ _ _ (IHn _ _ _ _)) => /=.
        * rewrite size_rem //.
            by case : s Hs Hb {Hperm}.
        * rewrite -(perm_cons b).
          apply: perm_trans Hperm.
          apply: (perm_trans (y := [:: a, b & rem b s])).
          ** apply/permP => g /=.
               by rewrite addnCA.
          ** rewrite perm_cons perm_sym.
             exact: perm_to_rem.
Qed.

Lemma perm_eq_ind (T : eqType) (S : Type) (f : seq T -> S) :
  (forall a s t, f s = f t -> f (a :: s) = f (a :: t)) ->
  (forall a b s, f [:: a, b & s] = f [:: b, a & s]) ->
  forall s t, perm_eq s t -> f s = f t.
Proof.
  move=> Hcons Hcons2.
    by apply: perm_ind => [| u s t -> -> || a b s t <-].
Qed.

(**
## 応用例
*)
Lemma foldr_addn_perm s t :
  perm_eq s t -> foldr addn 0 s = foldr addn 0 t.
Proof.
  move: s t.
  apply: perm_eq_ind => [a s t /= -> | a b s] //=.
    by rewrite addnCA.
Qed.

(**
## 補足説明
*)
Check @permP : forall (T : eqType) (s1 s2 : seq T),
    reflect (count^~ s1 =1 count^~ s2) (perm_eq s1 s2).

(**
# perm 型

perm型とはordinal型の仲間で、
perm_finType が定義されているが、
リストの perm_eq とは直接関係ない。

see. csm_6_2_x_permutation.v
*)
From mathcomp Require Import all_fingroup.

(*
permP の定義が重複している。
*)
Check permP : forall (T : finType) (s t : {perm T}), s =1 t <-> s = t.

(*
リスト(tuple)の perm_eq とのリフレクションの補題がひとつある。
*)
Check @tuple_permP : forall (T : eqType) (n : nat) (s : seq T) (t : n.-tuple T),
    reflect (exists p : 'S_n, s = [tuple tnth t (p i)  | i < n]) (perm_eq s t).

(* END *)
