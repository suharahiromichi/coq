(**
Coq/SSReflect/MathComp による定理証明

7.2 確率論 - 分布、期待値、分散
======
infotheo/toy_examples/expected_value_variance.v
 *)

From mathcomp Require Import all_ssreflect.
Require Import Reals Lra.
From infotheo Require Import ssrR Reals_ext Rbigop proba.

(* Coq/SSReflect/MathComp, Morikita, Sect. 7.2 *)

(**
分布は、

(1). 有限集合上の関数である。

(2). 関数の像は非負実数である。

(3). 像の和は1.0である。

コードのコメントに (1) (2) (3) で記載した。
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope reals_ext_scope.
Local Open Scope R_scope.          (* 実数スコープ。coq/Reals で定義。 *)

(**
# (1) 分布は、有限集合上の関数である。

内側の ``[fun x => e0 with a1 |-> e1, ...]`` は eqTypeで定義されている。
e0 は others の意味である。
 *)
Definition f : {ffun 'I_3 -> R} :=          (* {0, 1, 2} 上の確率分布 *)
  [ffun i =>
   [fun x => 0 with inord 0 |-> 1/2,        (* P(0) = 1/2 *)
                    inord 1 |-> 1/3,        (* P(1) = 1/3 *)
                    inord 2 |-> 1/6]        (* P(2) = 1/6 *)
     i].

(* Inductive にしても同じ。 *)
CoInductive I3_spec : 'I_3 -> bool -> bool -> bool -> Prop :=
| I2_0 : I3_spec (inord 0) true false false
| I2_1 : I3_spec (inord 1) false true false
| I2_2 : I3_spec (inord 2) false false true.

Ltac I3_neq := rewrite (_ : _ == _ = false); last by
              apply/negbTE/negP => /eqP/(congr1 (@nat_of_ord 3));
              rewrite !inordK.

(**
確率変数 i が、0, 1, 2 を分布する。
*)

(**
mapP は、``i ∈ map f l`` を ``∃x.x∈l /\ i = f x`` にする命題です。

また、map の構文糖衣も思い出してください。
 *)
Check @mapP : forall (T1 T2 : eqType) (f : T1 -> T2) (s : seq T1) (y : T2),
    reflect (exists2 x : T1, x \in s & y = f x) (y \in [seq f i | i <- s]).

Lemma I3P (i : 'I_3) : I3_spec i
                               (i == inord 0) (i == inord 1) (i == inord 2).
Proof.
(**
ローカルな補題 ``i ∈ map inord [:: 0; 1; 2]`` を証明する。
have の次に変数がないので、証明ができた時点で、ゴールのスタックにつまれます。
*)
  have : i \in map inord (iota 0 3). (* i \in [seq inord i | i <- iota 0 3] *)
  - apply/mapP.
    exists (nat_of_ord i).
    + by rewrite mem_iota leq0n add0n ltn_ord. (* i ∈ [:: 0; 1; 2] の証明 *)
    + by rewrite inord_val.      (* i = inord (nat_of_ord i) の証明 *)
  - rewrite inE => /orP [/eqP -> |].
(**
I3_spec (inord 0) (inord 0 == inord 0) (inord 0 == inord 1) (inord 0 == inord 2)
*)
    Check eqxx : forall (T : eqType) (x : T), (x == x). (* = true はコアーション *)
    Check eqxx : forall (T : eqType) (x : T), (x == x) = true.
    + rewrite eqxx.      (* ``inord 0 == inord 0`` を true にする。 *)
      do 2 I3_neq.       (* ``inord 0 == inord 1`` を false にする。 *)
      exact: I2_0.       (* I3_spec のコンストラクタ *)
      
    + rewrite inE => /orP[/eqP ->|].
(**
I3_spec (inord 1) (inord 1 == inord 0) (inord 1 == inord 1) (inord 1 == inord 2)
*)
      * rewrite eqxx.
        I3_neq.
        I3_neq.
        exact: I2_1.
      * rewrite inE => /eqP ->.
(**
I3_spec (inord 2) (inord 2 == inord 0) (inord 2 == inord 1) (inord 2 == inord 2)
*)
        rewrite eqxx.
        I3_neq.
        I3_neq.
        exact: I2_2.
Qed.

(**
# (2) 関数の像は非負実数である。

演算子 ``<b=`` は infotheo.lib.ssrR.leRb で定義されている。不等号である。
 *)
Check infotheo.lib.ssrR.leRb : R -> R -> bool.

(**
ffunE は、finfun に対して ``(λx.g(x))(x) = g(x)`` の書き換えをおこなう。
 *)
  Check ffunE
    : forall (aT : finType) (rT : aT -> Type) (g : forall x : aT, rT x) (x : aT),
      [ ffun x : _ => g x] x = g x.
(**
ifT は、if-then-else の then 節を取り出す。
 *)
  Check ifT : forall (A : Type) (b : bool) (vT vF : A),
      b -> (if b then vT else vF) = vT.
(**
ifF は、if-then-else の else 節を取り出す。
*)
  Check ifF : forall (A : Type) (b : bool) (vT vF : A),
      b = false -> (if b then vT else vF) = vF.
  
Lemma f_nonneg : [forall a : 'I_3, 0 <b= f a].
Proof.
  Check forallP_leRP
  : forall (A : finType) (f : A -> R),
    reflect (forall a : A, 0 <= f a) [forall a, 0 <b= f a].
  apply/forallP_leRP.                       (* Prep に変換する。 *)
  case/I3P.
  - rewrite /f ffunE /= eqxx.
    lra.                                    (* 0 <= 1 / 2 *)
    
  - rewrite /f ffunE /= ifF; last by I3_neq.
    rewrite eqxx.
    lra.                                    (* 0 <= 1 / 3 *)
    
  - rewrite /f ffunE /= ifF; last by I3_neq.
    rewrite ifF; last by I3_neq.
    rewrite eqxx.
    lra.                                    (* 0 <= 1 / 6 *)
Qed.

(**
(1)(2)
 *)
Definition pmf : [finType of 'I_3] ->R+ := mkPosFfun f_nonneg.

Ltac I3_eq := rewrite (_ : _ == _ = true); last by
                  apply/eqP/val_inj => /=; rewrite inordK.

(**
# (3) 像の和は1.0である。

``_ == _ :> R`` は R型 (real ?) での比較 を意味する。
 *)
Lemma pmf1 : \sum_(i in 'I_3) pmf i == 1 :> R.
Proof.
  apply/eqP.
  do 3 rewrite big_ord_recl.
  rewrite big_ord0 addR0 /=.
  rewrite /f !ffunE /= ifT; last by I3_eq. (* ord0 == inord 0 を true に簡約する。 *)
  rewrite ifF; last by I3_neq. (* lift ord0 ord0 == inord 0 を false に簡約する。 *)
  rewrite ifT; last by I3_eq.  (* lift ord0 ord0 == inord 1 を true に簡約する。 *)
  rewrite ifF; last by I3_neq. (* lift ord0 (lift ord0 ord0) == inord 0 を false *)
  rewrite ifF; last by I3_neq. (* lift ord0 (lift ord0 ord0) == inord 1 を false *)
  rewrite ifT; last by I3_eq.  (* lift ord0 (lift ord0 ord0) == inord 2 を treu *)
    (* goal : 1 / 2 + (1 / 3 + 1 / 6) = 1 *)
    by field.
Qed.
Check ifT.            (* if true then vT else vF を vT に簡約する。 *)
Check ifF.            (* if false then vT else vF を vF に簡約する。 *)

Local Open Scope proba_scope.

(**
# 分布 d の定義
 *)
Definition d : {fdist 'I_3} := FDist.mk pmf1.

(**
確率変数 X を d に従う確率分布とする。
 *)
Definition X : {RV d -> R} := (fun i => INR i.+1). (* x |-> x+1  *)

(**
# 期待値の計算例

E(X) = 1・(1/2) + 2・(1/3) + 3・(1/6) = 10/6 = 5/3
*)
Lemma expected : `E X = 5/3.
Proof.
  rewrite /Ex /p_of.
  do 3 rewrite big_ord_recl.
  rewrite big_ord0 addR0.
  rewrite /p_of /= /X mul1R.
  rewrite /f !ffunE /= ifT; last by I3_eq.
  rewrite (_ : INR _ = 2) //.
  rewrite /= ifF; last by I3_neq.
  rewrite ifT; last by I3_eq.
  rewrite (_ : INR _ = 3); last first.
  - rewrite S_INR (_ : INR _ = 2) //.
      (* goal : 2 + 1 = 3 *)
      by field.
  - rewrite /f /= ifF; last by I3_neq.
    rewrite ifF; last by I3_neq.
    rewrite ifT; last by I3_eq.
      (* goal : 1 / 2 + (2 * (1 / 3) + 3 * (1 / 6)) = 5 / 3 *)
      by field.
Qed.

(**
# 分散の計算例

E(X^2) = 1^2・(1/2) + 2^2・(1/3) + 3^2・(1/6) = 10/3

σ^2 = E(X^2) - (E(X))^2 = 10/3 - (5/3)^2 = 5/9
*)
Lemma variance : `V X = 5/9.
Proof.
  rewrite VarE.                             (*  /Ex /p_of. *)
  rewrite expected.
  rewrite /Ex /X.
  do 3 rewrite big_ord_recl.
  rewrite big_ord0 addR0 /=.
  rewrite /sq_RV /comp_RV /=.
  rewrite !mul1R.
  rewrite {1}/f !ffunE /=.
  rewrite ifT; last by I3_eq.
  rewrite (_ : INR _ = 2) // mulR1.
  rewrite /f /=.
  rewrite ifF; last by I3_neq.
  rewrite ifT; last by I3_eq.
  rewrite (_ : INR _ = 3); last first.
  - rewrite S_INR (_ : INR _ = 2) //.
      (* goal : 2 + 1 = 3 *)
      by field.
  - rewrite ifF; last by I3_neq.
    rewrite ifF; last by I3_neq.
    rewrite ifT; last by I3_eq.
    (* 1 / 2 + (2 * 2 * (1 / 3) + 3 * (3 * 1) * (1 / 6)) - 5 / 3 * (5 / 3 * 1) = 5 / 9 *)
      by field.
Qed.

(* END *)
