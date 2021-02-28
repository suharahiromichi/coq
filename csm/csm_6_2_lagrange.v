(**
Coq/SSReflect/MathComp による定理証明

6.2 テーマ2 有限群とラグランジュの定理
======
2018_05_02 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Section Lagrange.

(**
# 6.2.1 有限群の定義 (see. fingroup.v)

finType型クラスのインスタンス型 T を台とする。
・二項演算 mul T -> T -> T が存在する。
・元 one : T が存在する。
・関数 inv : T -> T が存在する。
・mul は結合律を満たす。
・one は左単位元である。
・inv は対合である（2回適用するともとにもどる）。inv (inv x) = x
・inv と mul はモルフィズムを満たす。inv (mul x y) = mul (inv y) (inv x)
 *)

  Open Scope group_scope.
  
  (* gT は finGroupType（有限群）型クラスの型インスタンスである。 *)
  Variable gT : finGroupType.
  
  Variable G H K : {group gT}.              (* G, H, K は有限群型の変数の *)
  
  Goal 1 \in G. by rewrite group1. Qed.
  Goal 1 * G = G. by rewrite mul1g. Qed.
  Goal G * H * K = G * (H * K). by rewrite mulgA. Qed.
  Goal H^-1^-1 = H. by rewrite invgK. Qed.
  Goal (G * H)^-1 = H^-1 * G^-1. by rewrite invMg. Qed.
  
  (**
# 6.2.2 部分群の性質
*)
(**
## 部分群
*)
  Hypothesis HG : H \subset G.

(**
## 同値関係

bool型の二項関係を定義します。
*)  
  Definition R := [rel x y | x * y^-1 \in H].
  Check R : gT -> gT -> bool.               (* simpl_rel gT. *)
  
  Check groupM : forall (gT : finGroupType) (G : {group gT}) (x y : gT),
      x \in G -> y \in G -> x * y \in G.
  Check groupVr : forall (gT : finGroupType) (G : {group gT}) (x : gT),
       x \in G -> x^-1 \in G.
  
(**
同値関係であることを証明する。

equivalence_rel は ssrbool で定義されている。
*)
(**
   fun (T : Type) (R : rel T) => forall x y z : T, R z z * (R x y -> R x z = R y z)
*)
  Set Printing All.
  Print equivalence_rel.
  (*
    fun (T : Type) (R : rel T) =>
    forall x y z : T,
    prod (is_true (R z z)) (forall _ : is_true (R x y), @eq bool (R x z) (R y z))
   *)
  Unset Printing All.
  
  Lemma equiv_rel_R : equivalence_rel R.
  Proof.
    rewrite /equivalence_rel => x y z.
    (* R z z * (R x y -> R x z = R y z) *)
(**
左辺の * は直積(prod)の意味であるので、pair を適用することで、
* の左と右のふたつのゴールに分けられる。
and は Prod型のふたつの直積に対して、prod は Type型のふたつの直積である。ここではおなじこと。
 *)
    apply: pair => /=.
    (* z * z^-1 \in H *)
    - by rewrite mulgV group1.
    (* x * y^-1 \in H -> (x * z^-1 \in H) = (y * z^-1 \in H) *)
    - move=> xRinvy.
      apply/idP/idP.
      + move/groupVr in xRinvy.
        (* [x in H -> y in H -> x * y in H] の [x in H] を指定する必要がある。 *)
        (* 直前の行とまとめて [move/(groupM (groupVr xRinvy))] とできる。 *)
        Check groupM xRinvy.
        move/(groupM xRinvy).
          by rewrite invMg invgK mulgA -(mulgA y) mulVg mulg1.
      + Check (groupM xRinvy).
        move/(groupM xRinvy).
          by rewrite mulgA -(mulgA x) mulVg mulg1.
  Qed.
  
(**
# 6.2.3 剰余類の性質の形式化
*)
(**
## 定理：どの剰余類(A)の濃度も、Hの濃度に等しい

rcosets は fingroup で定義されている。

右剰余類全体からなる集合族の任意の要素(A)、すなわち、どの剰余類(A)の濃度も、
Hの濃度に等しい
 *)
  Lemma myCard_rcoset (A : {set gT}) : A \in rcosets H G -> #|A| = #|H|.
  Proof.
    Check rcosetsP.
    case/rcosetsP => a ainG ->.
      by apply: card_rcoset.
  Qed.
  
(**
## 定理： H x = {y ∈ G | xRy}
*)
  Lemma coset_equiv_class (x : gT) (xinG : x \in G) : H :* x = [set y in G | R x y].
  Proof.
    apply/setP => /= y.
    rewrite inE.
    apply/idP/idP.
    - case/rcosetP => z zinH -> {y}.
      apply/andP.
      apply: conj.
      + Check groupM.
        rewrite groupM //.
        move/subsetP : HG => HG'.
        Check (HG' z zinH).
          by move: (HG' z zinH).
      + by rewrite invMg mulgA mulgV mul1g groupV.
    - case/andP => yinG xinvyinH.
      apply/rcosetP.
      (* プレースホルダーを埋めると次になる。 *)
      Check (ex_intro2 (fun g => g \in H)
                       (fun a => y = a * x)
                       (y * x^-1)) :
        y * x^-1 \in H -> y = y * x^-1 * x ->
                     ex2 (fun g : gT => g \in H) (fun a : gT => y = a * x).
      (* ゴールは、 exists2 a : gT, a \in H & y = a * x のデシュガ *)
      apply: (ex_intro2 _ _ (y * x^-1)).
      + by rewrite -groupV invMg invgK.
      + by rewrite -mulgA mulVg mulg1.
  Qed.
  
(**
## 補題：右剰余類全体からなる集合族は、同値関係で分割して得られた集合族に等しい。

equivalence_partition は finset で定義されている。
*)
  Lemma rcosets_equiv_part : rcosets H G = equivalence_partition R G.
  Proof.
    apply/setP => /= X.
    rewrite /rcosets /equivalence_partition.
    apply/idP/idP.
    - case/rcosetsP => x0 x0inG X_Hx.
      apply/imsetP.
      apply: (ex_intro2 _ _ x0).
      + done.
      + Check @coset_equiv_class x0.
          by rewrite -coset_equiv_class.
    - case/imsetP => x1 xinG Hypo.
      apply/imsetP.
      (* プレースホルダーを埋めると次になる。 *)
      Check (ex_intro2 (fun g => g \in G)
                       (fun x => X = rcoset H x)
                       x1) :
        x1 \in G ->
               X = rcoset H x1 ->
               exists2 x : gT, x \in G & X = rcoset H x.
      apply: (ex_intro2 _ _ x1).
      + done.
      + rewrite rcosetE.
        by rewrite coset_equiv_class.
  Qed.
  
(**
## 補題：右剰余類全体からなる集合族は、もとの集合の分割になっている。

partition は finset で定義されている。
*)
  Lemma partition_rcosets : partition (rcosets H G) G.
  Proof.
    rewrite rcosets_equiv_part.
    apply/equivalence_partitionP => x y z xinG yinG zinG.
      by apply : equiv_rel_R.
  Qed.

(**
# 6.2.4 ラグランジュの定理
*)
  Section TEST.
    Variable f : nat -> nat.
    Print iter.
    Compute iter 10 f 0. (* = f (f (f (f (f (f (f (f (f (f 0))))))))) *)
  End TEST.
  
  (* |G| = |H| (G : H) *)
  Theorem myLagrange : #|G| = (#|H| * #|G : H|)%nat.
  Proof.
    Check card_partition partition_rcosets.
    rewrite (card_partition partition_rcosets). (* 右剰余類による分割を与える。 *)
    Check  ((eq_bigr (fun _ => #|H|)) myCard_rcoset).
    rewrite ((eq_bigr (fun _ => #|H|)) myCard_rcoset). (* 剰余類の濃度が#|H|に一致する。 *)
    Check big_const 0 addn.
    rewrite big_const.                      (* iter に展開する。 *)
    (* 0 に対して、f = addn #|H| を n = #|rcosets H G| 回繰り返し適用する。 *)
    Check iter_addn_0.
    (* 0 に対して addn m を n 回繰り返すのは、m * n である。 *)
    rewrite iter_addn_0.
    done.
  Qed.
  
  (* (G : H) は、HによるGの右剰余類の個数であり、mathcomp の表記だと #|G : H| である。 *)
  (* 剰余類(G : H) の個数(#| |) といういう意味ではないことに注意すること。 *)
  (* 剰余類(rcosets H G) の 個数(#|_|) なら、 #|rcosets H G| = #|G : H| である。 *)
End Lagrange.

(* END *)
