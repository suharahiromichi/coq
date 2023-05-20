(**
MathComp1 整数の定義

http://www-sop.inria.fr/teams/marelle/advanced-coq-17/lesson5.v
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require all_algebra.          (* 使うところは個別に Import する必要がある。 *)
Require Import Psatz.                       (* lia *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ssralg.
Import GRing.Theory.
Local Open Scope ring_scope.

(**
# 整数 int
*)
Module InstantiationInteger.
  
(* 自然数から整数を作るコンストラクタ Posz と Negz を定義する。
   Posz は自然数から整数へのコアーションにするとともに、``%:Z``という演算子を用意しておく。*)
  CoInductive int : Set :=
  | Posz of nat
  | Negz of nat.
  Local Coercion Posz : nat >-> int.
  Notation "n %:Z" := (Posz n)(at level 2, left associativity, format "n %:Z", only parsing).

  Definition natsum_of_int (m : int) : nat + nat :=
    match m with
    | Posz p => inl _ p
    | Negz n => inr _ n
    end.
  
  Definition int_of_natsum (m : nat + nat) : int :=
    match m with
    | inl p => Posz p
    | inr n => Negz n
    end.

  Lemma natsum_of_intK : cancel natsum_of_int int_of_natsum. (* (1) *)
  Proof. by case. Qed.

  Definition int_eqMixin := CanEqMixin natsum_of_intK. (* MathComp1 *)
  Canonical int_eqType := EqType int int_eqMixin.      (* MathComp1 *)
  
  Definition int_choiceMixin := CanChoiceMixin natsum_of_intK. (* MathComp1 *)
  Canonical int_choiceType := ChoiceType int int_choiceMixin. (* MathComp1 *)
  
  Definition int_countMixin := CanCountMixin natsum_of_intK. (* MathComp1 *)
  Canonical int_countType := CountType int int_countMixin. (* MathComp1 *)

(**
## Z加群     
*)
  Module intZmod.
    Section intZmod.

      Print ZmodMixin.
      Print GRing.Zmodule.Mixin.
(**
Record mixin_of (V : Type) : Type := Mixin
  { zero : V;
    opp : V -> V;
    add : V -> V -> V;
    _ : associative add;
    _ : commutative add;
    _ : left_id zero add;
    _ : left_inverse zero opp add }.

Arguments GRing.Zmodule.mixin_of V%type_scope
Arguments GRing.Zmodule.Mixin [V]%type_scope [zero] [opp add]%function_scope _ _ _ _
*)      

      (* Negz 0 で -1 を表すようにする。すると、intの表現の一意性が保たれる。 *)
      Check Posz 1.                         (* +1 *)
      Check Posz 0.                         (* 0 *)
      Check Negz 0.                         (* -1 *)
      Check Negz 1.                         (* -2 *)
      (* この定義に基づいて、整数の加算を定義すると、以下 addz と oppz のようになる。 *)
      
      Definition addz (m n : int) :=
        match m, n with
        | Posz m', Posz n' => Posz (m' + n')
        | Negz m', Negz n' => Negz (m' + n').+1
        | Posz m', Negz n' => if n' < m' then Posz (m' - n'.+1)
                              else Negz (n' - m')
        | Negz n', Posz m' => if n' < m' then Posz (m' - n'.+1)
                              else Negz (n' - m')
        end.
      
      Definition oppz m := nosimpl
                             match m with
                             | Posz n => if n is (n'.+1)%N then Negz n' else Posz 0
                             | Negz n => Posz (n.+1)%N
                             end.

      Lemma addzC : commutative addz.
      Proof.
        rewrite /commutative.
        move=> [m [n | n] | m [n | n]].
        - by rewrite /= addnC.
        - by rewrite /=.
        - by rewrite /=.
        - by rewrite /= addnC.
      Qed.
      
      Lemma add0z : left_id (Posz 0) addz.
      Proof.
        rewrite /left_id.
        move=> [[| n] | [| n]].
        - by rewrite /=.
        - by rewrite /=.
        - by rewrite /=.
        - by rewrite /=.
      Qed.

      Lemma oppzK : involutive oppz.
      Proof.
        rewrite /involutive /cancel.
        move=> [[| n] | [| n]].
        - by rewrite /=.
        - by rewrite /=.
        - by rewrite /=.
        - by rewrite /=.
      Qed.


      Lemma PoszD (m n : nat) : (m + n)%:Z = addz m%:Z n%:Z.
      Proof.
        done.
      Qed.
      
      Lemma addSz (m n : int) : addz (addz 1%:Z m) n = addz 1%:Z (addz m n).
      Proof.
        move: m n => [m [n | n]| m [n | n]].
        - by rewrite /= addnA.
        - rewrite [addz 1%:Z m%:Z]/=.
      Admitted.
      
      Lemma oppz_add (m n : int) : oppz (addz m n) = addz (oppz m) (oppz n).
      Proof.
      Admitted.
      
      Lemma addPz (m n : int) : addz (addz m (oppz 1%:Z)) n = addz (addz m n) (oppz 1%:Z).
      Proof.
      Admitted.
      
      Lemma NegzE : forall n : nat, Negz n = oppz n.+1.
      Proof.
        done.
      Qed.
      
      Lemma int_ind (P : int -> Type) :
        P 0%:Z ->
        (forall n : nat, P n -> P n.+1) ->
        (forall n : nat, P (oppz n) -> P (oppz n.+1)) ->
        forall n : int, P n.
      Proof.
        by move=> P0 hPp hPn []; elim=> [|n ihn]; do ?[apply: hPn | apply: hPp].
      Qed.
      
      Lemma addzA : associative addz.
      Proof.
        rewrite /associative.
        elim=> [| m IHm | m IHm] n p; first by rewrite !add0z.
        - by rewrite -add1n PoszD !addSz IHm.
        - by rewrite -add1n addnC PoszD oppz_add !addPz IHm.
      Qed.
      
      Lemma addNz : left_inverse (Posz 0) oppz addz.
      Proof.
        rewrite /left_inverse.
        elim=> //=.
        elim=> //=.
        elim=> //=.
      Qed.
      
      Definition Mixin := ZmodMixin addzA addzC add0z addNz. (* MathComp1 *)
      
    End intZmod.
  End intZmod.
  
  Canonical int_ZmodType := ZmodType int intZmod.Mixin. (* MathComp1 *)
  Check 1%:Z : int_ZmodType : zmodType.                 (* MathComp1 *)
  Check 1%:Z : int : Type.                              (* MathComp1 *)
  
(**
整数論に特有のアーベル群論の一部を展開することができます。
 *)
  Section intZmoduleTheory.
(**
PoszD は、Posz (正整数) の加算 (D) について、
自然数を  加算して正整数にすることと、自然数を正整数にして加算することは等しい。
 *)
    Lemma PoszD : {morph Posz : n m / (n + m)%N >-> n + m}.
    Proof. by []. Qed.
    Check PoszD : forall x y : nat, Posz (x + y) = Posz x + Posz y.
    Check PoszD : forall x y : nat, (x + y)%:Z = x%:Z + y%:Z.
    
  End intZmoduleTheory.

(**
# 環
*)
  Module intRing.
    Section intRing.
      
      Print RingMixin.
      Print GRing.Ring.Mixin.
(**
Record mixin_of (R : zmodType) : Type := Mixin
  { one : GRing.Zmodule.sort R;
    mul : R -> R -> R;
    _ : associative mul;
    _ : left_id one mul;
    _ : right_id one mul;
    _ : left_distributive mul +%R;
    _ : right_distributive mul +%R;
    _ : is_true (one != 0) }.

Arguments GRing.Ring.mixin_of R
Arguments GRing.Ring.Mixin [R] [one]%ring_scope [mul]%function_scope _ _ _ _ _ _
*)
      
      Definition mulz (m n : int) :=
        match m, n with
        | Posz m', Posz n' => (m' * n')%N%:Z
        | Negz m', Negz n' => (m'.+1%N * n'.+1%N)%N%:Z
        | Posz m', Negz n' => - (m' * (n'.+1%N))%N%:Z
        | Negz n', Posz m' => - (m' * (n'.+1%N))%N%:Z
        end.
      
      Lemma NegzE : forall n : nat, Negz n = intZmod.oppz n.+1.
      Proof.
        done.
      Qed.
      
      Compute -0%:Z.                              (* 0%:Z *)
      Compute -1%:Z.                              (* Negz 0 *)
      Compute -2%:Z.                              (* Negz 1%N *)
      Compute -2%:Z == Negz 1%N.                  (* true *)
      
      Lemma mulz_pn m n : mulz m%:Z (- n%:Z) = - (m * n)%:Z.
      Proof.
        case: n => [| n].
        - by rewrite /= muln0.
        - rewrite -[- n.+1%:Z]NegzE.
          rewrite /mulz.
          done.
      Qed.
      
      Lemma mulz_np m n : mulz (- m%:Z) n%:Z = - (m * n)%:Z.
      Proof.
        case: m => [| m].
        - by rewrite /= mul0n.
        - rewrite -[- m.+1%:Z]NegzE.
          rewrite /mulz.
          rewrite mulnC.
          done.
      Qed.
      
      Lemma mulz_nN m n : mulz (- m%:Z) (Negz n) = (m * n.+1)%:Z.
      Proof.
        case: m => [| m].
        - by rewrite mul0n.
        - rewrite -[- m.+1%:Z]NegzE.
          rewrite /mulz.
          rewrite mulnC.
          done.
      Qed.
      
      Lemma mulz_Nn m n : mulz (Negz m) (- n%:Z) = (m.+1 * n)%:Z.
      Proof.
        case: n => [| n].
        - by rewrite /= muln0.
        - rewrite -[- n.+1%:Z]NegzE.
          rewrite /mulz.
          done.
      Qed.
      
      Lemma mulzA : associative mulz.
      Proof.
        rewrite /associative.
        move=> [] m [] n [] p.
        - rewrite /=.
          (* (m * (n * p))%Z = (m * n * p)%Z *)
          by rewrite mulnA.
        - rewrite mulz_pn.
          (* - (m * (n * p.+1))%Z = - (m * n * p.+1)%Z  *)
          by rewrite mulnA.
        - rewrite mulz_pn mulz_np.
          (* - (m * (n.+1 * p))%Z = - (m * n.+1 * p)%Z *)
          by rewrite mulnCA mulnC.
        - rewrite mulz_nN /=.
          (* (m * (n.+1 * p.+1))%Z = (m * n.+1 * p.+1)%Z *)
          by rewrite mulnA.
        - rewrite mulz_np.
          (* - (m.+1 * (n * p))%Z = - (m.+1 * n * p)%Z *)
          by rewrite mulnAC.
        - rewrite mulz_nN mulz_Nn.
          (* (m.+1 * (n * p.+1))%Z = (m.+1 * n * p.+1)%Z *)
          by rewrite mulnCA mulnA.
        - rewrite mulz_Nn /=.
          (* (m.+1 * (n.+1 * p))%Z = (m.+1 * n.+1 * p)%Z *)
          by rewrite mulnAC mulnA.
        - rewrite /=.
          (* - (m.+1 * (n.+1 * p.+1))%Z = - (m.+1 * n.+1 * p.+1)%Z *)
          by rewrite mulnC mulnA.
      Qed.
      
      Lemma mulzC : commutative mulz.
      Proof.
        rewrite /commutative.
        move=> [m [n | n] | m [n | n]].
        - by rewrite /= mulnC.
        - by rewrite /=.
        - by rewrite /=.
        - by rewrite /= mulnC.
      Qed.  
      
      Lemma PoszM (m n : nat) : (m * n)%:Z = mulz m%:Z n%:Z.
      Proof.
        done.
      Qed.
      
      Lemma mul1z : left_id (Posz 1) mulz.
      Proof.
        rewrite /left_id.
        move=> [[| n] | [| n]].
        - by rewrite /=.
        - by rewrite -PoszM mul1n.
        - by rewrite /=.
        - rewrite /mulz.
          rewrite mul1n.
          rewrite NegzE.
          done.
      Qed.
      
      Lemma mulz_addl : left_distributive mulz (+%R).
      Proof.
        rewrite /left_distributive.
        (* move=> [] m [] n [] p. *)
        move=> x y z.
        apply: (intZmod.int_ind z) => [n | n].    (* elim: z *)
      Admitted.
      
      Lemma onez_neq0 : (Posz 1) != 0. Proof. by []. Qed.
      Definition comMixin := ComRingMixin mulzA mulzC mul1z mulz_addl onez_neq0. (* MathComp1 *)
      
    End intRing.
  End intRing.
  
  Canonical int_Ring := RingType int intRing.comMixin. (* MathComp1 *)
  Canonical int_comRing := ComRingType int intRing.mulzC. (* MathComp1 *)

  Check 1%:R : int_Ring : ringType.         (* MathComp1 *)
  Check 1%:R : int_comRing : comRingType.   (* MathComp1 *)
  Check 1%:R : int : Type.
  
  Check fun x : int => x + x.
  Check @addr0 int_Ring.
  
End InstantiationInteger.

(* END *)
