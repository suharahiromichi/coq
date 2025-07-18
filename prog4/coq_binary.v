From mathcomp Require Import all_ssreflect.
Require Import ZArith Lia.

(**

- ZArith/BinInt.v

- ZArith/Zbitwise.v


*)

(* Import Z. すると、補題の前置のZ.が省略できるが、しないことにする。 *)
Fail Check sub_lor_land.
Check Z.sub_lor_land.

Open Scope Z_scope.

Check 1 : Z.

(* Z_scope は関数に影響しない。 *)
Fail Check add.
Fail Check lxor.
Check Z.add.
Check Z.lxor.

(* ZArith/Zbitwise.v の Local 定義をグローバルにする。 *)
(* level 40 は、「*」と同じ優先順位である。 *)
Notation ".~ x" := (Z.lnot x) (at level 35).
Infix ".|" := Z.lor (at level 40).
Infix ".&" := Z.land (at level 40).
Infix ".^" := Z.lxor (at level 40).
Infix ".-" := Z.ldiff (at level 50).
Infix ".<<" := Z.shiftl (at level 60). 
Infix ".>>" := Z.shiftr (at level 60). 

Infix "^^" := xorb (at level 40).

Search "lxor".                           (* サーチは Z.をつけない。 *)
Search (_ .^ _) "diff".                  (* 演算子でサーチしたほうがよい。 *)


(* testbit *)
(* LSB を 0 とする。上限はない。 *)
Compute Z.testbit 0%Z 0%Z.                  (* 全ビット false *)
Compute Z.testbit 1%Z 0%Z.                  (* true *)
Compute Z.testbit 2%Z 1%Z.                  (* true *)
Compute Z.testbit 4%Z 2%Z.                  (* true *)
Compute Z.testbit (-1)%Z 0%Z.               (* 全ビット true *)
Compute Z.testbit (-2)%Z 0%Z.               (* false *)
Compute Z.testbit (-4)%Z 1%Z.               (* false *)
Compute Z.testbit (-8)%Z 2%Z.               (* false *)

(* _spec 補題 *)
(* n と m も Z である。Z.testbit におけるの負数の指定は false になる。 *)
Check Z.lor_spec    : forall a b n : Z, Z.testbit (a .| b) n = Z.testbit a n || Z.testbit b n.
Check Z.land_spec   : forall a b n : Z, Z.testbit (a .& b) n = Z.testbit a n && Z.testbit b n.
Check Z.lxor_spec   : forall a b n : Z, Z.testbit (a .^ b) n = Z.testbit a n ^^ Z.testbit b n.
Check Z.ldiff_spec  : forall a b n : Z, Z.testbit (a .- b) n = Z.testbit a n && ~~ Z.testbit b n.
Check Z.shiftl_spec : forall a n m : Z, 0 <= m -> Z.testbit (a .<< n) m = Z.testbit a (m - n).
Check Z.shiftr_spec : forall a n m : Z, 0 <= m -> Z.testbit (a .>> n) m = Z.testbit a (m + n).

(* -1 に関する補題。-1 は all 1 *)
Check Z.lor_m1_l    : forall a : Z, - (1) .| a = - (1).
Check Z.lor_m1_r    : forall a : Z, a .| - (1) = - (1).
Check Z.land_m1_l   : forall a : Z, - (1) .& a = a.
Check Z.land_m1_r   : forall a : Z, a .& - (1) = a.
Check Z.lxor_m1_l   : forall a : Z, - (1) .^ a = .~ a.
Check Z.lxor_m1_r   : forall a : Z, a .^ - (1) = .~ a.
Check Z.ldiff_m1_r  : forall a : Z, a .- (- (1)) = 0.
Check Z.ldiff_m1_l  : forall a : Z, (- (1)) .- a = .~ a.

(* 対角線 *)
Check Z.lor_diag         : forall a : Z, a .| a = a.
Check Z.lor_lnot_diag    : forall a : Z, a .| .~ a = - (1).
Check Z.land_diag        : forall a : Z, a .& a = a.
Check Z.land_lnot_diag   : forall a : Z, a .& .~ a = 0.
Check Z.lor_diag         : forall a : Z, a .| a = a.
Check Z.lor_lnot_diag    : forall a : Z, a .| .~ a = - (1).

(* +1 や -1 についての補題 *)
Check Z.lnot_opp         : forall x   : Z, .~ (- x) = x - 1.
Check Z.lnot_eq_pred_opp : forall x   : Z, .~ x = - x - 1.
Check Z.lnot_pred        : forall x   : Z, .~ (x - 1) = - x.
Check Z.add_lnot_r       : forall x y : Z, x + .~ y = x - y - 1.
Check Z.pred_sub_lnot_r  : forall x y : Z, x - .~ y - 1 = x + y.
Check Z.succ_lnot        : forall x   : Z, .~ x + 1 = - x.
Check Z.opp_lnot         : forall x   : Z, - .~ x = x + 1.
Check Z.succ_add_lnot_r  : forall x y : Z, x + .~ y + 1 = x - y.

(* not-xor の分配則 *)
Check Z.lnot_lxor_l: forall a b : Z, .~ (a .^ b) = .~ a .^ b.
Check Z.lnot_lxor_r: forall a b : Z, .~ (a .^ b) = a .^ .~ b.

(* 加算、減算、2倍との関係 *)
Check Z.sub_lor_land     : forall x y : Z, x .| y - x .& y = x .^ y.
Check Z.add_lor_land     : forall x y : Z, x .| y + x .& y = x + y.
Check Z.sub_land_same_l  : forall x y : Z, x - x .& y = x .& .~ y.
Check Z.sub_lor_l_same_r : forall x y : Z, x .| y - y = x .& .~ y.
Check Z.add_nocarry_lxor : forall a b : Z, a .& b = 0 -> a + b = a .^ b.
Check Z.add_lxor_2land   : forall x y : Z, x .^ y + 2 * (x .& y) = x + y.
Check Z.sub_2lor_lxor    : forall x y : Z, 2 * (x .| y) - x .^ y = x + y.
Check Z.sub_landn_rlandn : forall x y : Z, x .& .~ y - .~ x .& y = x - y.
Check Z.sub_lxor_2rlandn : forall x y : Z, x .^ y - 2 * (.~ x .& y) = x - y.
Check Z.sub_2landn_lxor  : forall x y : Z, 2 * (x .& .~ y) - x .^ y = x - y.

(* log2 との関係 *)
Check Z.log2_lor: forall a b : Z, 0 <= a -> 0 <= b -> Z.log2 (a .| b) = Z.max (Z.log2 a) (Z.log2 b).
Check Z.log2_land: forall a b : Z, 0 <= a -> 0 <= b -> Z.log2 (a .& b) <= Z.min (Z.log2 a) (Z.log2 b).
Check Z.log2_lxor: forall a b : Z, 0 <= a -> 0 <= b -> Z.log2 (a .^ b) <= Z.max (Z.log2 a) (Z.log2 b).
Check Z.log2_shiftl': forall a n : Z, 0 < a -> Z.log2 (a .<< n) = Z.max 0 (Z.log2 a + n).
Check Z.log2_shiftl: forall a n : Z, 0 < a -> 0 <= n -> Z.log2 (a .<< n) = Z.log2 a + n.
Check Z.log2_shiftr: forall a n : Z, 0 < a -> Z.log2 (a .>> n) = Z.max 0 (Z.log2 a - n).


(* 証明例 *)

(* xor の証明 *)
(* bool で証明して、バイナリに injection する。 *)
Check Z.bits_inj' : forall a b : Z, (forall n : Z, 0 <= n -> Z.testbit a n = Z.testbit b n) -> a = b.

Lemma xor_or_and (a b : bool) : a ^^ b = (a || b) && (~~ a || ~~ b).
Proof.
  by case: a; case b.
Qed.

Lemma lxor_lor_land (x y : Z) : x .^ y = (x .| y) .& (.~ x .| .~ y).
Proof.
  apply: Z.bits_inj' => n H.
  rewrite Z.land_spec.
  (* 左辺 *)
  rewrite Z.lxor_spec xor_or_and.
  (* 右辺 *)
  by rewrite 2!Z.lor_spec Z.lnot_spec //=  Z.lnot_spec.
Qed.

(* END *)
