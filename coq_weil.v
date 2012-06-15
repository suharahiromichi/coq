(* ヴェイユ「初学者のための整数論」 
   演習 1.1 (-1) (-1) = 1 を示せ。
   
   分配律を使っていることはたしかだが、
   解答編と正確に一致しているわけではない。
*)


Require Import Setoid.                      (* rewrite H at n *)


Inductive  Z : Set :=
| One : Z
| Zero : Z
| Plus : Z -> Z -> Z
| Mult : Z -> Z -> Z
| Neg  : Z -> Z.


Infix "+" := Plus (at level 50, left associativity).
Infix "*" := Mult (at level 40, left associativity).
Notation "--" := Neg (at level 10).
Check Zero + -- One + Zero.


(*
Implicit Arguments Plus.
Implicit Arguments Mult.
Implicit Arguments Neg.
*)


(*
Axiom plus_injection :
  forall x y a,
    x + a = y + a -> x = y.
Axiom plus_injection' :
  forall x y a,
    x = y -> x + a = y + a.
*)


Axiom swap :
  forall x y : Z, x = y -> y = x.


(* 結合則 *)
Axiom plus_associative_law :
  forall x y z a, x + (y + z) = a -> (x + y) + z = a.
Axiom plus_associative_law' :
  forall x y z a, (x + y) + z = a -> x + (y + z) = a.


(* 可換則 *)
Axiom plus_commutative_law :
  forall x y a, x + y = a -> y + x = a.


(* 方程式 *)
Axiom solve_equation :
  forall a b,
    forall x y,
      (a + x = b /\ a + y = b) -> x = y.


Axiom solve_equation2 :                     (* solution x *)
  forall a b,
    exists x, a + x = b.                    (* 解xが存在する *)


(* 単位元 *)
Axiom plus_identity_element :
  forall x, Zero + x = x.
Axiom plus_identity_element_law :
  forall x a, Zero + x = a -> x = a.
Axiom plus_identity_element_law' :
  forall x a, x = a -> Zero + x = a.


(* 結合則 *)
Axiom mult_associative_law :
  forall x y z a, x * (y * z) = a -> (x * y) * z = a.
Axiom mult_associative_law' :
  forall x y z a, (x * y) * z = a -> x * (y * z) = a.


(* 可換則 *)
Axiom mult_commutative_law :
  forall x y a, x * y = a -> y * x = a.


(* 単位元 *)
Axiom mult_identity_element :
  forall x, One * x = x.
Axiom mult_identity_element_law :
  forall x a, One * x = a -> x = a.
Axiom mult_identity_element_law' :
  forall x a, x = a -> One * x = a.


(* Negの定義。もうすこし厳密であるべきだろうか。 *)
Axiom plus_neg :
  forall x,
    -- x + x = Zero.
Axiom plus_neg' :
  forall x,
    x + -- x = Zero.
Axiom mult_neg :
  forall x y,
    -- (x) * y = -- (x * y).




(* 分配則 *)
Axiom distributive_law :
  forall x y z a, x * (y + z) = a -> x * y + x * z = a.
Axiom distributive_law' :
  forall x y z a, x * y + x * z = a -> x * (y + z) = a.


(* 補助定理 *)


(*********************************)
(* a * 0 = 0                     *)
(*********************************)


Lemma one_plus_zero_eq_one :                (* 1 + 0 = 1 *)
  One + Zero = One.
Proof.
  apply plus_commutative_law.
  apply plus_identity_element_law'.
  reflexivity.
Qed.


(*
Lemma one_mult_zero_eq_zero :               (* 1 * 0 = 0 *) (* 使っていない *)
  One * Zero = Zero.
Proof.
  apply mult_identity_element_law'.
  reflexivity.
Qed.


Lemma one_a_zero_eq_a :                     (* a + 0 = a *) (* 使っていない *)
  forall a, a + Zero = a.
Proof.
  intros.
  apply plus_commutative_law.
  apply plus_identity_element_law'.
  reflexivity.
Qed.


Lemma a_plus_a_mult_zero_eq_a :
  forall a, a + a * Zero = a.
Proof.
  intros.
(*
  replace a with (a * One).
  apply mult_commutative_law.
  apply mult_identity_element'.
*)
  assert (forall a, a * One = a).
  intros.
  apply mult_commutative_law.
  apply mult_identity_element'.
  reflexivity.
  rewrite <- H.
  Abort.
*)


Lemma a_mult_One_eq_a :                     (* a * 1 = a *)
  forall a, a * One = a.
Proof.
  intros.
  apply mult_commutative_law.
  apply mult_identity_element_law'.
  reflexivity.
Qed.


Lemma a_plus_a_mult_zero_eq_a :             (* a * 1 + a * = a *)
  forall a, a * One + a * Zero = a.
Proof.
  intros.
  apply distributive_law.
  rewrite one_plus_zero_eq_one.
  (* 直接 rewrite <- plus_identity_element とすると、右辺の = a が書き換わってしまう *)
  apply mult_commutative_law.
  apply mult_identity_element_law'.
  reflexivity.
Qed.


Lemma a_mult_one_plus_zero_eq_a :           (* a * 1 + 0 = a *)
  forall a,
    a * One + Zero = a.
Proof.
  intro.
  apply plus_commutative_law.
  apply plus_identity_element_law'.
  apply mult_commutative_law.
  apply mult_identity_element_law'.
  reflexivity.
Qed.


(*
   a * 1 + a * 0 = a
   a * 1 + 0     = a
   の解としての、a * 0 = 0
*)


Lemma a_mult_zero_eq_zero :                 (* a * 0 = 0 *)
  forall a,
    a * Zero = Zero.
Proof.
  intros.
  Check solve_equation (a * One) a.
  apply (solve_equation (a * One) a).
  split.
  apply a_plus_a_mult_zero_eq_a.
  apply a_mult_one_plus_zero_eq_a.
Qed.


(*********************************)
(* -1 * -1 = 1                   *)
(*********************************)


Lemma t1 :
  -- One * One + -- One * -- One = Zero.
Proof.
  apply distributive_law.
  rewrite plus_neg'.
  apply a_mult_zero_eq_zero.
Qed.


Lemma t2 :
  -- One * One + One = Zero.
Proof.
  intros.
  rewrite mult_neg.
  rewrite mult_identity_element.
  rewrite plus_neg.
  reflexivity.
Qed.  


(*
   -1 * 1 + -1 * -1 = 0
   -1 * 1 + 1 = 0
   から、-1 * -1 = 1 を得る。
*)


Theorem neg_neg_pos :
  -- One * -- One = One.
Proof.
  Check (solve_equation (-- One * One) Zero).
  apply (solve_equation (-- One * One) Zero).
  split.
  apply t1.
  apply t2.
Qed.


(* End *)