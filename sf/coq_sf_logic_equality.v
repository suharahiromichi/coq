(** * Logic_J: Coqにおける論理 *)
(* @suharahiromochi 2012_11_26 *)
(*  * Equality *)
(** * 等しいということ（同値性） *)

Module MyEquality.

Inductive eq (X:Type) : X -> X -> Prop :=
  refl_equal : forall x, eq X x x.
Notation "x = y" := (eq _ x y)
  (at level 70, no associativity) : type_scope.

Definition eq_ind_me : forall (X : Type) (P : X -> X -> Prop),
  (forall u : X, P u u) -> forall v w : X, v = w -> P v w.
Proof.
  intros X P H v w H0.
  destruct H0.
  apply H.
Qed.

(** この例は少し難解かもしれません。これがどういうものかを考えると、
    集合 [X] が与えられると、「集合 [X] に属する値 ([x] and [y]) にインデックス
    された、[x] は [y] に等しい」というような命題の _集団_ を定義してくれる
    ということです。この集団に属する命題に根拠を与えるためには、一つの
    方法しかありません。それは、コンストラクタ [refl_equal] に型 [X] とその値
    [x : X] を適用し、[x] が [x] と等しいという根拠を生成することです。
 *)

(* Coqの標準ライブラリにおける定義 *)
Inductive eq' (X:Type) (x:X) : X -> Prop :=
    refl_equal' : eq' X x x.
Notation "x =' y" := (eq' _ x y)
  (at level 70, no associativity) : type_scope.
Check eq'_ind.

Definition eq'_ind_me : forall (X : Type) (u : X) (P : X -> Prop),
  P u -> forall v : X, u =' v -> P v.
Proof.
  intros X u P H v H0.
  destruct H0.
  apply H.
Qed.

(** これら二つの定義が等価であることを確認する。 *)

(** 一般的な証明 *)
Theorem two_defs_of_eq_coincide : forall (X:Type) (x y : X),
  x = y <-> x =' y.
Proof.
  intros X x y.
  split.
(* -> *)
  intros H.
  (* H : x = y を使って、Goal : x =' y を x =' x にする。 *)
  destruct H.
  apply refl_equal'.

(* <- *)
  intros H'.
  (* H : x =' y を使って、Goal : x = y を x = x にする。 *)
  destruct H'.
  apply refl_equal.
Qed.

(** apply を明示的につかう証明 *)
Theorem two_defs_of_eq_coincide' : forall (X:Type) (x y : X),
  x = y <-> x =' y.
Proof.
  intros X x y.
  split.
(* -> *)
  Check (eq_ind X (eq' X)).
(**
   (forall x, x =' x) ->
   forall y y0, y = y0 ->
   y =' y0

   deﬁnitional equality（intentional equality ???）
   簡単に書くと、
   ∀x(x =' x) -> ∀y∀y0(y = y0 -> y =' y0)
   
   eq (=) は、それが成立するなら、eq' (=') も成立するような命題を与える。
   ここで、eq' (=') は同じものなら成立する(x =' x)ようなもの。
   （このことから、「β簡約で同じ」と言えるだろうか？）
*)
  apply (eq_ind X (eq' X)).
  apply refl_equal'.
  
(* <- *)
  Check (eq'_ind X x (fun y0 => (eq X x y0))).
(**
   (fun y0 => x = y0) x ->
   forall y, x =' y ->
   (fun y0 : X => x = y0) y
   
   propositional equality（extensional equality ???）
   簡単に書くと、x= ≡ P ≡ λy0.(x = y0) に対して、
   x= x -> ∀y(x =' y -> x= y)
   P  x -> ∀y(x =' y -> P  y)
   
   eq' (=' ≡ propositional equality)は、P(≡ x=) に対して、
   ライプニッツの外延性を満たす。Leibniz equality という。
*)
  apply (eq'_ind X x (fun y0 => (eq X x y0))).
  apply refl_equal.
Qed.

(** [] *)

(**
   二つ目の定義の優れたところは、Coqが生成する帰納法の原理が正確に
   「ライプニッツの同値関係（ _Leibniz equality_ ）」と親和している点です。
   それはつまり、「[x] と [y] が等しいということは、 任意の命題 [P] が
   [x] でtrueとなるならば [y] でもtrueとなる」ということです。
 **)

(** 一つ大事なことが残っています。確かに [refl_equal] は [2 = 2] というような
    証明に根拠を与えることに使えます。 [1 + 1 = 2] はどうでしょうか？
    答えは Yes です。実際、これらは証明としてはほとんど同じようなものだと
    言えます。 その理由は Coq が二つの式がシンプルな計算ルールによって交換可能である
    ことをを示し、それを"同値である"として処理しているからです。
    このルールは [Eval simpl] と同じものです。ただしこれには、
    関数適用の評価、定義のインライン化、[match] の簡約が含まれています。

    タクティックを使った同値性の証明では、 [simpl] を使うことで暗黙的にこの
    交換ルールに触れています（[reflexivity] のような他のタクティックでも、明示的に、
    もしくは暗黙的に含まれています）。このことは、次のような明示的な証明オブジェクトで
    確認することができます。
 *)

Definition four : 2 + 2 = 1 + 3 :=
  refl_equal nat 4.

(* 同様に eq' でも可能である。*)
Definition four' : 2 + 2 =' 1 + 3 :=
  refl_equal' nat 4.

End MyEquality.
