(**
誰も書かない圏論入門以前の話

========================

@suharahiromichi

2020/11/03
 *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CATE.
(**
# 準備
 *)
  Variables (Obj : Type) (Hom : Obj -> Obj -> Set).
  
(**
# 対象とはなにか

対象とは Obj型の要素です。
*)
  Variables A B C : Obj.
  
(**
同じにみえる対象は等しい。
*)
  Goal A = A. Proof. done. Qed.
  
(**
同じに見えない対象は、等しいか等しくないか、判らない。
*)
  Goal A = B. Proof. Abort.
  Goal A <> B. Proof. Abort.

(**
同じと定義すれば、等しくなる。
*)
  Definition X := A.
  Goal X = A. Proof. rewrite /X. done. Qed.

(**
具体圏を考える場合は、この Obj が具体的な型に具体化され、
その型で定義された等号に基づいて対象の等しさが定義されます。

例えば、自然数を対象とする圏の場合、対象の等しさは自然数の等しさで定義されます。
*)  
  Check 1 : nat.
  Check 2 : nat.

  Goal 1 = 1. Proof. done. Qed.
  Goal 1 <> 2. Proof. done. Qed.


(**
# 射が等しいとは

射とは Obj型からObj型への型の要素です。
 *)
  Variable f f' : Hom A B.
  Variable g g' : Hom B C.
  Variable h h' : Hom A C.
  
(**
同じにみえる射は等しい。
*)
  Goal f = f. Proof. done. Qed.

(**
ドメインとコドメインが同じだからとって、等しいわけではない。
実際に、同じに見えない対象は、等しいか等しくないか、判らない。
 *)
  Goal f = f'. Proof. Abort.
  Goal f <> f'. Proof. Abort.
  
(**
ドメインやコドメインの異なる射どうしは、比較さえできない。
*)  
  Fail Goal f = g.
  
(**
同じと定義すれば、等しくなる。
*)
  Definition g'' := g.
  Goal g = g''. Proof. rewrite /g''. done. Qed.
  
(**
# 射の合成の意味

``Hom A B`` の射 f と、``Hom B C`` の射 g から、
``Hom A C`` の射 ``g・f`` ができることをいう。
 *)
  Variable comp : forall {Ob1 Ob2 Ob3 : Obj}, Hom Ob2 Ob3 -> Hom Ob1 Ob2 -> Hom Ob1 Ob3.
  Infix "・" := comp (at level 20, right associativity).
  
  Check comp g f.
  Check g・f.

(**
f・g は作れない。コドメインとドメインが繋がらないから。
*)
  Fail Check f・g.

(**
同じにみえる射は等しいことから、 g・f どうしは等しい。 
*)  
  Goal g・f = g・f. Proof. done. Qed.
  
(**
``g・f`` は``Hom A C``の射だが、前に定義した``Hom A C``の射 h と等しいとは限らない。
*)
  Goal g・f = h. Proof. Abort.
  Goal g・f <> h. Proof. Abort.

(**
同じと定義すれば、等しくなる。
*)
  Definition h'' := g・f.
  Goal g・f = h''. Proof. rewrite /h''. done. Qed.

(**  
## 射の合成・可換図式の意味 （その1）
 *)
(**
``g・f = h`` は、これを満たす射の存在を主張しているのに過ぎない。可換図式も同様である。

- ``Hom Ob1 Ob2`` の任意の射と、``Hom Ob2 Ob3`` の任意の射に対して、``Hom Ob1 Ob3``
の射が存在する。
 *)
  Definition ex_comp_hom {Ob1 Ob2 Ob3 : Obj} (m2 : Hom Ob2 Ob3) (m1 : Hom Ob1 Ob2) :=
    exists (m3 : Hom Ob1 Ob3), m2・m1 = m3.
  
  Goal ex_comp_hom g f.
  Proof. exists h''. done. Qed.
  
(**
- ``Hom Ob2 Ob3`` の任意の射と、``Hom Ob1 Ob3`` の任意の射に対して、``Hom Ob1 Ob2``
の射が存在する。
 *)
  Definition ex_comp_hom_1 {Ob1 Ob2 Ob3 : Obj} (m2 : Hom Ob2 Ob3) (m3 : Hom Ob1 Ob3) :=
    exists (m1 : Hom Ob1 Ob2), m2・m1 = m3.
  
  Goal ex_comp_hom_1 g h''.
  Proof. exists f. done. Qed.

(**
- ``Hom Ob1 Ob2`` の任意の射と、``Hom Ob1 Ob3`` の任意の射に対して、``Hom Ob2 Ob3``
の射が存在する。
*)  
  Definition ex_comp_hom_2 {Ob1 Ob2 Ob3 : Obj} (m1 : Hom Ob1 Ob2) (m3 : Hom Ob1 Ob3) :=
    exists (m2 : Hom Ob2 Ob3), m2・m1 = m3.
  
  Goal ex_comp_hom_2 f h''.
  Proof. exists g. done. Qed.

(**  
## 射の合成・可換図式の意味 （その2）

等しい射を合成した射は等しい。

逆は一般には成り立たないが、一方がモノ、あるいは、エピならば逆が成り立つ。
 *)
  Goal forall {Ob1 Ob2 Ob3 : Obj} (m2 m2' : Hom Ob2 Ob3) (m1 m1' : Hom Ob1 Ob2),
      m1 = m1' -> m2 = m2' -> m2・m1 = m2'・m1'.
  Proof.
    move=> Ob1 Ob2 Ob3 m2 m2' m1 m1' H1 H2.
      by rewrite -H1 -H2.
  Qed.
  
(**
# 射の一意

P を満たす射が一意に存在するとは、``∃!(m : Hom Ob1 Ob2).P(m)``
と書く場合があるが、Coqにはその記法はない。
*)
  Definition uniq_P {Ob1 Ob2 : Obj} (P : Hom Ob1 Ob2 -> Prop) :=
    forall (m : Hom Ob1 Ob2), P m -> exists (m' : Hom Ob1 Ob2), P m' -> m = m'.

(**
あるいは、m を満たす ``Hom Ob1 Ob2`` 型の要素は唯一であるといえる。
*)

(**
# 関手は写像であるから

射 f g h があり ``g・f = h`` が成り立つとする。
 *)
  Check f : Hom A B.
  Check g : Hom B C.

  Check h'' : Hom A C.
  Check g・f : Hom A C.
  Goal g・f = h''. Proof. done. Qed.


(**
対象と対象の写像と射と射の写像 F : C -> D が存在するなら、

  F(A) = A'
  F(B) = B'
  F(C) = C'

  F(f) : Hom A' B'
  F(g) : Hom B' C'
  F(h) : Hom A' C'

であるとき、``h = g・f`` なので、

  F(h) = F(g・f)

は成り立つ。また、

  F(g)・F(f) : Hom A' C'

である。しかし、

  F(g)・F(f) = F(g・f)                          (#)

とは言えない。なぜならば、写像 F が g・f が写す先が、
特定の ``F(g)・F(f)`` であるとが限らないからである。
（写像なので、写す先は一意であることに注意してください）。

しかし、F(f) と F(g) に対して F(g・f) が一意である場合は、
写像 F が g・f が写す先の ``Hom A C`` の要素はひとつであるから(#)は成り立つ。

よって、F は C -> D の関手といえる。
 *)

(**
証明。

h = g・f なので、

  F(f) = f'
  F(g) = g'
  F(h) = F(g・f) = h'

とする。f'とg'に対して h' は一意であることから、

  g'・f' = h' -> (∃h''. g'・f' = h'' -> h' = h'')

これから、適当な h'' として F(g)・F(h) を代入すると、

  F(g)・F(f) = F(g・f)

が得られる。
*)

End CATE.

(* END *)
