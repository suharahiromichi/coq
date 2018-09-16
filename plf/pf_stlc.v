(** ProofCafe SF/PLF Support Page *)
(** Stlc.v *)

(**
これは、「Software Foundations, Vol.2 Programming Language Foundations」 の
勉強会（ProofCafe）のサポートページです。復習などに利用しててください。

本ファイルの実行は、本ファイルを pfl ディレクトリの中に混ぜて置くか、
pfl のオリジナルの適当なファイルの適当な場所にcopy&pasteすることで可能です。
 *)

(** ご注意：

1. 実際の勉強会は、本ファイルではなく、オリジナルのファイルを直接編集・実行しておこないます。

2. 本ファイルには、演習問題の答えは含まれません。

*)

Require Import Coq.Arith.Arith.
Require Import Maps.
Require Import Imp. 
Require Import Smallstep.
Require Import Types.
Require Import Stlc.

(* Module *)
Import STLC.
Export STLC.

(* ################################################################# *)
(** ProofCafe ##78 2018/08/18 *)
(** ProofCafe ##79 2018/09/15 *)

(**
目次

対象言語の型と項を定義する。

Small-Step 関係を定義する。

話題 #1 substi_correct

型付け(typing)関係を定義する。

話題 #2 equiv_types

話題 #3 Gamma

話題#1 自由変数の扱いについて。テクニカルノート

補足説明 Big Step はどうなった？

話題#2 「λx.(x x) の型付け不能」 最後の演習問題

補足説明 型の有限性を前提としていること
*)

(**
概要

型と項を定義する。
*)

Print ty.
(**
型は、Bool と（Boolの）関数型。
[[
 | TBool : ty
 | TArrow : ty -> ty -> ty
]]
*)

(** BNF風に書くと  *)
(** <ty> ::= TBool | TArrow <ty> <ty>  *)

Print tm.
(**
Bool型の定数とif式、変数と関数抽象と関数適用だけからなる項である。
[[
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
]]
*)

(** BNF風に書くと  *)
(** <id> ::= x | y | z  *)
(** <tm> ::= tvar <id> | tapp <tm> <tm> | tabs <id> <ty> <tm>
    | ttrue | tfalse | tif <tm> <tm> <tm> *)

(** このうち、ttrue、tfalse と tabs<id><ty><tm> がvalueである。
    tvar<id>はvalueでないことの注意してください。 *)

(**
**************************************************
Small-Step 関係を定義する。
**************************************************
*)
Locate "[ _ := _ ] _".                      (* subst x s t *)

Print step.
(**
[[
  | ST_AppAbs : forall (x : id) (T : ty) (t12 v2 : tm),
                value v2 -> tapp (tabs x T t12) v2 ==> [x := v2] t12
  | ST_App1 : forall t1 t1' t2 : tm, t1 ==> t1' -> tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2' : tm,
              value v1 -> t2 ==> t2' -> tapp v1 t2 ==> tapp v1 t2'
  | ST_IfTrue : forall t1 t2 : tm, tif ttrue t1 t2 ==> t1
  | ST_IfFalse : forall t1 t2 : tm, tif tfalse t1 t2 ==> t2
  | ST_If : forall t1 t1' t2 t3 : tm,
            t1 ==> t1' -> tif t1 t2 t3 ==> tif t1' t2 t3
]]

[[
証明図っぽい書き方
A ==> A'  B ==> B'
-----------------
C ==> C'
]]

は、[A ==> A' -> B ==> B' -> C ==> C'] の意味です。

また、

ST_If は、if t1 then t2 else t3 のうち if項である t1 をまず値にすること、
ST_App1 は、(t1 tm) の t1の項をまず値にすること。

を示しています。
*)

Locate "_ ==> _".          (* "t1 '==>' t2" := step t1 t2 *)
Locate "_ ==>* _".         (* "t1 '==>*' t2" := multi step t1 t2 *)
About multi.               (* mutli は Smallstep で定義されたもの。 *)
Print multi.               (* 次の R に step が入る。 *)
(**
Inductive multi {X : Type} (R : relation X) : relation X :=
    multi_refl : forall x : X, multi R x x
  | multi_step : forall x y z : X, R x y -> multi R y z -> multi R x z
 *)

(**
それでは、step_example を解いていきましょう！！！
*)
Check step_example1 : tapp idBB idB ==>* idB.
Check step_example2 : tapp idBB (tapp idBB idB) ==>* idB.
Check step_example3 : tapp (tapp idBB notB) ttrue ==>* tfalse.
Check step_example4 : tapp idBB (tapp notB ttrue) ==>* tfalse.
Check step_example5 : (tapp (tapp idBBBB idBB) idB) ==>* idB.

(* 話題 #1 *)
(**
subst は Fixpoint で定義された関数で、変数を項に置き換えるものある。
 *)
Print subst.
(**
[[
subst = 
fix subst (x : id) (s t : tm) {struct t} : tm :=
  match t with
  | tvar x' => if beq_id x x' then s else t
  | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
  | tabs x' T t1 => tabs x' T (if beq_id x x' then t1 else subst x s t1) ← 注意
  | ttrue => ttrue
  | tfalse => tfalse
  | tif t1 t2 t3 => tif (subst x s t1) (subst x s t2) (subst x s t3)
  end
     : id -> tm -> tm -> tm
]]

注意：
[tabs <id> <ty> <tm>] の<tm>についても書き換えが行われることに注意してください。
このとき、束縛された変数は（仮に名前が同じでも）書き換えの対象になりません。
 *)

(**
Fixpoint で定義されたsubst と Inductive で定義された substi と同じであることを証明する。

こういった証明の技法については、SFの第3部 VFA も参照のこと。
 *)
Check substi : tm -> id -> tm -> tm -> Prop.
(** subst の引数と値の関係を定義する仕様と考える。 *)

Check substi_correct :
  forall (s : tm) (x : id) (t t' : tm), [x := s] t = t' <-> substi s x t t'.

(**
**************************************************
型付け(typing)関係を定義する。
**************************************************
*)
Locate "_ |- _ \in _". (* "Gamma '|-' t '\in' T" := has_type Gamma t T *)
Print has_type.
(**
[[
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall (Gamma : id -> option ty) (x : id) (T : ty),
            Gamma x = Some T -> Gamma |- tvar x \in T
  | T_Abs : forall (Gamma : partial_map ty) (x : id) (T11 T12 : ty) (t12 : tm),
            update Gamma x T11 |- t12 \in T12 ->
            Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall (T11 T12 : ty) (Gamma : context) (t1 t2 : tm),
            Gamma |- t1 \in TArrow T11 T12 ->
            Gamma |- t2 \in T11 -> Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma : context, Gamma |- ttrue \in TBool
  | T_False : forall Gamma : context, Gamma |- tfalse \in TBool
  | T_If : forall (t1 t2 t3 : tm) (T : ty) (Gamma : context),
           Gamma |- t1 \in TBool ->
           Gamma |- t2 \in T -> Gamma |- t3 \in T -> Gamma |- tif t1 t2 t3 \in T
]]
*)
(** if t1 t2 t3 のthen (t2) と else (t3) が同じ型でなければならないことに注意してください。 *)

(**
それでは、typing_example を解いていきましょう！！！
*)
Check typing_example_1 : empty |- idB \in TArrow TBool TBool.
Check typing_example_2 : empty |- tabs x TBool
            (tabs y (TArrow TBool TBool) (tapp (tvar y) (tapp (tvar y) (tvar x)))) \in
    TArrow TBool (TArrow (TArrow TBool TBool) TBool).
Check typing_example_3 : exists T,
    empty |-
      (tabs x (TArrow TBool TBool)
         (tabs y (TArrow TBool TBool)
            (tabs z TBool
               (tapp (tvar y) (tapp (tvar x) (tvar z)))))) \in T.
Check typing_nonexample_1 :
  ~ (exists T : ty,
        empty |- tabs x TBool (tabs y TBool (tapp (tvar x) (tvar y))) \in T).
Check typing_nonexample_3 :        (* TAPL 演習 9.3.2. とおなじ。 *)
  ~ (exists S, exists T,
        empty |-
          (tabs x S
             (tapp (tvar x) (tvar x))) \in T).

(* 話題 #2 *)
(**
fixpoint で type_of を定義する。TAPLの10.3型検査の節を参照。

type_of と has_type が同じであることを証明する equiv_types 。
これについては、pf_type.v を参照のこと。
 *)

(* 話題 #3 *)
(**
注意：原ドキュメントでは、Gammaが関数か集合か解りにくくなっています。

Gamma は関数で [Gamma x = T] は [(Gamma x) = T] であり、集合で [x:T ∈ Gamma] の意味です。
また、[Gamma, x:T11] は、[Gamma ∪ {x:T11}] の意味です（どちらも集合）。

Map.v では Gamma は関数 (partical_map型) として定義されるので、
[x : T ∈ Gamma] を [(Gamma x) = (Some T)] と記述しています。また、
[Gamma ∪ {x:T11}] は [update Gamma x T11] となります。

typing_example_1 の証明図を集合的に書く。
[[
   x:Bool ∈ {x:Bool}
----------------------------------------- T_Var
  {x:Bool} |- x:Bool
----------------------------------------- T_Abs
        φ |- λx:Bool.x : Bool->Bool
]]

追記：
このように文句を書いたところ、原書では Maps.v に Notation が追加されて、
[update Gamma x T11] が [Gamma & {{x --> T11}}] と書けるようになった。
つまり、Coq側の関数定義を集合風の表記で扱えるようになった。

また、string が id に変わっているが、これは大きな影響はない。
*)

(** Gamma の定義について。Map.v を参照 *)

(** Gamma の作り方 *)
Definition Empty  := @empty ty             : partial_map ty. (* φ *)
Definition Gamma1 := update Empty  x TBool : partial_map ty. (* {x : Bool} *)
Definition Gamma2 := update Gamma1 y (TArrow TBool TBool) : partial_map ty.
(* Gamma1 ∪ {y : Bool -> Bool *)

(** Gamma から型の取り出し型  *)
Compute Empty x.                            (* None *)
Compute Gamma1 x.                           (* Bool *)
Compute Gamma1 y.                           (* None *)
Compute Gamma2 x.                           (* Bool *)
Compute Gamma2 y.                           (* Bool -> Bool *)

(** Gamma を update したものをすぐに取り出している場合は、
[apply update_eq] でただちに証明できる。 *)

Check update_eq : forall (A : Type) (m : partial_map A) (x : id) (v : A),
    update m x v x = Some v.
(** mをxでupdateしたあと [update m x v]、
すぐxを取り出す [(update m x v) x]  。
ならば、値は [v] である。 *)

Goal update Empty x TBool x = Some TBool.
Proof.
  now apply update_eq.
  Undo.
  Check (update_eq ty Empty x TBool) : update Empty x TBool x = Some TBool.
  now apply (update_eq ty Empty y TBool).
  Undo.
  
  (* updateを計算してしまう、という方法もある。 *)
  unfold update, t_update. simpl. reflexivity.
Qed.

Goal update Gamma1 y (TArrow TBool TBool) y = Some (TArrow TBool TBool).
Proof.
  now apply update_eq.
  Undo.
  Check (update_eq ty Gamma1 y (TArrow TBool TBool)) :
    update Gamma1 y (TArrow TBool TBool) y = Some (TArrow TBool TBool).
  now apply (update_eq ty Gamma1 y (TArrow TBool TBool)).
  Undo.
  
  (* updateを計算してしまう、という方法もある。 *)
  unfold update, t_update. simpl. reflexivity.
Qed.

(** updateを計算してしまう、という方法もある。 *)
(** こっちのほうが汎用的なのではないか。  *)
Goal Gamma2 y = Some (TArrow TBool TBool).
Proof.
  unfold Gamma2, Gamma1.
  unfold update, t_update. simpl. reflexivity.
Qed.

Goal Gamma2 x = Some TBool.
Proof.
  unfold Gamma2, Gamma1.
  unfold update, t_update. simpl. reflexivity.
Qed.

(** ***************** *)
(** 話題#1 自由変数の扱いについて。テクニカルノート *)
(** ***************** *)

(**
値 Value の節

関数抽象 λa:A.t1 を値とみなすか？

第一の選択肢：t1が値であるなら、値とみなす。（この場合、t1 が step の対象となる）
第二の選択肢：t1が値でなくても、値とみなす。（この場合、t1 は step の対象にならない）

（引用）
しかし実際の関数型プログラミング言語のほとんどは、 第二の選択肢を取っています。
つまり、関数の本体の簡約は、関数が実際に引数に適用されたときにのみ開始されます。
ここでは、同様に第二の選択肢を選びます。

Most real-world functional programming languages make the second choice
— reduction of a function's body only begins
when the function is actually applied to an argument.
We also make the second choice here.
（引用終）

具体的には、任意の項tに対して、value (tabs x T t) が成り立つ。
 *)

Print value.
(**
[[
Inductive value : tm -> Prop :=
  | v_abs : forall (x : id) (T : ty) (t : tm), value (tabs x T t)
  | v_true : value ttrue
  | v_false : value tfalse
]]
*)

(**
置換 Substituion の節

（引用）
技術的注釈: 置換は、もし、つまり他の項の変数を置換する項が、 それ自身
に自由変数を含むときを考えると、 定義がよりトリッキーなものになります。
ここで興味があるのは閉じた項についてのstep関係の定義のみなので、そのさ
らなる複雑さは避けることができます。
（引用終）

自由変数を扱うのは面倒である。しかし、
・関数抽象 λa:A.t1 の t1 には、変数aを含む。t1においてaは自由変数である。
・第二の選択肢をとることで、自由変数を含む t1 はstepの対象にしない。
・よって、自由変数の面倒さを回避できた。

補足説明：
上記の場合以外で、自由変数は出現しないのか。→しないようにする。
そもそも、STLCでは、グローバル変数のようなもを導入しない。

TAPLは、習慣 5.3.4
自由変数と束縛変数の名前は重ならないようにする。束縛変数側で常にリネームする習慣とする。
TAPLのサンプルコードは de Brujin Index を使用している。
*)

(** 補足説明 *)
(** BIG STEP の話はどうなりましたか。 *)

(** small step は項書換え系である。
一方、big step で、環境束縛による評価をおこなう場合、
静的束縛と動的束縛の違いによって、結果が事なる場合がある。
 *)

(** 例 *)
Check   (fun x => (fun f => (fun x => f (x + 3)) 2) (fun y => x + y)) 1.
Compute (fun x => (fun f => (fun x => f (x + 3)) 2) (fun y => x + y)) 1. (* 6 *)

Check   (fun x => (fun f => (fun x => f x) false) (fun y => x)) true.
Compute (fun x => (fun f => (fun x => f x) false) (fun y => x)) true. (* true *)

(* f = fun y => x であるが、 *)
(* 静的束縛の場合は、f ≡ fun y => x1 ≡ fun y => true *)
(* f x2 ≡ false *)
Compute (fun x1 => (fun f => (fun x2 => f x2) false) (fun y => x1)) true. (* true *)

(* 動的束縛の場合は、f ≡ fun y => x2 ≡ fun y => true *)
(* f x2 ≡ true *)
Fail Compute (fun x1 => (fun f => (fun x2 => f x2) false) (fun y => x2)) true. (* false *)

(*
big stepを単純に実装すると動的束縛になる。
現在では、動的束縛で得られる結果は「bug」とされている。
（静的束縛による結果こそが正しい、と考える）

そこで、big stepにおいて、
関数抽象を評価したときに、値として「クロージャ closure」を得ることで、
静的束縛を実現する。

クロージャによって静的束縛が実現される様子：
環境 (x:=true) のもとで、λy.x を評価すると、
クロージャ<λy.x, (x:=true)> が得られ、それがfに代入される。
環境 (x:=false) のもとで、f x を適用しても、
fの中身を評価するときはクロージャの環境が使われるので x は true となる。
*)

(* small step は項書換え系なので、静的束縛と同じ結果になる。 *)

Compute (fun x => (fun f => (fun x => f
                                        x)
                              false)
                    (fun y => x))
        true.
(* true *)

Definition t := 
  tapp
    (tabs x TBool (tapp
                     (tabs z (TArrow TBool TBool) (tapp
                                                     (tabs x TBool (tapp
                                                                      (tvar z)
                                                                      (tvar x)))
                                                     tfalse))
                     (tabs y TBool (tvar x))))
    ttrue.

Goal t ==>* ttrue.
Proof.
  eapply multi_step.
  - constructor.
    easy.
  - simpl.
    eapply multi_step.
    + constructor.
      easy.
    + simpl.
      eapply multi_step.
      * constructor.
        easy.
      * simpl.
        eapply multi_step.
        ** constructor.
           easy.
        ** simpl.
           easy.
Qed.

(** ***************** *)
(** 話題#2 「λx.(x x) の型付け不能」 最後の演習問題 *)
(** ***************** *)

(** [~ (exists S, exists T, empty |- \x : S. x x \in T) ] **)
(** [~ (∃S. ∃T. ├ λx : S.(x x) ∈ T *)

Check typing_nonexample_3 :
  ~ (exists S T : ty,
        has_type empty
                      (tabs x S (tapp (tvar x) (tvar x)))
                      T).

(** TAPL 演習 9.3.2 が参考になる。 *)

(** TAPL の 演習 9.3.2 *)
(** 回答 9.3.2. では、すべての型が有限サイズを持つことから、
    T1 -> T2 = T1 は偽であるとしている。 *)
Lemma type_finiteness : forall (T1 T2 : ty), TArrow T1 T2 <> T1.
Proof.
  intros T1 T2 H.
  induction T1 as [|T11 H1 T12 H2].
  - (* T1 = TBool *)
    easy.
  - (* T1 = T11 -> T12 *)
    (* inversion タクティクは、TAPL の 型付け関係の逆転の補題
       (9.3.1 inversion lemma) を使うのとと同じ。 *)
    inversion H.
    (* T11 -> T12 = T11 を得る。 *)
    rewrite H4 in *.                      (* subst はエラーになる。 *)
    (* これは偽である。 *)
    easy.
Qed.

(** これは、STLCに限定したことでははなく、コンストラクタ一般に成り立つ。  *)

(** Smallstep で定義した Plus コンストラクタの場合 *)
Goal forall tm1 tm2, P tm1 tm2 <> tm1.
Proof.
  intros tm1 tm2 H.
  induction tm1.
  - easy.
  - inversion H.
    rewrite H1 in *.
    easy.
Qed.

(** list の cons の有限性 *)
Lemma list_finiteness : forall (n : nat) (l : list nat), cons n l <> l.
Proof.
  intros n l H.
  induction l as [|n' l].
  - easy.
  - inversion H; clear H.                 (* subst はエラーになる。 *)
    rewrite H1 in *; clear H1.
    easy.
Qed.

(** より一般的に、(Inductiveで定義された）コンストラクタの有限性を証明できないだろうか。 *)
(** 直観的な証明ではひとことで済むことが、形式的には毎回証明が必要になる例だろうか。 *)

(** 補足説明 *)

(**
型の有限性を前提とすると、再帰呼び出しによる繰り返しができないことになります。
それについては、MoreStlc の General Recursion の節 や

https://www.math.nagoya-u.ac.jp/~garrigue/lecture/2016_kyouyou/typed.pdf

を参考にしてください。
*)

(* END *)
