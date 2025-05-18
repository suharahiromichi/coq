(*
Chapter 17 A Taste of Reasoning About Programming Language Syntax
*)
Require Import FunctionalExtensionality List. (* ext *)
Require Import Coq.Program.Equality.        (* dep_destruct E *)
Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import String.
Open Scope string_scope.

(* f_equal の「逆」をするタクティク *)
Ltac ext := let x := fresh "x" in extensionality x.

(* 複雑な場合分をする。 *)
Ltac dep_destruct E :=
  let x := fresh "x" in
  remember E as x; simpl in x; dependent destruction x;
  try match goal with
    | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
    end.

(* pl タクティクは使えない。 *)

(* 対象言語（変換は扱うが、ソース言語もターゲット言語も同じ） *)
(* 対象言語の型 *)
Inductive type : Type :=
| Nat : type
| Func : type -> type -> type.

(* 対象言語の型をGallinaの型に変換する関数 *)
Fixpoint typeDenote (t : type) : Type :=
  match t with
  | Nat => nat
  | Func t1 t2 => typeDenote t1 -> typeDenote t2
  end.

(** * 17.2 Parametric Higher-Order Abstract Syntax *)

Module HigherOrder.
  
  (* Typed PHOAS による対象言語の定義 *)
  Section var.
    Variable var : type -> Type.

    (* 型ファミリ（依存型）を引数 var にとる。var は representation of variables という。 *)
    Inductive term : type -> Type :=
    | Var : forall t, var t -> term t
    | Const : nat -> term Nat
    | Plus : term Nat -> term Nat -> term Nat
    | Abs : forall dom ran, (var dom -> term ran) -> term (Func dom ran)
    | App : forall dom ran, term (Func dom ran) -> term dom -> term ran
    | Let : forall t1 t2, term t1 -> (var t1 -> term t2) -> term t2.
  End var.

  Arguments Var [var t] _.
  Arguments Const [var] _.
  Arguments Abs [var dom ran] _.

  (* var を forall にした Term を定義する。 *)
  Definition Term t := forall (var : type -> Type), term var t.
  Check term : (type -> Type) -> type -> Type.
  Check Term : type -> Type.
  
  (* Typed PHOAS による対象言語の定義の例 *)
  (* forall (Π) 型の実体は、fun (λ) である。 *)
  Example add : Term (Func Nat (Func Nat Nat)) :=
    fun var => Abs (fun x => Abs (fun y => Plus (Var x) (Var y))).
  Example add' : Term (Func Nat (Func Nat Nat)) :=
    fun _ => Abs (fun x => Abs (fun y => Plus (Var x) (Var y))).
  
  Example three_the_hard_way : Term Nat :=
    fun var => App (App (add var) (Const 1)) (Const 2).
  Example three_the_hard_way' : Term Nat :=
    fun _ => App (App (add' _) (Const 1)) (Const 2).

  (* e全体の型は、``term var t`` であるが、コンストラクタによって、以下のように振り分けられる。  *)
  (* さらに、Var の中で、パラメタライズされた ``var t`` が出現する。 *)
  Check @Var   : forall (var : type -> Type)
                        (t : type),         (* t *)
      var t ->                              (* tt これがパラメタライズされたもの。 *)
      term var t.                           (* e全体 *)
  Check @Const : forall (var : type -> Type),
      nat ->                                (* n *)
      term var Nat.                         (* e全体 *)
  Check @Plus  : forall (var : type -> Type),
      term var Nat ->                       (* e1 *)
      term var Nat ->                       (* e2 *)
      term var Nat.                         (* e全体 *)
  Check @Abs   : forall (var : type -> Type) (dom ran : type),
      (var dom -> term var ran) ->          (* e1 *)
      term var (Func dom ran).              (* e全体 *)
  Check @App   : forall (var : type -> Type) (dom ran : type),
      term var (Func dom ran) ->            (* e1 *)
      term var dom ->                       (* e2 *)
      term var ran.                         (* e全体 *)
  Check @Let   : forall (var : type -> Type) (t1 t2 : type),
      term var t1 ->                        (* e1 *)
      (var t1 -> term var t2) ->            (* e2 *)
      term var t2.                          (* e全体 *)
  
  (* ``e : term var t`` で受けた値を、コンストラクタで組み立てられた要素に分解する。 *)
  
  (* 具体的に作った例： *)
  Check (fun (var : type -> Type) (t : type) => @Var var t _)         : forall var t, term var t.
  Check (fun var : type -> Type => @Const var 1)                      : forall var, term var Nat.
  Check (fun var : type -> Type => @Plus var (Const 1) (Const 1))     : forall var, term var Nat.
  Check (fun var : type -> Type =>
           (@Abs var Nat Nat (fun x => @Plus var (Const 1) (Var x)))) : forall var, term var (Func Nat Nat).
  Check (fun var : type -> Type =>
           (@Abs var Nat Nat (fun x => Var x))) : forall var, term var (Func Nat Nat).
  Check (fun var : type -> Type =>
           (@Abs var Nat (Func Nat Nat)
              (fun x => @Abs var Nat Nat
                          (fun y => @Plus var (@Const var 1) (@Plus var (Var x) (Var x))))))
    : forall var, term var (Func Nat (Func Nat Nat)).
  
  Check (fun (var : type -> Type) (t : type) => Var _)         : forall var t, term var t.
  Check (fun var : type -> Type => Const 1)                    : forall var, term var Nat.
  Check (fun var : type -> Type => Plus (Const 1) (Const 1))   : forall var, term var Nat.
  Check (fun var : type -> Type =>
           (Abs (fun x => Plus (Const 1) (Var x))))            : forall var, term var (Func Nat Nat).
  Check (fun var : type -> Type =>
           (Abs (fun x => Plus (Plus (Const 1) (Const 2)) (Var x)))) : forall var, term var (Func Nat Nat).
  Check (fun var : type -> Type => (Abs (fun x => Var x))) : forall var, term var (Func Nat Nat).
  Check (fun var : type -> Type =>
           (Abs (fun x => Abs (fun y => Plus (Const 1) (Plus (Var x) (Var x))))))
    : forall var, term var (Func Nat (Func Nat Nat)).

  (* fun var => ... は外せない。 *)
  Check (fun var : type -> Type => @Const var 1)               : Term Nat.
  Check (fun var : type -> Type => Const 1)                    : Term Nat.
  (* Typed PHOAS による対象言語の定義。終わり。 *)
  
  (** ** 17.2.1 Functional Programming with PHOAS *)

  (** *** CountVars *)
  
  (** This operation requires no data annotated on variables,
      so we simply annotate variables with [unit] values.
      数で注釈がついているデータを必要としない。
      
      Note that, when we go under binders in the cases for [Abs] and [Let],
      we must provide the data value to annotate on the new variable we pass beneath.
      For our current choice of [unit] data, we always pass [tt].
   *)
  
  (* コンストラクタの引数と、match の実引数を比べる。 *)
  Fixpoint countVars (t : type) (e : term (fun _ => unit) t) : nat :=
    match e with
    (*                       ↓↓↓↓↓↓↓ 型 ``var t : unit`` がパターンに出てくる。 *)
    (*       (var) (t)       (var t)                       (e全体 : term var t) *)
    | @Var   _     t         tt      => 1
    (*       (var)           (nat)                         (e全体 : term var Nat) *)
    | @Const _               n       => 0
    (*       (var)           (term var Nat) (term var Nat) (e全体 : term var Nat) *)
    | @Plus  _               e1 e2   => @countVars Nat e1 + @countVars Nat e2
    (*       (var)           (var dom -> term var ran)     (e全体 : term var (Func dom ran)) *)
    | @Abs   _     dom ran   e1      => @countVars ran (e1 tt)
    (*       (var)           (term var (Func dom ran)) (term var dom) (e全体 : term var ran) *)
    | @App   _     dom ran   e1 e2   => @countVars (Func dom ran) e1 + @countVars dom e2
    | @Let   _     t1  t2    e1 e2   => @countVars t1 e1 + @countVars t2 (e2 tt)
    end.
  (* ``e : term var t`` で受けた値を、コンストラクタで組み立てられた要素に分解する。 *)
  
(*
  Fixpoint countVars (t : type) (e : term (fun _ => unit) t) : nat :=
    match e with
    | Var _    _    => 1
    | Const    _    => 0
    | Plus    e1 e2 => countVars e1 + countVars e2
    | Abs _ _ e1    => countVars (e1 tt)
    | App _ _ e1 e2 => countVars e1 + countVars e2
    | Let _ _ e1 e2 => countVars e1 + countVars (e2 tt)
    end.
*)  
  
  (* パラメトリックに与えられる引数は、ここで追加される。 *)
  Definition CountVars (t : type) (E : Term t) := countVars (E (fun _ => unit)).
  
  Eval compute in CountVars three_the_hard_way. (* 2 *)
  (* sample *)
  Compute CountVars (fun var : type -> Type => (Abs (fun x => Var x))). (* 1 *)
  Compute CountVars (fun var : type -> Type => Const 1). (* 0 *)
  Compute CountVars (fun var : type -> Type => Plus (Const 1) (Const 1)). (* 0 *)
  Compute CountVars (fun var : type -> Type =>
                       (Abs (fun x => Plus (Const 1) (Var x)))). (* 1 *)
  Compute CountVars (fun var : type -> Type =>
                       (Abs (fun x => Plus (Plus (Const 1) (Const 2)) (Var x)))). (* 1 *)
  Compute CountVars (fun var : type -> Type =>
                       (Abs (fun x => Abs (fun y => Plus (Const 1) (Plus (Var x) (Var x)))))). (* 2 *)
  
  (** *** Pretty *)  
  
  (** 直感的には、PHOAS と任意の適切な一次表現との間で相互変換が可能です。
      次に、PHOAS 項を一次表現 (first-order) を提供する文字列に変換する、示唆に富む例を示します。

      この翻訳を実行するために、鍵となる洞察は変数に文字列を付け加えることです。
      そして、その文字列は変数の名前を伝えます。
      関数は、さらなる入力として持ち出される 次の変数 に割り当てられる名前を伝えている文字列をとります。
      We evolve this name by adding a prime to its end.
      To avoid getting bogged down in orthogonal details, we render all constants as the string ["N"].
   *)
  
  (*                                                         ↓ λの束縛変数に使う文字で、本質ではない。 *)
  Fixpoint pretty (t : type) (e : term (fun _ => string) t) (x : string) : string :=
    match e with
    (*            ↓ 型 ``var t : string`` がパターンに出てくる。 *)
    | Var _       s => s
    | Const       _ => "N"
    | Plus    e1 e2 => "(" ++ pretty e1 x ++ " + " ++ pretty e2 x ++ ")"
    | Abs _ _ e1    => "(fun " ++ x ++ " => " ++ pretty (e1 x) (x ++ "'") ++ ")"
    | App _ _ e1 e2 => "(" ++ pretty e1 x ++ " " ++ pretty e2 x ++ ")"
    | Let _ _ e1 e2 => "(let " ++ x ++ " = " ++ pretty e1 x ++ " in "
                         ++ pretty (e2 x) (x ++ "'") ++ ")"
                         (* Let の e2 は ``var t = string`` を引数に取る。 *)
    end.
  Compute pretty (three_the_hard_way (fun _ => string)) "x".

  Definition Pretty (t : type) (E : Term t) := pretty (E (fun _ => string)) "x".

  Eval compute in Pretty three_the_hard_way. (* "(((fun x => (fun x' => (x + x'))) N) N)" *)
  (* sample *)
  Compute Pretty (fun var : type -> Type => Abs (fun x => Var x)).
  Compute Pretty (fun var : type -> Type => Const 1).
  Compute Pretty (fun var : type -> Type => Plus (Const 1) (Const 1)).
  Compute Pretty (fun var : type -> Type => Abs (fun x => Plus (Const 1) (Var x))).
  Compute Pretty (fun var : type -> Type => Abs (fun x => Plus (Plus (Const 1) (Const 2)) (Var x))).
  Compute Pretty (fun var : type -> Type => Abs (fun x => Plus (Const 1) (Plus (Const 2) (Var x)))).
  
  (** *** squash *)
  
  (** Note that this function squash is parameterized over a specific var choice.
      この関数 squash は、特定の var 選択に対してパラメーター化されることに注意してください。
   *)

  Definition Term1 (t1 t2 : type) := forall (var : type -> Type), var t1 -> term var t2.
  
  Fixpoint squash (var : type -> Type) (t : type) (e : term (term var) t) : term var t :=
    match e with
    (*                 ↓↓ 型 ``var t = term var t`` がパターンに出てくる。 *)
    | @Var   _ t       v     => v   (* ``Var v`` を v に変換する。 *)
    | @Const _         n     => @Const var n
    | @Plus  _         e1 e2 => @Plus  var (squash e1) (squash e2)
    | @Abs   _ t   ran e1    => @Abs   var t ran
                                  (fun x => squash (e1 (Var x))) (* ``e1 x`` では型があわない。 *)
    | @App   _ dom ran e1 e2 => @App   var dom ran
                                  (squash  e1) (squash e2)
    | @Let   _ t1   t2 e1 e2 => @Let   var t1 t2
                                  (squash e1) (fun x => squash (e2 (Var x)))
    end.
  
  Definition Subst (t1 t2 : type) (E : Term1 t1 t2) (E' : Term t1) : Term t2 :=
    fun var => squash (E (term var) (E' var)).

  Eval compute in Subst (fun _ x => Plus (Var x) (Const 3)) three_the_hard_way.
  (* Subst をunfold してから計算する。 *)
  Compute (fun var : type -> Type => squash (Plus (Var (three_the_hard_way var)) (Const 3))).
  (* 結果 *)
  Check (fun var : type -> Type =>
           Plus
             (App
                (App
                   (Abs (fun x : var Nat => Abs (fun y : var Nat => Plus (Var x) (Var y))))
                   (Const 1))
                (Const 2))
             (Const 3))
          : forall var : type -> Type, term var Nat.
  
  (* squash の引数だけを計算する。 *)
  Compute (fun var => (Plus (Var (three_the_hard_way var)) (Const 3))).
  Check (fun var : type -> Type =>
           Plus
             (Var
                (App
                   (App
                      (Abs (fun x : var Nat => Abs (fun y : var Nat => Plus (Var x) (Var y))))
                      (Const 1))
                   (Const 2)))
             (Const 3))
    : forall var : type -> Type, term (term var) Nat.
  
  (* 結果。上記とくらべると Var の中身が取り出されたのみ。 *)
  Check (fun var : type -> Type =>
           Plus
             (App
                (App
                   (Abs (fun x : var Nat => Abs (fun y : var Nat => Plus (Var x) (Var y))))
                   (Const 1))
                (Const 2))
             (Const 3))
          : forall var : type -> Type, term var Nat.
  
  (** *** termDenote *)
  
  (** 表示的意味論を与える関数を定義できる。 *)
  
  Fixpoint termDenote (t : type) (e : term typeDenote t) : typeDenote t :=
    match e with
    (* ここで、t と e の関係をよく見ておくこと。 *)
    (*            ↓ 型 ``var t = typeDenote t`` がパターンに出てくる。 *)
    | Var _       v => v
    | Const       n => n
    | Plus    e1 e2 => termDenote e1 + termDenote e2
    | Abs _ _ e1    => fun x => termDenote (e1 x)
    | App _ _ e1 e2 => (termDenote e1) (termDenote e2)
    | Let _ _ e1 e2 => termDenote (e2 (termDenote e1))
    end.
  
  Definition TermDenote (t : type) (E : Term t) : typeDenote t := termDenote (E typeDenote).
  
  Eval compute in TermDenote three_the_hard_way. (* = 3 *)
  (* sample *)
  Compute TermDenote (fun var : type -> Type => Abs (fun (x : var Nat) => Var x)).
  Compute TermDenote (fun var : type -> Type => Const 1).
  Compute TermDenote (fun var : type -> Type => Plus (Const 1) (Const 1)).
  Compute TermDenote (fun var : type -> Type => Abs (fun (x : var Nat) => Plus (Const 1) (Var x))).
  Compute TermDenote (fun var : type -> Type => App (Abs (fun (x : var Nat) => Var x))
                                                  (Const 1)).
  
  (** 要約すると、
      PHOAS 表現はより標準的な first-order エンコーディングの表現力をすべて備えており、
      変数にデータをタグ付けするという新しい機能のおかげで、
      さまざまな変換を実際に通常よりもはるかに快適に実装できます。
   *)
  
  (** ** 17.2.2 Verifying Program Transformations *)
  
  (** *** ident *)
  
  (** 前のセクション (17.1) の 3 つのプログラム変換例をもう一度見てみましょう。
      それぞれは PHOAS で簡単に実装でき、最後のものは 1 階表現よりも大幅に簡単です。
      まず、前のサブセクションと同じパターンに従う再帰的な恒等関数があり、
      タグ選択で多態的なヘルパー関数と、選択を適切にインスタンス化する最終関数があります。
   *)
  
  Fixpoint ident (var : type -> Type) (t : type) (e : term var t) : term var t :=
    match e with
    (*         ↓ 型 ``var t = var t`` がパターンに出てくる。 *)
    | Var _    x    => Var x
    | Const    n    => Const n
    | Plus    e1 e2 => Plus (ident e1) (ident e2)
    | Abs _ _ e1    => Abs (fun x => ident (e1 x))
    | App _ _ e1 e2 => App (ident e1) (ident e2)
    | Let _ _ e1 e2 => Let (ident e1) (fun x => ident (e2 x))
    end.

  Definition Ident (t : type) (E : Term t) : Term t := fun var => ident (E var).

  (* sample *)
  Compute Ident (fun var : type -> Type => Abs (fun (x : var Nat) => Var x)).
  Compute Ident (fun var : type -> Type => Const 1).
  Compute Ident (fun var : type -> Type => Plus (Const 1) (Const 1)).
  Compute Ident (fun var : type -> Type => Abs (fun (x : var Nat) => Plus (Const 1) (Var x))).
  Compute Ident (fun var : type -> Type => App (Abs (fun (x : var Nat) => Var x))
                                             (Const 1)).
  
  Lemma identSound : forall t (e : term typeDenote t),
      termDenote (ident e) = termDenote e.
  Proof.
    Fail induction e; pl.
    
    induction e; try easy.

    - simpl.
      now rewrite IHe1, IHe2.
    - ext.
      simpl.
      now rewrite H.
    - simpl.
      now rewrite IHe1, IHe2.
    - simpl.
      now rewrite H, IHe.
  Qed.
  
  Theorem IdentSound : forall t (E : Term t),
    TermDenote (Ident E) = TermDenote E.
  Proof.
    intros; apply identSound.
  Qed.

  (** *** cfold *)
  
  (** 定数畳み込み関数の翻訳とその証明は、ほぼ同じように機能します。 *)

  Fixpoint cfold (var : type -> Type) (t : type) (e : term var t) : term var t :=
    match e with
    | Plus    e1 e2 =>
        let e1' := cfold e1 in
        let e2' := cfold e2 in
        match e1', e2' with
        | Const n1, Const n2 => Const (n1 + n2) (* Plus の引数が定数になったら、定数に置き換える。 *)
        | _, _ => Plus e1' e2'
        end
    | Abs _ _ e1    => Abs (fun x => cfold (e1 x))
    | App _ _ e1 e2 => App (cfold e1) (cfold e2)
    | Let _ _ e1 e2 => Let (cfold e1) (fun x => cfold (e2 x))
(*  | e => e *)
    (*        ↓ 型 ``var t = var t`` がパターンに出てくる。 *)
    | Var _   e     => Var e
    | Const   n     => Const n
    end.

  Definition Cfold (t : type) (E : Term t) : Term t := fun var => cfold (E var).

  (* sample *)
  Compute Cfold (fun var : type -> Type => Plus (Const 1) (Const 2)).
  Compute Cfold (fun var : type -> Type => Abs (fun x => Plus (Plus (Const 1) (Const 2)) (Var x))).
  Compute Cfold (fun var : type -> Type => Abs (fun x => Plus (Const 1) (Plus (Const 2) (Var x)))).

  Lemma cfoldSound : forall t (e : term typeDenote t),
      termDenote (cfold e) = termDenote e.
  Proof.
    Fail induction e; pl;
      repeat (match goal with
              | [ |- context[match ?E with Var _ _ _ => _ | _ => _ end] ] =>
                  dep_destruct E
              end; pl).
    
    induction e; try easy.
    - simpl.
      dep_destruct (cfold e1); dep_destruct (cfold e2);
        now rewrite <- IHe1, <- IHe2.
    - ext.
      simpl.
      now rewrite H.
    - simpl.
      now rewrite IHe1, IHe2.
    - simpl.
      now rewrite IHe.
  Qed.
  
  Theorem CfoldSound : forall t (E : Term t),
    TermDenote (Cfold E) = TermDenote E.
  Proof.
    intros; apply cfoldSound.
  Qed.
  

(** *** unlet *)

  Fixpoint unlet (var : type -> Type) (t : type) (e : term (term var) t) : term var t :=
    match e with
    (*        ↓ 型 ``var t = tarm var t`` がパターンに出てくる。 *)
    | Var _   e1    => e1
    | Const   n     => Const n
    | Plus    e1 e2 => Plus (unlet e1) (unlet e2)
    | Abs _ _ e1    => Abs (fun x => unlet (e1 (Var x)))
    | App _ _ e1 e2 => App (unlet e1) (unlet e2)
    | Let _ _ e1 e2 => unlet (e2 (unlet e1))
    end.
  
  Definition Unlet (t : type) (E : Term t) : Term t := fun var => unlet (E (term var)).
  
  Eval compute in three_the_hard_way.
  Eval compute in Unlet three_the_hard_way. (* 変化はない。 *)

  Definition three_a_harder_way : Term Nat :=
    fun _ => Let (Const 1)
               (fun x => Let (Const 2)
                           (fun y => App (App (add _) (Var x)) (Var y))).
  Eval compute in three_a_harder_way.
  Eval compute in Unlet three_a_harder_way. (* Let が消えた。 *)

  Definition three_a_harder_way' : Term Nat :=
    fun _ => Let (Const 1)
               (fun x => Let (Const 2)
                           (fun y => Plus (Var x) (Var y))).
  Eval compute in three_a_harder_way'.
  Eval compute in Unlet three_a_harder_way'. (* Let が消えた。 *)
  
  
  (** *** wf *)

  Section wf.
    Variables var1 var2 : type -> Type.
    
    Record varEntry := {
      Ty : type;
      First : var1 Ty;
      Second : var2 Ty
    }.
    
    Inductive wf : list varEntry -> forall t, term var1 t -> term var2 t -> Prop :=
    | WfVar : forall G t x x', In {| Ty := t; First := x; Second := x' |} G
      -> wf G (Var x) (Var x')

    | WfConst : forall G n, wf G (Const n) (Const n)
                               
    | WfPlus : forall G e1 e2 e1' e2', wf G e1 e1'
      -> wf G e2 e2'
      -> wf G (Plus e1 e2) (Plus e1' e2')

    | WfAbs : forall G dom ran (e1 : _ dom -> term _ ran) e1',
      (forall x1 x2, wf ({| First := x1; Second := x2 |} :: G) (e1 x1) (e1' x2))
      -> wf G (Abs e1) (Abs e1')

    | WfApp : forall G dom ran (e1 : term _ (Func dom ran)) (e2 : term _ dom) e1' e2',
      wf G e1 e1'
      -> wf G e2 e2'
      -> wf G (App e1 e2) (App e1' e2')

    | WfLet : forall G t1 t2 e1 e1' (e2 : _ t1 -> term _ t2) e2', wf G e1 e1'
      -> (forall x1 x2, wf ({| First := x1; Second := x2 |} :: G) (e2 x1) (e2' x2))
      -> wf G (Let e1 e2) (Let e1' e2').
  End wf.
  
  Definition Wf (t : type) (E : Term t) := forall var1 var2, wf nil (E var1) (E var2).
  
  Theorem three_the_hard_way_Wf : Wf three_the_hard_way.
  Proof.
    red; intros; repeat match goal with
                   | [ |- wf _ _ _ ] => constructor; intros
                   end; intuition.
  Qed.

  (*
  Hint Extern 1 => match goal with
                     | [ H1 : Forall _ _, H2 : In _ _ |- _ ] => apply (Forall_In H1 _ H2)
                   end.
   *)
  
  Lemma unletSound : forall G t (e1 : term _ t) e2,
    wf G e1 e2
    -> Forall (fun ve => termDenote (First ve) = Second ve) G
    -> termDenote (unlet e1) = termDenote e2.
  Proof.
    Fail induction 1; pl.
    induction 1.
  Admitted.
  
  Theorem UnletSound : forall t (E : Term t), Wf E
    -> TermDenote (Unlet E) = TermDenote E.
  Proof.
    intros; eapply unletSound; eauto.
  Qed.

  Hint Constructors wf.
  Hint Extern 1 (In _ _) => simpl; tauto.
(* Hint Extern 1 (Forall _ _) => eapply Forall_weaken; [ eassumption | simpl ]. *)

(** ** 17.2.3 Establishing Term Well-Formedness *)

  Lemma wf_monotone : forall var1 var2 G t (e1 : term var1 t) (e2 : term var2 t),
    wf G e1 e2
    -> forall G', Forall (fun x => In x G') G
      -> wf G' e1 e2.
  Proof.
    Fail induction 1; pl; auto 6.
  Admitted.
  
  Hint Resolve wf_monotone. (* Forall_In'. *)

  Hint Extern 1 (wf _ _ _) => progress simpl.

  Lemma unletWf : forall var1 var2 G t (e1 : term (term var1) t) (e2 : term (term var2) t),
    wf G e1 e2
    -> forall G', Forall (fun ve => wf G' (First ve) (Second ve)) G
      -> wf G' (unlet e1) (unlet e2).
  Proof.
    Fail induction 1; pl; eauto 9.
  Admitted.

  Theorem UnletWf : forall t (E : Term t), Wf E
    -> Wf (Unlet E).
  Proof.
    red; intros; apply unletWf with nil; auto.
  Qed.

(** ** 17.2.4 A Few More Remarks *)

    Infix "-->" := Func (right associativity, at level 52).

  Notation "^" := Var.
  Notation "#" := Const.
  Infix "@" := App (left associativity, at level 50).
  Infix "@+" := Plus (left associativity, at level 50).
  Notation "\ x : t , e" := (Abs (dom := t) (fun x => e))
    (no associativity, at level 51, x at level 0).
  Notation "[ e ]" := (fun _ => e).

  Example Add : Term (Nat --> Nat --> Nat) :=
    [\x : Nat, \y : Nat, ^x @+ ^y].
  Example Three_the_hard_way : Term Nat :=
    [Add _ @ #1 @ #2].
  
  Eval compute in TermDenote Three_the_hard_way.

(**
まとめ。
引数は1個 ``term var t`` または ``Term t`` であることに注意
*)
  (* ``var : type -> Type`` として与えられるものの例： *)
  Section a.
    Check [unit]          : type -> Type. (* ``fun _ => unit`` の意味 *)
    Check [string]        : type -> Type.
    (* term var も var として与えられる。 *)
    Variable var : type -> Type.
    Check term var        : type -> Type.
    Check typeDenote      : type -> Type.
  End a.

  (* ``var t : Type`` パターンマッチ ``Var _ s`` に出現する s の型の例： *)
  Section b.
    (* term var も var として与えられる。 *)
    Variable var : type -> Type.
    Variable t : type.                      (* 対象言語型 *)
    
    (*                          ____________ ← s の型 *)
    Check @Var var t          : var t                 -> term var t.
    Check @Var [unit] t       : unit                  -> term [unit] t.
    Check @Var [string] t     : string                -> term [string] t.
    Check @Var (term var) t   : term var t            -> term (term var) t.
    Check @Var typeDenote t   : typeDenote t          -> term typeDenote t.
    Check @Var typeDenote Nat : nat                   -> term typeDenote Nat.
  End b.

  (*                                                               ↓パラメトリックに与える var  *)
  Check countVars  : forall t : type,                        (term [unit]     t) -> nat.
  Check pretty     : forall t : type,                        (term [string]   t) -> string -> string.
  Check squash     : forall (var : type -> Type) (t : type), (term (term var) t) -> (term var t).
  Check termDenote : forall t : type,                        (term typeDenote t) -> (typeDenote t).
  Check ident      : forall (var : type -> Type) (t : type), (term var        t) -> (term var t).
  Check cfold      : forall (var : type -> Type) (t : type), (term var        t) -> (term var t).
  Check unlet      : forall (var : type -> Type) (t : type), (term (term var) t) -> (term var t).
  
  Check Term  : type -> Type.
  (* Term  *) Check fun t     : type => forall var : type -> Type,           term var t.
  Check Term1 : type -> type -> Type.
  (* Term1 *) Check fun t1 t2 : type => forall var : type -> Type, var t1 -> term var t2.
  
  Check CountVars  : forall t : type,                        (Term t)            -> nat.
  Check Pretty     : forall t : type,                        (Term t)            -> string.
  Check Subst      : forall t1 t2 : type, (Term1 t1 t2) -> (Term t1) -> (Term t2). (* squash *)
  Check TermDenote : forall t : type,                        (Term t)            -> (typeDenote t).
  Check Ident      : forall t : type,                        (Term t)            -> (Term t).
  Check Cfold      : forall t : type,                        (Term t)            -> (Term t).
  Check Unlet      : forall t : type,                        (Term t)            -> (Term t).
  
End HigherOrder.

(* END *)
