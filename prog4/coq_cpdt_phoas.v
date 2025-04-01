Require Import FunctionalExtensionality List. (* ext *)
Require Import Coq.Program.Equality.        (* dep_destruct E *)
Set Implicit Arguments.
Set Asymmetric Patterns.

Ltac ext := let x := fresh "x" in extensionality x.

Ltac dep_destruct E :=
  let x := fresh "x" in
  remember E as x; simpl in x; dependent destruction x;
  try match goal with
    | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
    end.

Inductive type : Type :=
| Nat : type
| Func : type -> type -> type.

Fixpoint typeDenote (t : type) : Type :=
  match t with
  | Nat => nat
  | Func t1 t2 => typeDenote t1 -> typeDenote t2
  end.

(** * 17.2 Parametric Higher-Order Abstract Syntax *)

Module HigherOrder.

  Section var.
    Variable var : type -> Type.

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

  Definition Term t := forall var, term var t. (* var : type -> Type *)
  Check term : (type -> Type) -> type -> Type.
  Check Term : type -> Type.

  Example add : Term (Func Nat (Func Nat Nat)) :=
    fun var => Abs (fun x => Abs (fun y => Plus (Var x) (Var y))).
  Example three_the_hard_way : Term Nat :=
    fun var => App (App (add var) (Const 1)) (Const 2).
  Example add' : Term (Func Nat (Func Nat Nat)) :=
    fun _ => Abs (fun x => Abs (fun y => Plus (Var x) (Var y))).
  Example three_the_hard_way' : Term Nat :=
    fun _ => App (App (add' _) (Const 1)) (Const 2).

  (** ** 17.2.1 Functional Programming with PHOAS *)

  (** *** CountVars *)

  (** This operation requires no data annotated on variables,
      so we simply annotate variables with [unit] values.
      数で注釈がついているデータを必要としない。
      
      Note that, when we go under binders in the cases for [Abs] and [Let],
      we must provide the data value to annotate on the new variable we pass beneath.
      For our current choice of [unit] data, we always pass [tt].
*)

  (* sample *)
  Module test.
    Section test.
      Variable t : type.
      
      (* 抽象型 var を与える。具体的な型は与えられない。 *)
      Variable var : type -> Type.
      Check term var t : Type.
      Check @Var var t _ : term var t.
      Check Var _ : term var t.
      
      (* e : ``term var t`` の var を具体的に与える。 *)
      Check (fun _ : type => unit) : type -> Type.
      (* ``var t`` は、上記の型に依存する。この場合 unit 型になる。 *)
      Check tt : (fun _ : type => unit) t.
      (* ``term var t`` の具体的な型は Type になる。 *)
      Check term (fun _ : type => unit) t : Type.
      (* @Var は4引数、略すと1引数である。 *)
      Check @Var (fun _ => unit) t          tt      : term (fun _ => unit) t.
      (*         (var)           (forall t) (var t) *)
      Check Var                             tt      : term (fun _ => unit) t.
      (* 次の match 式のパターンが 2引数である理由は判らない。 *)
    End test.
  End test.
  
  Fixpoint countVars (t : type) (e : term (fun _ => unit) t) : nat :=
    match e with
    | @Var   _ t        tt     => 1
    | @Const _ t               => 0
    | @Plus  _          e1 e2  => @countVars Nat e1 + @countVars Nat e2
    | @Abs   _ t   ran  e1     => @countVars ran (e1 tt)
    | @App   _ dom ran  e1 e2  => @countVars (Func dom ran) e1 + @countVars dom e2
    | @Let   _ t1  t2   e1 e2  => @countVars t1 e1 + @countVars t2 (e2 tt)
    end.
(*
  Set Prinitng All.
  Print countVars.
  
  Fixpoint countVars (t : type) (e : term (fun _ => unit) t) : nat :=
    match e with
    | Var _ _ => 1
    | Const _ => 0
    | Plus e1 e2 => countVars e1 + countVars e2
    | Abs _ _ e1 => countVars (e1 tt)
    | App _ _ e1 e2 => countVars e1 + countVars e2
    | Let _ _ e1 e2 => countVars e1 + countVars (e2 tt)
    end.
*)  
  Compute @countVars _ (three_the_hard_way (fun _ : type => unit)). (* 2 *)
  
  Definition CountVars t (E : Term t) := countVars (E (fun _ => unit)).
  
  Eval compute in CountVars three_the_hard_way. (* 2 *)
  (* sample *)
  Compute CountVars (fun var : type -> Type => Var _).
  Compute CountVars (fun var : type -> Type => Const 1).
  Compute CountVars (fun var : type -> Type => Plus (Const 1) (Const 1)).
  Compute CountVars (fun var : type -> Type => Plus (Const 1) (Var _)).
  Compute CountVars (fun var : type -> Type => Plus (Plus (Const 1) (Const 2)) (Var _)).
  Compute CountVars (fun var : type -> Type => Plus (Const 1) (Plus (Const 2) (Var _))).

  
  (** *** Pretty *)  
  
  (** 直感的には、PHOAS と任意の適切な一次表現との間で相互変換が可能です。
      次に、PHOAS 項を一次表現 (first-order) を提供する文字列に変換する、示唆に富む例を示します。

      この翻訳を実行するために、鍵となる洞察は変数に文字列を付け加えることです。
      そして、その文字列は変数の名前を伝えます。
      関数は、さらなる入力として持ち出される 次の変数 に割り当てられる名前を伝えている文字列をとります。
      We evolve this name by adding a prime to its end.
      To avoid getting bogged down in orthogonal details, we render all constants as the string ["N"].
   *)
  Require Import String.
  Open Scope string_scope.

  (* sample *)
  Module test2.
    Section test2.
      Variable t : type.
      (* e : ``term var t`` の var を具体的に与える。 *)
      Check (fun _ : type => string) : type -> Type.
      (* ``var t`` は、上記の型に依存する。この場合 string 型になる。 *)
      Check "x" : (fun _ : type => string) t.
      (* ``term var t`` の具体的な型は Type になる。 *)
      Check term (fun _ : type => string) t : Type.
      (* @Var は4引数、略すと1引数である。 *)
      Check @Var (fun _ => string) t          "x"      : term (fun _ => string) t.
      (*         (var)             (forall t) (var t) *)
      Check Var                               "x"      : term (fun _ => string) t.
    End test2.
  End test2.
  
  Fixpoint pretty (t : type) (e : term (fun _ => string) t) (x : string) : string :=
    match e with
    | Var _ s => s
    | Const _ => "N"
    | Plus e1 e2 => "(" ++ pretty e1 x ++ " + " ++ pretty e2 x ++ ")"
    | Abs _ _ e1 => "(fun " ++ x ++ " => " ++ pretty (e1 x) (x ++ "'") ++ ")"
    | App _ _ e1 e2 => "(" ++ pretty e1 x ++ " " ++ pretty e2 x ++ ")"
    | Let _ _ e1 e2 => "(let " ++ x ++ " = " ++ pretty e1 x ++ " in "
                         ++ pretty (e2 x) (x ++ "'") ++ ")"
    end.
  Compute pretty (three_the_hard_way (fun _ => string)) "x".

  Definition Pretty t (E : Term t) := pretty (E (fun _ => string)) "x".

  Eval compute in Pretty three_the_hard_way. (* "(((fun x => (fun x' => (x + x'))) N) N)" *)
  (* sample *)
  Compute Pretty (fun var : type -> Type => Var _).
  Compute Pretty (fun var : type -> Type => Const 1).
  Compute Pretty (fun var : type -> Type => Plus (Const 1) (Const 1)).
  Compute Pretty (fun var : type -> Type => Plus (Const 1) (Var _)).
  Compute Pretty (fun var : type -> Type => Plus (Plus (Const 1) (Const 2)) (Var _)).
  Compute Pretty (fun var : type -> Type => Plus (Const 1) (Plus (Const 2) (Var _))).

  (** *** squash *)
  (** Note that this function squash is parameterized over a specific var choice.
      この関数 squash は、特定の var 選択に対してパラメーター化されることに注意してください。
   *)
  
  Module test3.
    Section test3.
      Variable var : type -> Type.
      (* e : ``term var t`` の var を具体的に与える。 *)
      Check (term var).
      (* ``term var t`` の具体的な型は Type になる。 *)
      Check term (term var) Nat : Type.
      (* @Var は4引数、略すと1引数である。 *)
      Check @Var (term var) Nat        (Const 3) : term (term var) Nat.
      (*         (var)      (forall t) (var t) *)
      Check Var                        (Const 3) : term (term var) Nat.
      Check @Var (term var) Nat        (three_the_hard_way var)  : term (term var) Nat.
      Check Var                        (three_the_hard_way var)  : term (term var) Nat.
      
      Check (three_the_hard_way var) : term var Nat. (* これは既出。*)
      Check Var (three_the_hard_way var) : term (term var) Nat. (* 上記を Var の引数にとる。 *)
    End test3.
  End test3.
  
  Fixpoint squash var (t : type) (e : term (term var) t) : term var t :=
    match e with
    | Var _ e1 => e1                 (* ``Var e`` を e に変換する。 *)
    | Const n => Const n
    | Plus e1 e2 => Plus (squash e1) (squash e2)
    | Abs _ _ e1 => Abs (fun x => squash (e1 (Var x))) (* ``e1 x`` では型があわない。 *)
    | App _ _ e1 e2 => App (squash e1) (squash e2)
    | Let _ _ e1 e2 => Let (squash e1) (fun x => squash (e2 (Var x)))
    end.
  
  Definition Term1 (t1 t2 : type) := forall var, var t1 -> term var t2.
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
  
  Fixpoint termDenote t (e : term typeDenote t) : typeDenote t :=
    match e with
    | Var _ v => v
    | Const n => n
    | Plus e1 e2 => termDenote e1 + termDenote e2
    | Abs _ _ e1 => fun x => termDenote (e1 x)
    | App _ _ e1 e2 => (termDenote e1) (termDenote e2)
    | Let _ _ e1 e2 => termDenote (e2 (termDenote e1))
    end.
  
  Definition TermDenote t (E : Term t) : typeDenote t := termDenote (E typeDenote).
  
  Eval compute in TermDenote three_the_hard_way. (* = 3 *)
  (* sample *)
  Compute TermDenote (fun var : type -> Type => Var _).
  Compute TermDenote (fun var : type -> Type => Const 1).
  Compute TermDenote (fun var : type -> Type => Plus (Const 1) (Const 1)).
  Compute TermDenote (fun var : type -> Type => Plus (Const 1) (Var _)).
  Compute TermDenote (fun var : type -> Type => Plus (Plus (Const 1) (Const 2)) (Var _)).
  Compute TermDenote (fun var : type -> Type => Plus (Const 1) (Plus (Const 2) (Var _))).
  
  (* Subst をunfold してから計算する。 *)

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
  
  (* sample *)
  Check (fun var : type -> Type => Var _)                    : forall var, term var Nat.
  (* λ式のボディは term var Nat である。 *)
  Check (fun var : type -> Type => Var _)                    : Term Nat.
  Check (fun var : type -> Type => Const 1)                  : Term Nat.
  Check (fun var : type -> Type => Plus (Const 1) (Const 2)) : Term Nat.
  Check (fun var : type -> Type => Plus (Const 1) (Var _))   : Term Nat.
  Check (fun var : type -> Type => Plus (Plus (Const 1) (Const 2)) (Var _)) : Term Nat.
  Check (fun var : type -> Type => Plus (Const 1) (Plus (Const 2) (Var _))) : Term Nat.
  
  Fixpoint ident var t (e : term var t) : term var t :=
    match e with
    | Var _ x => Var x
    | Const n => Const n
    | Plus e1 e2 => Plus (ident e1) (ident e2)
    | Abs _ _ e1 => Abs (fun x => ident (e1 x))
    | App _ _ e1 e2 => App (ident e1) (ident e2)
    | Let _ _ e1 e2 => Let (ident e1) (fun x => ident (e2 x))
    end.

  Definition Ident t (E : Term t) : Term t := fun var => ident (E var).

  (* sample *)
  Compute Ident (fun var : type -> Type => Var _).
  Compute Ident (fun var : type -> Type => Const 1).
  Compute Ident (fun var : type -> Type => Plus (Const 1) (Const 1)).
  Compute Ident (fun var : type -> Type => Plus (Const 1) (Var _)).
  Compute Ident (fun var : type -> Type => Plus (Plus (Const 1) (Const 2)) (Var _)).
  Compute Ident (fun var : type -> Type => Plus (Const 1) (Plus (Const 2) (Var _))).

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

  Fixpoint cfold var t (e : term var t) : term var t :=
    match e with
    | Plus e1 e2 =>
        let e1' := cfold e1 in
        let e2' := cfold e2 in
        match e1', e2' with
        | Const n1, Const n2 => Const (n1 + n2) (* Plus の引数が定数になったら、定数に置き換える。 *)
        | _, _ => Plus e1' e2'
        end
    | Abs _ _ e1 => Abs (fun x => cfold (e1 x))
    | App _ _ e1 e2 => App (cfold e1) (cfold e2)
    | Let _ _ e1 e2 => Let (cfold e1) (fun x => cfold (e2 x))
(*  | e => e *)
    | Var _ e => Var e
    | Const n => Const n
    end.

  Definition Cfold t (E : Term t) : Term t := fun var => cfold (E var).

  (* sample *)
  Compute Cfold (fun var : type -> Type => Plus (Const 1) (Const 2)).
  Compute Cfold (fun var : type -> Type => Plus (Plus (Const 1) (Const 2)) (Var _)).
  Compute Cfold (fun var : type -> Type => Plus (Const 1) (Plus (Const 2) (Var _))).

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

  Fixpoint unlet var t (e : term (term var) t) : term var t :=
    match e with
    | Var _ e1 => e1
    | Const n => Const n
    | Plus e1 e2 => Plus (unlet e1) (unlet e2)
    | Abs _ _ e1 => Abs (fun x => unlet (e1 (Var x)))
    | App _ _ e1 e2 => App (unlet e1) (unlet e2)
    | Let _ _ e1 e2 => unlet (e2 (unlet e1))
    end.
  
  Definition Unlet t (E : Term t) : Term t := fun var => unlet (E (term var)).
  
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
  
  Definition Wf t (E : Term t) := forall var1 var2, wf nil (E var1) (E var2).
  
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
  
  Eval compute in TermDenote Three_the_hard_way. (*  *)

End HigherOrder.

(* END *)
