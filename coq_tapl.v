(*
   TAPL 第8章
   
   お茶大浅井先生・廣田先生：
   http://pllab.is.ocha.ac.jp/coq_print/nori_Coq7.pdf
   http://pllab.is.ocha.ac.jp/coq_print/nori_Coq8.pdf
   
   http://www.cs.helsinki.fi/u/lealanko/ftt09/src/typed_arith_lang.v
   http://www.cs.helsinki.fi/u/lealanko/ftt09/src/tapl_ch8.v
   
   mzpさん：
   mzp-lambda-983dc07/Progress.v
   mzp-lambda-983dc07/Progress.v
   ただし、tm_pred があると難しいので、削除している。
   *)   


(* term *)
Inductive term : Set :=
| tm_true  : term 
| tm_false : term
| tm_if    : term -> term -> term -> term
| tm_zero  : term
| tm_succ  : term -> term
(* | tm_pred  : term -> term *)
| tm_iszero : term -> term.


(* type *)
Inductive type : Set :=
| TyBool
| TyNat.


(* value *)
Inductive is_bv : term -> Prop :=
| is_bv_true  : is_bv tm_true
| is_bv_false : is_bv tm_false.


Inductive is_nv : term -> Prop :=
| is_nv_0    : is_nv tm_zero
| is_nv_succ : forall nv,
  is_nv nv -> is_nv (tm_succ nv).


Inductive is_value : term -> Prop :=
| is_value_bv : forall t,
  is_bv t -> is_value t
| is_value_nv : forall t,
  is_nv t -> is_value t.


(* evaluation rule *)
Inductive eval : term -> term -> Prop :=
| e_iftrue     : forall t2 t3,
  eval (tm_if tm_true  t2 t3) t2
| e_iffalse    : forall t2 t3,
  eval (tm_if tm_false t2 t3) t3
| e_if         : forall t1 t1' t2 t3,
  eval t1 t1' ->
  eval (tm_if t1 t2 t3) (tm_if t1' t2 t3)
| e_succ       : forall t t',
  eval t t' ->
  eval (tm_succ t) (tm_succ t')
(*
   | e_predzero   : eval (tm_pred tm_zero) tm_zero
   | e_predsucc   : forall nv,
   eval (tm_pred (tm_succ nv)) nv
   | e_pred       : forall t t',
   eval t t' ->
   eval (tm_pred t) (tm_pred t')
*)
| e_iszerozero : eval (tm_iszero tm_zero) tm_true
| e_iszerosucc : forall nv,
  eval (tm_iszero (tm_succ nv)) tm_false
| e_iszero     : forall t t',
  eval t t' ->
  eval (tm_iszero t) (tm_iszero t').
Hint Constructors eval : evaluator.


(* typing rule *)
Inductive typing : term -> type -> Prop :=
| typing_true  : typing tm_true  TyBool
| typing_false : typing tm_false TyBool
| typing_if    : forall t1 t2 t3 T,
  typing t1 TyBool ->
  typing t2 T ->
  typing t3 T ->
  (typing (tm_if t1 t2 t3) T)
| typing_zero  : typing tm_zero TyNat
| typing_succ  : forall t,
  typing t TyNat -> typing (tm_succ t) TyNat
| typing_iszero: forall t,
  typing t TyNat -> typing (tm_iszero t) TyBool.
Hint Constructors typing : type_checker.
Notation "A ~: B" := (typing A B) (at level 85).


 (*
    t がnv ならば、
    (tm_succ (tm_pred (tm_succ t))) は
    (tm_succ t) へと簡約できる。


    Lemma eval_succ_pred_succ : forall t,
    is_nv t ->
    eval (tm_succ (tm_pred (tm_succ t))) (tm_succ t).
    Proof.
    info auto with evaluator.
    Qed.
*) 


(*
   t がnv ならば、t はTyNat 型を持つ。
*)
Lemma type_nvalue :
  forall t, is_nv t -> t ~: TyNat.
Proof.
  intros t Hnv.
  induction Hnv.
  auto with type_checker.
  auto with type_checker.
Qed.


(*
   (tm_if t1 t2 t3) がT 型を持つなら、
   t1 はTyBool 型を持ち、t2 はT 型を持ち、t3 はT 型を持つ。
*)
Lemma type_if :
  forall t1 t2 t3 T,
    ((tm_if t1 t2 t3) ~: T) -> (t1 ~: TyBool) -> t2 ~: T -> t3 ~: T.
Proof.
  intros.
  inversion H.
  apply H8.
Qed.


(*
   もし t が TyBool 型を持つ value であるならば、
   t は tm_true 又は tm_falseのどちらかである。
*)


Lemma canonical_forms_TyBool :
  forall t : term, (is_value t /\ (t ~: TyBool)) -> is_bv t.
Proof.
  intros t H.


  destruct H as [H1 H2].
  inversion H1.                             (* H1 : is_value t *)
  auto.
  
  inversion H.
  rewrite <- H3 in H2.
  inversion H2.


  rewrite <- H4 in H2.
  inversion H2.
Qed.


Lemma canonical_forms_TyBool' :
  forall t : term, (is_value t /\ (t ~: TyBool)) -> is_bv t.
Proof.
  intros t H.


  destruct H as [H1 H2].
  inversion H2.                             (* H2 : t ~: TyBool *)
  apply is_bv_true.
  apply is_bv_false.
  
  rewrite <- H4 in H1.
  inversion H1.
  apply H6.
Abort.


(*
   もし t が TyNat 型を持つ value である
   ならば、t は nv である。
   *)


Lemma canonical_forms_TyNat :
  forall t : term, (is_value t /\ (t ~: TyNat)) -> is_nv t.
Proof.
  intros t H.
  destruct H as [H1 H2].
  inversion H1.                             (* H1: is_value t *)


  inversion H.
  rewrite <- H3 in H2.
  inversion H2.


  rewrite <- H3 in H2.
  inversion H2.
  
  apply H.
Qed.


(*
   preservation:
   well-typed termはstuckではない。
   
   もしterm t がT という型を持ち（つまりt ~: T であり）、
   t はt' へと評価出来る（t --> t'）ならば、t' はT 型を持つ（t' ~: T）。
*)


Theorem preservation :
  forall (t t' : term) (T : type),
    (t ~: T) -> eval t t' -> (t' ~: T).
Proof.
(* Tを固定しないように、introsの前にinductionする。*)
  induction t.
  
(* True *)
  intros t' T t_T tEt'.
  inversion tEt'.


(* False *)
  intros t' T t_T tEt'.
  inversion tEt'.


(* IF *)
  intros t' T t_T tEt'.
  inversion t_T.
  inversion tEt'.
  subst.
  assumption.
  subst.
  assumption.
  Check (typing_if t1' t2 t3).
  apply (typing_if t1' t2 t3).
  Check (IHt1 t1' TyBool).                  (* これのために、forallを残しておく。*)
  apply (IHt1 t1' TyBool).
  assumption.
  assumption.
  assumption.
  assumption.


(* Number *)
  intros t' T t_T tEt'.
  inversion tEt'.


  intros t' T t_T tEt'.
  inversion t_T.
  inversion tEt'.
  Check typing_succ.
  apply typing_succ.
  apply (IHt t'0 TyNat).
  assumption.
  assumption.


  intros t' T t_T tEt'.
  inversion t_T.
  inversion tEt'.
  apply typing_true.
  apply typing_false.
  apply typing_iszero.


  subst.
  apply IHt.
  assumption.
  assumption.
Qed.


(*
   progress:
   もしwell-typed termがさらに評価出来
   るならば、評価後のtermもwell-typedで
   ある。
   
   term t が T という型を持つならば（つまりt ~: Tならば）、
   tはvalueであるか、又はt --> t’を満たすt’が存在するか
   のどちらかである。
*)


(* is_bv があると、本体側の証明が煩瑣になるので *)
Axiom bool_can :                            (* XXXXX *)
  forall t, (* is_bv t -> *) (t = tm_true \/ t = tm_false).
Lemma bool_can' :
  forall t, is_bv t -> (t = tm_true \/ t = tm_false).
Proof.
  intros.
  inversion H.
  left.
  reflexivity.
  right.
  reflexivity.
Qed.


(* 以下の仮定は、あってしかるべきだと思うが *)
Axiom eval_can : forall t, (eval t t).


Theorem progress : forall t T,
  (t ~: T) -> (is_value t) \/ (exists t', eval t t').
Proof.
  induction t.
  intros.
  inversion H.
  left; apply is_value_bv; apply is_bv_true.
  left; apply is_value_bv; apply is_bv_false.


  (* IF *)
  intros.
  right.
  inversion H.
  generalize H3, H5, H6.
  apply IHt1 in H3.
  apply IHt2 in H5.
  apply IHt3 in H6.
  intros.
  inversion H3.
  assert (t1 = tm_true \/ t1 = tm_false).   (* XXXXXXXXX *)
  apply bool_can.                           (* XXXXXXXXX *)
  
  inversion H11.
  subst.
  exists t2.
  apply e_iftrue.
  subst.
  exists t3.
  apply e_iffalse.


  subst.
  decompose [ex] H10.
  exists (tm_if x t2 t3).
  apply e_if.
  assumption.


  (* SUCC *)
  intros.
  left; apply is_value_nv; apply is_nv_0.
  right.
  inversion H.
  generalize H1.
  apply IHt in H1.
  intros.
  inversion H1.
  
  (* is_value t *)
  assert (eval t t).                        (* XXXXXXXXX *)
  apply eval_can.
  exists (tm_succ t).
  apply (e_succ t).
  apply H5.


  (* (exists t' : term, eval t t')  *)
  decompose [ex] H1.
  assert (eval t t).                        (* XXXXXXXXX *)
  apply eval_can.
  exists (tm_succ t).
  apply (e_succ t).
  apply H5.
  
  (* ISZERO *)
  intros.
  right.
  exists (tm_iszero t).
  apply e_iszero.
  assert (eval t t).                        (* XXXXXXXXX *)
  apply eval_can.
  apply H0.
Qed.


(* END *)