From mathcomp Require Import all_ssreflect.
Require Import ssrinv.

(** MiniML *)

Section MiniML.
  
  Inductive Literal := A | B | C | F | G | H | X | Y | Z.
  
  Definition eqLiteral (x y : Literal) :=
    match (x, y) with
    | (A, A) => true
    | (B, B) => true
    | (C, C) => true
    | (F, F) => true
    | (G, G) => true
    | (H, H) => true
    | (X, X) => true
    | (Y, Y) => true
    | (Z, Z) => true
    | _ => false
    end.
  
  Lemma Literal_eqP (x y : Literal) : reflect (x = y) (eqLiteral x y).
  Proof.
    rewrite /eqLiteral.
      by apply: (iffP idP); case: x; case: y.
  Qed.
  
  Definition Literal_eqMixin := EqMixin Literal_eqP.
  Canonical Literal_eqType := EqType Literal Literal_eqMixin.
  
  (** variables *)
  Definition Var := Literal.
  
  (** MiniML abstract syntax *)
  Inductive MML_exp : Set :=
  | eNat (n : nat)
  | eBool (b : bool)
  | ePlus (t1 t2 : MML_exp)
  | eMinus (t1 e2 : MML_exp)
  | eTimes (t1 e2 : MML_exp)
  | eEq (t1 e2 : MML_exp)
  | eVar (v : Var)
  | eLet (v : Var) (t1 e2 : MML_exp)
  | eIf (t1 e2 e3 : MML_exp)
  | eLam (v : Var) (e : MML_exp)
  | eMuLam (f : Var) (v : Var) (e : MML_exp)
  | eApp (t1 e2 : MML_exp).
  
  (** values *)
  Inductive MML_val : Set :=
  | uNat (n : nat)
  | uBool (b : bool)
  | uClos (v : Var) (e : MML_exp) (g : seq (Var * MML_val))
  | uClosRec (f : Var) (v : Var) (e : MML_exp) (g : seq (Var * MML_val)).
  
  (** environments *)
  Definition MML_env := (seq (Var * MML_val)).
  Fixpoint lookup (x : Var) (g : MML_env) : MML_val :=
    match g with
    | (x', v) :: g' => if (x' == x) then v else lookup x g'
    | _ => uBool false
    end.
  
  (** The natural semantics of MiniML *)
  Inductive MML_NS : MML_env -> MML_exp -> MML_val -> Prop :=
  | MML_NS_Nat   (g : MML_env) (n : nat) : MML_NS g (eNat n) (uNat n)
  | MML_NS_Bool  (g : MML_env) (b : bool) : MML_NS g (eBool b) (uBool b)
  | MML_NS_Plus  (g : MML_env) (t1 t2 : MML_exp) (m n : nat) :
      MML_NS g t1 (uNat m) ->
      MML_NS g t2 (uNat n) ->
      MML_NS g (ePlus t1 t2) (uNat (m + n))
  | MML_NS_Minus (g : MML_env) (t1 t2 : MML_exp) (m n : nat) :
      MML_NS g t1 (uNat m) ->
      MML_NS g t2 (uNat n) ->
      MML_NS g (eMinus t1 t2) (uNat (m - n))
  | MML_NS_Times (g : MML_env) (t1 t2 : MML_exp) (m n : nat) :
      MML_NS g t1 (uNat m) ->
      MML_NS g t2 (uNat n) ->
      MML_NS g (eTimes t1 t2) (uNat (m * n))
  | MML_NS_Eq    (g : MML_env) (t1 t2 : MML_exp) (m n : nat) :
      MML_NS g t1 (uNat m) ->
      MML_NS g t2 (uNat n) ->
      MML_NS g (eEq t1 t2) (uBool (m == n))
  | MML_NS_Var   (g : MML_env) (x : Var) :
      MML_NS g (eVar x) (lookup x g)
  | MML_NS_Let   (g : MML_env) (x : Var) (t1 t2 : MML_exp) (u1 u2 : MML_val) :
      MML_NS g t1 u1 ->
      MML_NS ((x, u1) :: g) t2 u2 ->
      MML_NS g (eLet x t1 t2) u2
  | MML_NS_Iftrue (g : MML_env) (t1 t2 e3 : MML_exp) (u2 : MML_val) :
      MML_NS g t1 (uBool true) ->
      MML_NS g t2 u2 ->
      MML_NS g (eIf t1 t2 e3) u2
  | MML_NS_Iffalse (g : MML_env) (t1 t2 e3 : MML_exp) (u3 : MML_val) :
      MML_NS g t1 (uBool false) ->
      MML_NS g e3 u3 ->
      MML_NS g (eIf t1 t2 e3) u3
  | MML_NS_Lam   (g : MML_env) (x : Var) (e : MML_exp) :
      MML_NS g (eLam x e) (uClos x e g)
  | MML_NS_MuLam (g : MML_env) (f : Var) (x : Var) (e : MML_exp) :
      MML_NS g (eMuLam f x e) (uClosRec f x e g)
  | MML_NS_App (g g1 : MML_env) (x : Var) (t1 t2 e : MML_exp) (u2 u : MML_val) :
     MML_NS g t1 (uClos x e g1) ->
      MML_NS g t2 u2 ->
      MML_NS ((x, u2) :: g1) e u ->
      MML_NS g (eApp t1 t2) u
  | MML_NS_AppRec (g g1 : MML_env) (x f : Var) (t1 t2 e : MML_exp) (u2 u : MML_val) :
      MML_NS g t1 (uClosRec f x e g1) ->
      MML_NS g t2 u2 ->
      MML_NS ((x, u2) :: (f, (uClosRec f x e g1)) :: g1) e u ->
      MML_NS g (eApp t1 t2) u.
  
End MiniML.

(** de Bruijn notation MiniMLdB *)

Section MiniMLdB.
  
  (** MiniMLdB abstract syntax *)
  Inductive MML_dB_exp : Set :=
  | dNat (n : nat)
  | dBool (b : bool)
  | dPlus (d1 d2 : MML_dB_exp)
  | dMinus (d1 d2 : MML_dB_exp)
  | dTimes (d1 d2 : MML_dB_exp)
  | dEq (d1 d2 : MML_dB_exp)
  | dVar (i : nat)
  | dLet (d1 d2 : MML_dB_exp)
  | dIf (d1 d2 d3 : MML_dB_exp)
  | dLam (d : MML_dB_exp)
  | dMuLam (d : MML_dB_exp)
  | dApp (d1 d2 : MML_dB_exp).
  
  (** nameless values *)
  Inductive MML_dB_val : Set :=
  | vNat (n : nat)
  | vBool (b : bool)
  | vClos (d : MML_dB_exp) (o : seq MML_dB_val)
  | vClosRec (d : MML_dB_exp) (o : seq MML_dB_val).
  
  (** nameless environments *)
  Definition MML_dB_env := (seq MML_dB_val).
  Definition olookup (i : nat) (o : MML_dB_env) := nth (vBool false) o i.
  
  (** The natural semantics of MiniMLdB *)
  Inductive MML_dB_NS : MML_dB_env -> MML_dB_exp -> MML_dB_val -> Prop :=
  | MML_dB_NS_Nat   (o : MML_dB_env) (n : nat) : MML_dB_NS o (dNat n) (vNat n)
  | MML_dB_NS_Bool  (o : MML_dB_env) (b : bool) : MML_dB_NS o (dBool b) (vBool b)
  | MML_dB_NS_Plus  (o : MML_dB_env) (d1 d2 : MML_dB_exp) (m n : nat) :
      MML_dB_NS o d1 (vNat m) ->
      MML_dB_NS o d2 (vNat n) ->
      MML_dB_NS o (dPlus d1 d2) (vNat (m + n))
  | MML_dB_NS_Minus (o : MML_dB_env) (d1 d2 : MML_dB_exp) (m n : nat) :
      MML_dB_NS o d1 (vNat m) ->
      MML_dB_NS o d2 (vNat n) ->
      MML_dB_NS o (dMinus d1 d2) (vNat (m - n))
  | MML_dB_NS_Times (o : MML_dB_env) (d1 d2 : MML_dB_exp) (m n : nat) :
      MML_dB_NS o d1 (vNat m) ->
      MML_dB_NS o d2 (vNat n) ->
      MML_dB_NS o (dTimes d1 d2) (vNat (m * n))
  | MML_dB_NS_Eq    (o : MML_dB_env) (d1 d2 : MML_dB_exp) (m n : nat) :
      MML_dB_NS o d1 (vNat m) ->
      MML_dB_NS o d2 (vNat n) ->
      MML_dB_NS o (dEq    d1 d2) (vBool (m == n))
  | MML_dB_NS_Var   (o : MML_dB_env) (i : nat) :
      MML_dB_NS o (dVar i) (olookup i o)
  | MML_dB_NS_Let   (o : MML_dB_env) (d1 d2 : MML_dB_exp) (v1 v2 : MML_dB_val) :
      MML_dB_NS o d1 v1 ->
      MML_dB_NS (v1 :: o) d2 v2 ->
      MML_dB_NS o (dLet   d1 d2) v2
  | MML_dB_NS_Iftrue (o : MML_dB_env) (d1 d2 d3 : MML_dB_exp) (v2 : MML_dB_val) :
      MML_dB_NS o d1 (vBool true) ->
      MML_dB_NS o d2 v2 ->
      MML_dB_NS o (dIf d1 d2 d3) v2
  | MML_dB_NS_Iffalse (o : MML_dB_env) (d1 d2 d3 : MML_dB_exp) (v3 : MML_dB_val) :
      MML_dB_NS o d1 (vBool false) ->
      MML_dB_NS o d3 v3 ->
      MML_dB_NS o (dIf d1 d2 d3) v3
  | MML_dB_NS_Lam   (o : MML_dB_env) (d : MML_dB_exp) :
      MML_dB_NS o (dLam d) (vClos d o)
  | MML_dB_NS_MuLam (o : MML_dB_env) (d : MML_dB_exp) :
      MML_dB_NS o (dMuLam d) (vClosRec d o)
  | MML_dB_NS_App (o o1 : MML_dB_env) (d1 d2 d : MML_dB_exp) (v2 v : MML_dB_val) :
      MML_dB_NS o d1 (vClos d o1) ->
      MML_dB_NS o d2 v2 ->
      MML_dB_NS (v2 :: o1) d v ->
      MML_dB_NS o (dApp d1 d2) v
  | MML_dB_NS_AppRec (o o1 : MML_dB_env) (d1 d2 d : MML_dB_exp) (v2 v : MML_dB_val) :
      MML_dB_NS o d1 (vClosRec d o1) ->
      MML_dB_NS o d2 v2 ->
      MML_dB_NS (v2 :: (vClosRec d o1) :: o1) d v ->
      MML_dB_NS o (dApp d1 d2) v.
  
  (* translation MiniML to MinMLdB *)
  Definition ctx := seq Var.
  
  Inductive dB_translation_NS : ctx -> MML_exp -> MML_dB_exp -> Prop :=
  | dB_translation_NS_Nat   (p : ctx) (n : nat) : dB_translation_NS p (eNat n) (dNat n)
  | dB_translation_NS_Bool  (p : ctx) (b : bool) : dB_translation_NS p (eBool b) (dBool b)
  | dB_translation_NS_Plus  (p : ctx) (t1 t2 : MML_exp) (d1 d2 : MML_dB_exp) :
      dB_translation_NS p t1 d1 ->
      dB_translation_NS p t2 d2 ->
      dB_translation_NS p (ePlus t1 t2) (dPlus d1 d2)
  | dB_translation_NS_Minus (p : ctx) (t1 t2 : MML_exp) (d1 d2 : MML_dB_exp) :
      dB_translation_NS p t1 d1 ->
      dB_translation_NS p t2 d2 ->
      dB_translation_NS p (eMinus t1 t2) (dMinus d1 d2)
  | dB_translation_NS_Times (p : ctx) (t1 t2 : MML_exp) (d1 d2 : MML_dB_exp) :
      dB_translation_NS p t1 d1 ->
      dB_translation_NS p t2 d2 ->
      dB_translation_NS p (eTimes t1 t2) (dTimes d1 d2)
  | dB_translation_NS_Var   (p : ctx) (x : Var) :
      dB_translation_NS p (eVar x) (dVar (index x p))
  | dB_translation_NS_Let   (p : ctx) (x : Var) (t1 t2 : MML_exp) (d1 d2 : MML_dB_exp) :
      dB_translation_NS p t1 d1 ->
      dB_translation_NS (x :: p) t2 d2 ->
      dB_translation_NS p (eLet x t1 t2) (dLet d1 d2)
  | dB_translation_NS_If    (p : ctx) (t1 t2 t3 : MML_exp) (d1 d2 d3 : MML_dB_exp) :
      dB_translation_NS p t1 d1 ->
      dB_translation_NS p t2 d2 ->
      dB_translation_NS p t3 d3 ->
      dB_translation_NS p (eIf t1 t2 t3) (dIf d1 d2 d3)
  | dB_translation_NS_Lam   (p : ctx) (x : Var) (e : MML_exp) (d : MML_dB_exp) :
      dB_translation_NS (x :: p) e d ->
      dB_translation_NS p (eLam x e) (dLam d)
  | dB_translation_NS_MuLam (p : ctx) (f x : Var) (e : MML_exp) (d : MML_dB_exp) :
      dB_translation_NS (x :: f :: p) e d ->
      dB_translation_NS p (eMuLam f x e) (dMuLam d)
  | dB_translation_NS_App   (p : ctx) (t1 t2 : MML_exp) (d1 d2 : MML_dB_exp) :
      dB_translation_NS p t1 d1 ->
      dB_translation_NS p t2 d2 ->
      dB_translation_NS p (eApp t1 t2) (dApp d1 d2).

  (* g から変数だけ取り出す。 *)
  Definition mkctx (g : MML_env) : ctx := [seq fst xv | xv <- g].
  Compute mkctx [:: (X, uNat 1); (Y, uNat 2); (Z, uNat 3)].
  (* ==> [:: X; Y; Z] *)

  Inductive dB_translation_NS_val : MML_val -> MML_dB_val -> Prop :=
  | dB_translation_NS_val_Nat  (n : nat) : dB_translation_NS_val (uNat n) (vNat n)
  | dB_translation_NS_val_Bool (b : bool) : dB_translation_NS_val (uBool b) (vBool b)
  | db_translation_NS_val_Clos (x : Var) (e : MML_exp) (g : MML_env)
                               (d : MML_dB_exp) (o : MML_dB_env) :
      dB_translation_NS_env g o ->
      dB_translation_NS (x :: (mkctx g)) e d ->
      dB_translation_NS_val (uClos x e g) (vClos d o)
  | db_translation_NS_val_ClosRec (f x : Var) (e : MML_exp) (g : MML_env)
                               (d : MML_dB_exp) (o : MML_dB_env) :
      dB_translation_NS_env g o ->
      dB_translation_NS (x :: f :: (mkctx g)) e d ->
      dB_translation_NS_val (uClosRec f x e g) (vClosRec d o)
                            
  with dB_translation_NS_env : MML_env -> MML_dB_env -> Prop :=
       | dB_translation_NS_env_all (g : MML_env) (o : MML_dB_env) :
           (forall (x : Var),
               dB_translation_NS_val (lookup x g) (olookup (index x (mkctx g)) o)) ->
           dB_translation_NS_env g o.
  
  Lemma dB_translation_NS_env_cons (x : Var) (v : MML_val) (g : MML_env)
        (vd : MML_dB_val) (o : MML_dB_env) :
    dB_translation_NS_env g o ->
    dB_translation_NS_val v vd ->
    dB_translation_NS_env ((x, v) :: g) (vd :: o).
  Proof.
    move=> He Hv.
    apply: dB_translation_NS_env_all.
    inv: He => H0 x0.
    case H: (x == x0); by rewrite /= H /=.
  Qed.
  
End MiniMLdB.

Section Modern_SECD.
  
  Inductive MSECD_Instr : Set :=
  | iNat (n : nat)
  | iBool (b : bool)
  | iAdd
  | iSub
  | iMul
  | iEq
  | iAcc (i : nat)
  | iLet
  | iEndLet
  | iSel (c1 c2 : seq MSECD_Instr)
  | iJoin
  | iClos (c : seq MSECD_Instr)
  | iClosRec (c : seq MSECD_Instr)
  | iApp
  | iRet.
  Definition MSECD_Code := seq MSECD_Instr.
  
  Inductive MSECD_Val : Set :=
  | mNat (n : nat)
  | mBool (b : bool)
  | mClos (c : MSECD_Code) (e : seq MSECD_Val)
  | mClosRec (c : MSECD_Code) (e : seq MSECD_Val).
  Definition MSECD_Env := seq MSECD_Val.
  
  Definition elookup (i : nat) (e : MSECD_Env) := nth (mBool false) e i.
  
  Inductive MSECD_SVal : Set :=
  | V (m : MSECD_Val)                       (* Machine Value *)
  | S (s : MSECD_Code * MSECD_Env).         (* Stack Frame *)
  Definition MSECD_Stack := seq MSECD_SVal.

  (* C/E/S *)
  Definition conf := (MSECD_Code * MSECD_Env * MSECD_Stack)%type.
  
  Inductive MSECD_SS : conf -> conf -> Prop :=
  | MSECD_SS_Nat  n c e s :
      MSECD_SS ( iNat n :: c,       e,                              s)
               (           c,       e,                 V(mNat n) :: s)
  | MSECD_SS_Bool b c e s :
      MSECD_SS (iBool b :: c,       e,                              s)
               (           c,       e,                V(mBool b) :: s)
  | MSECD_SS_Add  m n c e s :
      MSECD_SS (   iAdd :: c,       e,    V(mNat n) :: V(mNat m) :: s)
               (           c,       e,           V(mNat (m + n)) :: s)
  | MSECD_SS_Sub  m n c e s :
      MSECD_SS (   iSub :: c,       e,    V(mNat n) :: V(mNat m) :: s)
               (           c,       e,           V(mNat (m - n)) :: s)  
  | MSECD_SS_Mul  m n c e s :
      MSECD_SS (   iMul :: c,       e,    V(mNat n) :: V(mNat m) :: s)
               (           c,       e,           V(mNat (m * n)) :: s)
  | MSECD_SS_Eq   m n c e s :
      MSECD_SS (    iEq :: c,       e,    V(mNat n) :: V(mNat m) :: s)
               (           c,       e,         V(mBool (m == n)) :: s)
  | MSECD_SS_Acc  i c e s :
      MSECD_SS ( iAcc i :: c,       e,                              s)
               (           c,       e,            V(elookup i e) :: s)
  | MSECD_SS_Let  m c e s :
      MSECD_SS (   iLet :: c,       e,                      V(m) :: s)
               (           c,  m :: e,                              s)
  | MSECD_SS_EndLet m c e s :
      MSECD_SS (iEndLet :: c,  m :: e,                              s)
               (           c,       e,                              s)
  | MSECD_SS_Seltrue c1 c2 c3 e s :
      MSECD_SS (iSel c2 c3 :: c1,   e,             V(mBool true) :: s)
               (          c2,       e,               S(c1, [::]) :: s)
  | MSECD_SS_Selfalse c1 c2 c3 e s :
      MSECD_SS (iSel c2 c3 :: c1,   e,            V(mBool false) :: s)
               (          c3,       e,               S(c1, [::]) :: s)
  | MSECD_SS_Join m c1 c2 e1 e2 s :
      MSECD_SS ( iJoin :: c1,      e1,         V(m) :: S(c2, e2) :: s) (* e2 捨てる *)
               (          c2,      e1,                      V(m) :: s)
  | MSECD_SS_Clos c1 c2 e1 s :
      MSECD_SS (iClos c2 :: c1,    e1,                              s)
               (          c1,      e1,            V(mClos c2 e1) :: s)
  | MSECD_SS_ClosRec c1 c2 e1 s :
      MSECD_SS (iClosRec c2 :: c1, e1,                              s)
               (          c1,      e1,         V(mClosRec c2 e1) :: s)
  | MSECD_SS_App m c1 c2 e1 e2 s :
      MSECD_SS (  iApp :: c1,     e1,     V(m) :: V(mClos c2 e2) :: s)
               (          c2, m :: e2,                 S(c1, e1) :: s)
  | MSECD_SS_AppRec m c1 c2 e1 e2 s :
      MSECD_SS (  iApp :: c1,       e1, V(m) :: V(mClosRec c2 e2) :: s)
               (          c2,
            m :: mClosRec c2 e2 :: e2,                 S(c1, e1) :: s)
  | MSECD_SS_Ret m c1 c2 e1 e2 s :
      MSECD_SS (  iRet :: c1,     e1,          V(m) :: S(c2, e2) :: s)
               (          c2,     e2,                       V(m) :: s).
  
  Definition relation (X : Type) := X -> X -> Prop.  
  
  Inductive refl_step_closure {X : Type} (R : relation X)  : X -> X -> Prop :=
  | rsc_refl  : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X), R x y ->
                                   refl_step_closure R y z ->
                                   refl_step_closure R x z.
  
  Lemma rsc_R : forall {X : Type} (R : relation X) (x y : X),
      R x y -> refl_step_closure R x y.
  Proof.
    intros X R x y r.
    apply rsc_step with y.
    apply r.
    by apply rsc_refl.
  Qed.
  
  Lemma rsc_trans : forall {X : Type} (R : relation X) (x y z : X),
      refl_step_closure R x y ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
  Proof.
    intros X R x y z.
    intros HRxy HRyz.
    induction HRxy as [|z' x y Rxy].
    - by apply HRyz.
    - apply (rsc_step R z' x z).
      apply Rxy.
      apply IHHRxy.
      by apply HRyz.
  Qed.
  
  Definition RTC_MSECD_SS := refl_step_closure MSECD_SS.
  
  (* RTC_MSECD_SS_Reflexivity *)
  Definition RTC_MSECD_SS_Refl (cf : conf) := rsc_refl MSECD_SS cf.
  
  (* RTC_MSECD_SS_Transitivity *)
  Definition RTC_MSECD_SS_Step (cf1 cf2 cf3 : conf) :=
    rsc_step MSECD_SS cf1 cf2 cf3.
  
  Definition RTC_MSECD_SS_Trans (cf1 cf2 cf3 : conf) :=
    rsc_trans MSECD_SS cf1 cf2 cf3.
  
End Modern_SECD.

Section Compiler.

  Inductive Compiler_SS : MML_dB_exp -> MSECD_Code -> Prop :=
  | Compiler_SS_Nat n  : Compiler_SS (dNat n) [:: (iNat n)]
  | Compiler_SS_Bool b : Compiler_SS (dBool b) [:: (iBool b)]
  | Compiler_SS_Plus d1 d2 c1 c2 :
      Compiler_SS d1 c1 ->
      Compiler_SS d2 c2 ->
      Compiler_SS (dPlus d1 d2) (c1 ++ c2 ++ [:: iAdd])
  | Compiler_SS_Minus d1 d2 c1 c2 :
      Compiler_SS d1 c1 ->
      Compiler_SS d2 c2 ->
      Compiler_SS (dMinus d1 d2) (c1 ++ c2 ++ [:: iSub])
  | Compiler_SS_Times d1 d2 c1 c2 :
      Compiler_SS d1 c1 ->
      Compiler_SS d2 c2 ->
      Compiler_SS (dTimes d1 d2) (c1 ++ c2 ++ [:: iMul])
  | Compiler_SS_Eq d1 d2 c1 c2 :
      Compiler_SS d1 c1 ->
      Compiler_SS d2 c2 ->
      Compiler_SS (dEq d1 d2) (c1 ++ c2 ++ [:: iEq])
  | Compiler_SS_Var i  : Compiler_SS (dVar i) [:: (iAcc i)]
  | Compiler_SS_Let d1 d2 c1 c2 :
      Compiler_SS d1 c1 ->
      Compiler_SS d2 c2 ->
      Compiler_SS (dLet d1 d2) (c1 ++ [:: iLet] ++ c2 ++ [:: iEndLet])
  | Compiler_SS_If d1 d2 d3 c1 c2 c3 :
      Compiler_SS d1 c1 ->
      Compiler_SS d2 c2 ->
      Compiler_SS d3 c3 ->
      Compiler_SS (dIf d1 d2 d3) (c1 ++ [:: iSel (c2 ++ [:: iJoin]) (c3 ++ [:: iJoin])])
  | Compiler_SS_Lam d c :
      Compiler_SS d c ->
      Compiler_SS (dLam d) ([:: iClos (c ++ [:: iRet])])
  | Compiler_SS_MuLam d c :
      Compiler_SS d c ->
      Compiler_SS (dMuLam d) ([:: iClosRec (c ++ [:: iRet])])
  | Compiler_SS_App d1 d2 c1 c2 :
      Compiler_SS d1 c1 ->
      Compiler_SS d2 c2 ->
      Compiler_SS (dApp d1 d2) (c1 ++ c2 ++ [:: iApp]).

  Inductive Compiler_SS_val : MML_dB_val -> MSECD_Val -> Prop :=
  | Compiler_SS_val_Nat n  : Compiler_SS_val (vNat n) (mNat n)
  | Compiler_SS_val_Bool n : Compiler_SS_val (vBool n) (mBool n)
  | Compiler_SS_val_Clos d o c e :
      Compiler_SS d c ->
      Compiler_SS_env o e ->
      Compiler_SS_val (vClos d o) (mClos (c ++ [:: iRet]) e)
  | Compiler_SS_val_ClosRec d o c e :
      Compiler_SS d c ->
      Compiler_SS_env o e ->
      Compiler_SS_val (vClosRec d o) (mClosRec (c ++ [:: iRet]) e)
                      
  with Compiler_SS_env : MML_dB_env -> MSECD_Env -> Prop :=
       | Compiler_SS_env_all o e :
           (forall i, Compiler_SS_val (olookup i o) (elookup i e)) ->
           Compiler_SS_env o e.
  
  Lemma Compiler_SS_env_cons v o' m1 e :
    Compiler_SS_env o' e ->
    Compiler_SS_val v m1 ->
    Compiler_SS_env (v :: o') (m1 :: e).
  Proof.
    move=> He Hv.
    apply: Compiler_SS_env_all.
    inv: He => H0.
    elim=> [| i IHi].
    - by rewrite /=.
    - rewrite /=.
        by apply: H0.
  Qed.

End Compiler.

(* HINT *)
(* done に効果のあるもの。 *)

Hint Constructors MML_dB_NS.
Hint Constructors dB_translation_NS.
Hint Constructors dB_translation_NS_val.
Hint Constructors dB_translation_NS_env.

Hint Constructors MSECD_SS.
Hint Resolve RTC_MSECD_SS_Refl.

Hint Constructors Compiler_SS.
Hint Constructors Compiler_SS_val.
Hint Constructors Compiler_SS_env.

(* END *)
