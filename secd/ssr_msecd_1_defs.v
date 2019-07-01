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
  | ePlus (e1 e2 : MML_exp)
  | eMinus (e1 e2 : MML_exp)
  | eTimes (e1 e2 : MML_exp)
  | eEq (e1 e2 : MML_exp)
  | eVar (v : Var)
  | eLet (v : Var) (e1 e2 : MML_exp)
  | eIf (e1 e2 e3 : MML_exp)
  | eLam (v : Var) (e : MML_exp)
  | eMuLam (f : Var) (v : Var) (e : MML_exp)
  | eApp (e1 e2 : MML_exp).
  
  (** values *)
  Inductive MML_val : Set :=
  | VNat (n : nat)
  | VBool (b : bool)
  | VClos (v : Var) (e : MML_exp) (g : seq (Var * MML_val))
  | VClosRec (f : Var) (v : Var) (e : MML_exp) (g : seq (Var * MML_val)).
  
  (** environments *)
  Definition MML_env := (seq (Var * MML_val)).
  Fixpoint lookup (x : Var) (g : MML_env) : MML_val :=
    match g with
    | (x', v) :: g' => if (x' == x) then v else lookup x g'
    | _ => VBool false
    end.
  
  (** The natural semantics of MiniML *)
  Inductive MML_NS : MML_env -> MML_exp -> MML_val -> Prop :=
  | MML_NS_Nat   (g : MML_env) (n : nat) : MML_NS g (eNat n) (VNat n)
  | MML_NS_Bool  (g : MML_env) (b : bool) : MML_NS g (eBool b) (VBool b)
  | MML_NS_Plus  (g : MML_env) (e1 e2 : MML_exp) (m n : nat) :
      MML_NS g e1 (VNat m) ->
      MML_NS g e2 (VNat n) ->
      MML_NS g (ePlus e1 e2) (VNat (m + n))
  | MML_NS_Minus (g : MML_env) (e1 e2 : MML_exp) (m n : nat) :
      MML_NS g e1 (VNat m) ->
      MML_NS g e2 (VNat n) ->
      MML_NS g (eMinus e1 e2) (VNat (m - n))
  | MML_NS_Times (g : MML_env) (e1 e2 : MML_exp) (m n : nat) :
      MML_NS g e1 (VNat m) ->
      MML_NS g e2 (VNat n) ->
      MML_NS g (eTimes e1 e2) (VNat (m * n))
  | MML_NS_Eq    (g : MML_env) (e1 e2 : MML_exp) (m n : nat) :
      MML_NS g e1 (VNat m) ->
      MML_NS g e2 (VNat n) ->
      MML_NS g (eEq e1 e2) (VBool (m == n))
  | MML_NS_Var   (g : MML_env) (x : Var) :
      MML_NS g (eVar x) (lookup x g)
  | MML_NS_Let   (g : MML_env) (x : Var) (e1 e2 : MML_exp) (v1 v2 : MML_val) :
      MML_NS g e1 v1 ->
      MML_NS ((x, v1) :: g) e2 v2 ->
      MML_NS g (eLet x e1 e2) v2
  | MML_NS_Iftrue (g : MML_env) (e1 e2 e3 : MML_exp) (v2 : MML_val) :
      MML_NS g e1 (VBool true) ->
      MML_NS g e2 v2 ->
      MML_NS g (eIf e1 e2 e3) v2
  | MML_NS_Iffalse (g : MML_env) (e1 e2 e3 : MML_exp) (v3 : MML_val) :
      MML_NS g e1 (VBool false) ->
      MML_NS g e3 v3 ->
      MML_NS g (eIf e1 e2 e3) v3
  | MML_NS_Lam   (g : MML_env) (x : Var) (e : MML_exp) :
      MML_NS g (eLam x e) (VClos x e g)
  | MML_NS_MuLam (g : MML_env) (f : Var) (x : Var) (e : MML_exp) :
      MML_NS g (eMuLam f x e) (VClosRec f x e g)
  | MML_NS_App (g g1 : MML_env) (x : Var) (e1 e2 e : MML_exp) (v2 v : MML_val) :
      MML_NS g e1 (VClos x e g1) ->
      MML_NS g e2 v2 ->
      MML_NS ((x, v2) :: g1) e v ->
      MML_NS g (eApp e1 e2) v
  | MML_NS_AppRec (g g1 : MML_env) (x f : Var) (e1 e2 e : MML_exp) (v2 v : MML_val) :
      MML_NS g e1 (VClosRec f x e g1) ->
      MML_NS g e2 v2 ->
      MML_NS ((x, v2) :: (f, (VClosRec f x e g1)) :: g1) e v ->
      MML_NS g (eApp e1 e2) v.
  
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
  | dB_translation_NS_Plus  (p : ctx) (e1 e2 : MML_exp) (d1 d2 : MML_dB_exp) :
      dB_translation_NS p e1 d1 ->
      dB_translation_NS p e2 d2 ->
      dB_translation_NS p (ePlus e1 e2) (dPlus d1 d2)
  | dB_translation_NS_Minus (p : ctx) (e1 e2 : MML_exp) (d1 d2 : MML_dB_exp) :
      dB_translation_NS p e1 d1 ->
      dB_translation_NS p e2 d2 ->
      dB_translation_NS p (eMinus e1 e2) (dMinus d1 d2)
  | dB_translation_NS_Times (p : ctx) (e1 e2 : MML_exp) (d1 d2 : MML_dB_exp) :
      dB_translation_NS p e1 d1 ->
      dB_translation_NS p e2 d2 ->
      dB_translation_NS p (eTimes e1 e2) (dTimes d1 d2)
  | dB_translation_NS_Var   (p : ctx) (x : Var) :
      dB_translation_NS p (eVar x) (dVar (index x p))
  | dB_translation_NS_Let   (p : ctx) (x : Var) (e1 e2 : MML_exp) (d1 d2 : MML_dB_exp) :
      dB_translation_NS p e1 d1 ->
      dB_translation_NS (x :: p) e2 d2 ->
      dB_translation_NS p (eLet x e1 e2) (dLet d1 d2)
  | dB_translation_NS_If    (p : ctx) (e1 e2 e3 : MML_exp) (d1 d2 d3 : MML_dB_exp) :
      dB_translation_NS p e1 d1 ->
      dB_translation_NS p e2 d2 ->
      dB_translation_NS p e3 d3 ->
      dB_translation_NS p (eIf e1 e2 e3) (dIf d1 d2 d3)
  | dB_translation_NS_Lam   (p : ctx) (x : Var) (e : MML_exp) (d : MML_dB_exp) :
      dB_translation_NS (x :: p) e d ->
      dB_translation_NS p (eLam x e) (dLam d)
  | dB_translation_NS_MuLam (p : ctx) (f x : Var) (e : MML_exp) (d : MML_dB_exp) :
      dB_translation_NS (x :: f :: p) e d ->
      dB_translation_NS p (eMuLam f x e) (dMuLam d)
  | dB_translation_NS_App   (p : ctx) (e1 e2 : MML_exp) (d1 d2 : MML_dB_exp) :
      dB_translation_NS p e1 d1 ->
      dB_translation_NS p e2 d2 ->
      dB_translation_NS p (eApp e1 e2) (dApp d1 d2).

  (* g から変数だけ取り出す。 *)
  Definition mkctx (g : MML_env) : ctx := [seq fst xv | xv <- g].
  Compute mkctx [:: (X, VNat 1); (Y, VNat 2); (Z, VNat 3)].
  (* ==> [:: X; Y; Z] *)

  Inductive dB_translation_NS_val : MML_val -> MML_dB_val -> Prop :=
  | dB_translation_NS_val_Nat  (n : nat) : dB_translation_NS_val (VNat n) (vNat n)
  | dB_translation_NS_val_Bool (b : bool) : dB_translation_NS_val (VBool b) (vBool b)
  | db_translation_NS_val_Clos (x : Var) (e : MML_exp) (g : MML_env)
                               (d : MML_dB_exp) (o : MML_dB_env) :
      dB_translation_NS_env g o ->
      dB_translation_NS (x :: (mkctx g)) e d ->
      dB_translation_NS_val (VClos x e g) (vClos d o)
  | db_translation_NS_val_ClosRec (f x : Var) (e : MML_exp) (g : MML_env)
                               (d : MML_dB_exp) (o : MML_dB_env) :
      dB_translation_NS_env g o ->
      dB_translation_NS (x :: f :: (mkctx g)) e d ->
      dB_translation_NS_val (VClosRec f x e g) (vClosRec d o)

  with dB_translation_NS_env : MML_env -> MML_dB_env -> Prop :=
       | dB_translation_NS_env_all (g : MML_env) (o : MML_dB_env) :
           (forall (x : Var),
               dB_translation_NS_val (lookup x g) (olookup (index x (mkctx g)) o)) ->
           dB_translation_NS_env g o.
(*
  with dB_translation_NS_env : MML_env -> MML_dB_env -> Prop :=
  | dB_translation_NS_env_nil : dB_translation_NS_env [::] [::]
  | dB_translation_NS_env_cons (x : Var) (v : MML_val) (g : MML_env)
                               (vd : MML_dB_val) (o : MML_dB_env) :
      dB_translation_NS_val v vd ->
      dB_translation_NS_env g o ->
      dB_translation_NS_env ((x, v) :: g) (vd :: o).
 *)

  Lemma dB_translation_NS_env_cons (x : Var) (v : MML_val) (g : MML_env)
        (vd : MML_dB_val) (o : MML_dB_env) :
    dB_translation_NS_env g o ->
    dB_translation_NS_val v vd ->
    dB_translation_NS_env ((x, v) :: g) (vd :: o).
  Proof.
    move=> He Hv.
    apply: dB_translation_NS_env_all.
    inv: He => H0.
    case.                                   (* x0 *)
    - case H : (x == A).
      + by rewrite /= H /=.
      + by rewrite /= H /=.
    - case H : (x == B).
      + by rewrite /= H /=.
      + by rewrite /= H /=.
    - case H : (x == C).
      + by rewrite /= H /=.
      + by rewrite /= H /=.
    - case H : (x == F).
      + by rewrite /= H /=.
      + by rewrite /= H /=.
    - case H : (x == G).
      + by rewrite /= H /=.
      + by rewrite /= H /=.
    - case H : (x == H).
      + by rewrite /= H /=.
      + by rewrite /= H /=.
    - case H : (x == X).
      + by rewrite /= H /=.
      + by rewrite /= H /=.
    - case H : (x == Y).
      + by rewrite /= H /=.
      + by rewrite /= H /=.
    - case H : (x == Z).
      + by rewrite /= H /=.
      + by rewrite /= H /=.
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
  | mClos (c : MSECD_Code) (d : seq MSECD_Val)
  | mClosRec (c : MSECD_Code) (d : seq MSECD_Val).
  Definition MSECD_Env := seq MSECD_Val.
  
  Definition dlookup (i : nat) (d : MSECD_Env) := nth (mBool false) d i.
  
  Inductive MSECD_SVal : Set :=
  | V (v : MSECD_Val)                       (* Machine Value *)
  | S (s : MSECD_Code * MSECD_Env).         (* Stack Frame *)
  Definition MSECD_Stack := seq MSECD_SVal.

  (* C/E/S *)
  Definition conf := (MSECD_Code * MSECD_Env * MSECD_Stack)%type.
  
  Inductive MSECD_SS : conf -> conf -> Prop :=
  | MSECD_SS_Nat  (n : nat) (c : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS ( iNat n :: c,       d,                              s)
               (           c,       d,                 V(mNat n) :: s)
  | MSECD_SS_Bool (b : bool) (c : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS (iBool b :: c,       d,                              s)
               (           c,       d,                V(mBool b) :: s)
  | MSECD_SS_Add  (m n : nat) (c : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS (   iAdd :: c,       d,    V(mNat n) :: V(mNat m) :: s)
               (           c,       d,           V(mNat (m + n)) :: s)
  | MSECD_SS_Sub  (m n : nat) (c : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS (   iSub :: c,       d,    V(mNat n) :: V(mNat m) :: s)
               (           c,       d,           V(mNat (m - n)) :: s)  
  | MSECD_SS_Mul  (m n : nat) (c : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS (   iMul :: c,       d,    V(mNat n) :: V(mNat m) :: s)
               (           c,       d,           V(mNat (m * n)) :: s)
  | MSECD_SS_Eq   (m n : nat) (c : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS (    iEq :: c,       d,    V(mNat n) :: V(mNat m) :: s)
               (           c,       d,         V(mBool (m == n)) :: s)
  | MSECD_SS_Acc  (i : nat) (c : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS ( iAcc i :: c,       d,                              s)
               (           c,       d,            V(dlookup i d) :: s)
  | MSECD_SS_Let  (v : MSECD_Val) (c : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS (   iLet :: c,       d,                      V(v) :: s)
               (           c,  v :: d,                              s)
  | MSECD_SS_EndLet (v : MSECD_Val) (c : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS (iEndLet :: c,  v :: d,                              s)
               (           c,       d,                              s)
  | MSECD_SS_Seltrue (c c1 c2 : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS (iSel c1 c2 :: c,    d,             V(mBool true) :: s)
               (          c1,       d,                S(c, [::]) :: s)
  | MSECD_SS_Selfalse (c c1 c2 : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS (iSel c1 c2 :: c,    d,            V(mBool false) :: s)
               (          c2,       d,                S(c, [::]) :: s)
  | MSECD_SS_Join (v : MSECD_Val) (c c1 : MSECD_Code) (d d1 : MSECD_Env)
                  (s : MSECD_Stack) :
      MSECD_SS (  iJoin :: c,       d,         V(v) :: S(c1, d1) :: s) (* d1 捨てる *)
               (          c1,       d,                      V(v) :: s)
  | MSECD_SS_Clos (c c1 : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS (iClos c1 :: c,      d,                              s)
               (           c,       d,             V(mClos c1 d) :: s)
  | MSECD_SS_ClosRec (c c1 : MSECD_Code) (d : MSECD_Env) (s : MSECD_Stack) :
      MSECD_SS (iClosRec c1 :: c,   d,                              s)
               (           c,       d,          V(mClosRec c1 d) :: s)
  | MSECD_SS_App (v : MSECD_Val) (c c1 : MSECD_Code) (d d1 : MSECD_Env)(s : MSECD_Stack) :
      MSECD_SS (   iApp :: c,       d,    V(v) :: V(mClos c1 d1) :: s)
               (          c1, v :: d1,                   S(c, d) :: s)
  | MSECD_SS_AppRec (v : MSECD_Val)(c c1 : MSECD_Code)(d d1 : MSECD_Env)(s :MSECD_Stack) :
      MSECD_SS (   iApp :: c,       d, V(v) :: V(mClosRec c1 d1) :: s)
               (          c1,
            v :: mClosRec c1 d1 :: d1,                   S(c, d) :: s)
  | MSECD_SS_Ret (v : MSECD_Val)(c c1 : MSECD_Code)(d d1 : MSECD_Env)(s :MSECD_Stack) :
      MSECD_SS (   iRet :: c,       d,         V(v) :: S(c1, d1) :: s)
               (          c1,      d1,                      V(v) :: s).
  (*           
  Inductive RTC_MSECD_SS : conf -> conf -> Prop :=
  | RTC_MSECD_SS_Reflexivity (cf : conf) : RTC_MSECD_SS cf cf
  | RTC_MSECD_SS_Transitivity (cf1 cf2 cf3 : conf) :
      MSECD_SS cf1 cf2 -> RTC_MSECD_SS cf2 cf3 ->  RTC_MSECD_SS cf1 cf3.
   *)
  
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
           (forall i, Compiler_SS_val (olookup i o) (dlookup i e)) ->
           Compiler_SS_env o e.
(*
  with Compiler_SS_env : MML_dB_env -> MSECD_Env -> Prop :=
       | Compiler_SS_env_nil : Compiler_SS_env [::] [::]
       | Compiler_SS_env_cons v o m e :
           Compiler_SS_val v m ->
           Compiler_SS_env o e ->
           Compiler_SS_env (v :: o) (m :: e).
 *)
                      
  (* RTC_MSECD_SS_Trans を直接つかえばよい。  *)
  Lemma AppendSS c1 c2 c3 d1 d2 d3 s1 s2 s3 :
      RTC_MSECD_SS (c1 ++ c2 ++ c3, d1, s1) (c2 ++ c3, d2, s2) -> (* c1 を実行前後 *)
      RTC_MSECD_SS (      c2 ++ c3, d2, s2) (      c3, d3, s3) -> (* c2 を実行前後 *)
      RTC_MSECD_SS (c1 ++ c2 ++ c3, d1, s1) (      c3, d3, s3). (* c1とc2 を実行前後 *)
  Proof.
    move=> H1 H2.
    apply: RTC_MSECD_SS_Trans.
    - by apply: H1.
    - by apply: H2.
  Qed.

End Compiler.

(* END *)
