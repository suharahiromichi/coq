From mathcomp Require Import all_ssreflect.

(** A Correct Compiler from Mini-ML to a Big-Step Machine 
   Verified Using Natural Semantics in Coq *)
(** Angel Zuniga and Gemma Bel-Enguix *)

(** MiniML *)

Section MiniML.
  
  (** variables *)
  Inductive Var : Set :=
  | x
  | y
  | z
  | f
  | g
  | h.
  
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
  Notation MML_env := (seq (Var * MML_val)).
  Fixpoint lookup (x : Var) (g : MML_env) : MML_val :=
    match g with
    | [::] => VBool false
    | (x, v) :: _ => v
    | _ :: g' => lookup x g'
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
  | MML_NS_AppRec (g g1 : MML_env) (x : Var) (e1 e2 e : MML_exp) (v2 v : MML_val) :
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
  Notation MML_dB_env := (seq MML_dB_val).
  Definition lookup_dB (i : nat) (o : seq MML_dB_val) := nth (vBool false) o i.
  
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
      MML_dB_NS o (dVar i) (lookup_dB i o)
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
  
End MiniMLdB.

(* END *)
