From mathcomp Require Import all_ssreflect.

(* A Correct Compiler from Mini-ML to a Big-Step Machine 
   Verified Using Natural Semantics in Coq *)
(* Angel Zuniga and Gemma Bel-Enguix *)

Section MiniMLdB.
  
  (* MiniMLdB abstract syntax *)
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
  | dMu (d : MML_dB_exp)
  | dApp (d1 d2 : MML_dB_exp).
  
  (* nameless values *)
  Inductive MML_dB_val : Set :=
  | vNat (n : nat)
  | vBool (b : bool)
  | vClos (d : MML_dB_exp) (o : seq MML_dB_val)
  | vClosRec (d : MML_dB_exp) (o : seq MML_dB_val).
  
  (* nameless environments *)
  Definition lookup_dB (i : nat) (o : seq MML_dB_val) := nth (vBool false) o i.
  
  (* The natural semantics of MiniMLdB *)
  Inductive MML_dB_NS : seq MML_dB_val -> MML_dB_exp -> MML_dB_val -> Prop :=
  | MML_dB_NS_Nat   (o : seq MML_dB_val) (n : nat) : MML_dB_NS o (dNat n) (vNat n)
  | MML_dB_NS_Bool  (o : seq MML_dB_val) (b : bool) : MML_dB_NS o (dBool b) (vBool b)
  | MML_dB_NS_Plus  (o : seq MML_dB_val) (d1 d2 : MML_dB_exp) (m n : nat) :
      MML_dB_NS o d1 (vNat m) ->
      MML_dB_NS o d2 (vNat n) ->
      MML_dB_NS o (dPlus d1 d2) (vNat (m + n))
  | MML_dB_NS_Minus (o : seq MML_dB_val) (d1 d2 : MML_dB_exp) (m n : nat) :
      MML_dB_NS o d1 (vNat m) ->
      MML_dB_NS o d2 (vNat n) ->
      MML_dB_NS o (dMinus d1 d2) (vNat (m - n))
  | MML_dB_NS_Times (o : seq MML_dB_val) (d1 d2 : MML_dB_exp) (m n : nat) :
      MML_dB_NS o d1 (vNat m) ->
      MML_dB_NS o d2 (vNat n) ->
      MML_dB_NS o (dTimes d1 d2) (vNat (m * n))
  | MML_dB_NS_Eq    (o : seq MML_dB_val) (d1 d2 : MML_dB_exp) (m n : nat) :
      MML_dB_NS o d1 (vNat m) ->
      MML_dB_NS o d2 (vNat n) ->
      MML_dB_NS o (dEq    d1 d2) (vBool (m == n))
  | MML_dB_NS_Var   (o : seq MML_dB_val) (i : nat) (v : MML_dB_val) :
      lookup_dB i o = v -> MML_dB_NS o (dVar i) v
  | MML_dB_NS_Let   (o : seq MML_dB_val) (d1 d2 : MML_dB_exp) (v1 v2 : MML_dB_val) :
      MML_dB_NS o d1 v1 ->
      MML_dB_NS (v1 :: o) d2 v2 ->
      MML_dB_NS o (dLet   d1 d2) v2
  | MML_dB_NS_Iftrue (o : seq MML_dB_val) (d1 d2 d3 : MML_dB_exp) (v1 v2 : MML_dB_val) :
      MML_dB_NS o d1 v1 -> v1 = vBool true ->
      MML_dB_NS o d2 v2 ->
      MML_dB_NS o (dIf d1 d2 d3) v2
  | MML_dB_NS_Iffalse (o : seq MML_dB_val) (d1 d2 d3 : MML_dB_exp) (v1 v3 : MML_dB_val) :
      MML_dB_NS o d1 v1 -> v1 = vBool false ->
      MML_dB_NS o d2 v3 ->
      MML_dB_NS o (dIf d1 d2 d3) v3
  | MML_dB_NS_Lam   (o : seq MML_dB_val) (d : MML_dB_exp) :
      MML_dB_NS o (dLam d) (vClos d o)
  | MML_dB_NS_Mu    (o : seq MML_dB_val) (d : MML_dB_exp) :
      MML_dB_NS o (dMu  d) (vClosRec d o)
  | MML_dB_NS_App (o o1 : seq MML_dB_val) (d1 d2 d : MML_dB_exp) (v1 v2 v : MML_dB_val) :
      MML_dB_NS o d1 v1 -> v1 = vClos d o1 ->
      MML_dB_NS o d2 v2 ->
      MML_dB_NS (v2 :: o1) d v ->
      MML_dB_NS o (dApp d1 d2) v
  | MML_dB_NS_AppRec (o o1 : seq MML_dB_val) (d1 d2 d : MML_dB_exp)
                     (v1 v2 v : MML_dB_val) :
      MML_dB_NS o d1 v1 -> v1 = vClosRec d o1 ->
      MML_dB_NS o d2 v2 ->
      MML_dB_NS (v2 :: (vClosRec d o1) :: o1) d v ->
      MML_dB_NS o (dApp d1 d2) v.
  
End MiniMLdB.

(*
Inductive Var : Set :=
| x
| y
| z.

Inductive Fun : Set :=
| f
| g
| h.

Inductive MML_exp : Set :=
| eNat (n : nat)
| eBool (b : bool)
| ePlus (e1 e2 : MML_exp)
| eMinus (e1 e2 : MML_exp)
| eTimes (e1 e2 : MML_exp)
| eVar (v : Var)
| eCond (e1 e2 e3 : MML_exp)
| eLet (v : Var) (e1 e2 : MML_exp)
| eAbs (v : Var) (e : MML_exp)
| eFix (f : Fun) (v : Var) (e : MML_exp)
| eApp (e1 e2 : MML_exp).

Definition MML_env := seq (Var * MML_exp).

Inductive MML_val : Set :=
| vNat (n : nat)
| vBool (b : bool)
| vClos (v : Var) (e : MML_exp) (g : MML_env)
| vClosRec (f : Fun) (v : Var) (e : MML_exp) (g : MML_env).

Inductive MML_NS : MML_env -> MML_exp -> MML_val -> Prop :=
| MML_NS_Nat : forall (g : MML_env) (n : nat), MML_NS g (eNat n) (vNat n)
| MML_NS_Bool : forall (g : MML_env) (b : bool), MML_NS g (eBool b) (vBool b)
| MML_NS_Plus : forall (g : MML_env) (e1 e2 : MML_exp) (m n : nat),
    MML_NS g e1 (vNat m) -> MML_NS g e2 (vNat n) ->
    MML_NS g (ePlus e1 e2) (vNat (m + n))
| MML_NS_Minus : forall (g : MML_env) (e1 e2 : MML_exp) (m n : nat),
    MML_NS g e1 (vNat m) -> MML_NS g e2 (vNat n) ->
    MML_NS g (eMinus e1 e2) (vNat (m + n))
| MML_NS_Times : forall (g : MML_env) (e1 e2 : MML_exp) (m n : nat),
    MML_NS g e1 (vNat m) -> MML_NS g e2 (vNat n) ->
    MML_NS g (eTimes e1 e2) (vNat (m + n))
| MML_NS_Var : forall (g : MML_env) (v : Var),
    MML_NS g (eVar v) 
           
 *)
