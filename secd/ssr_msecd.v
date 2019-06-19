From mathcomp Require Import all_ssreflect.

(** A Correct Compiler from Mini-ML to a Big-Step Machine 
   Verified Using Natural Semantics in Coq *)
(** Angel Zuniga and Gemma Bel-Enguix *)

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
    | (x', v) :: g' => if (x == x') then v else lookup x g'
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
  
  Lemma MML_NS_deterministic (g : MML_env) (e : MML_exp) (v1 v2 : MML_val) :
    MML_NS g e v1 -> MML_NS g e v2 -> v1 = v2.
  Proof.
    move=> H1.
    move: v2.
    elim: H1 => g'.
    - move=> n v2 H2.
        by inversion H2; subst.
    - move=> b v2 H2.
        by inversion H2; subst.
    - move=> e1 e2 m n H1 IH1 H2 IH2 v2 H12.
      inversion H12; subst.
      congr (VNat (_ + _)).
      + move: (IH1 (VNat m0)) => IH1'.
        move: (IH1' H5) => IH1''.
          by inversion IH1''.
      + move: (IH2 (VNat n0)) => IH2'.
        move: (IH2' H7) => IH2''.
          by inversion IH2''.
    - move=> e1 e2 m n H1 IH1 H2 IH2 v2 H12.
      inversion H12; subst.
      congr (VNat (_ - _)).
      + move: (IH1 (VNat m0)) => IH1'.
        move: (IH1' H5) => IH1''.
          by inversion IH1''.
      + move: (IH2 (VNat n0)) => IH2'.
        move: (IH2' H7) => IH2''.
          by inversion IH2''.
    - move=> e1 e2 m n H1 IH1 H2 IH2 v2 H12.
      inversion H12; subst.
      congr (VNat (_ * _)).
      + move: (IH1 (VNat m0)) => IH1'.
        move: (IH1' H5) => IH1''.
          by inversion IH1''.
      + move: (IH2 (VNat n0)) => IH2'.
        move: (IH2' H7) => IH2''.
          by inversion IH2''.
    - move=> e1 e2 m n H1 IH1 H2 IH2 v2 H12.
      inversion H12; subst.
      congr (VBool (_ == _)).
      + move: (IH1 (VNat m0)) => IH1'.
        move: (IH1' H5) => IH1''.
          by inversion IH1''.
      + move: (IH2 (VNat n0)) => IH2'.
        move: (IH2' H7) => IH2''.
          by inversion IH2''.
    - move=> x v2 IH.
        by inversion IH; subst.
    - move=> x e1 e2 v v2 H1 IH1 H2 IH2 v' H.
      inversion H; subst.
      move: (IH1 v0) => IH1'.
      move: (IH1' H7) => IH1''.
      move: (IH2 v') => IH2'.
      rewrite IH1'' in IH2'.
      move: (IH2' H8).
      done.
    - move=> e1 e2 e3 v2 H1 IH1 H2 IH2 v H.
      inversion H; subst.
      + by apply: (IH2 v) H8.
      + by move: (IH1 (VBool false) H7) => Hc. (* 前提の矛盾 *)
    - move=> e1 e2 e3 v2 H1 IH1 H2 IH2 v H.
      inversion H; subst.
      + by move: (IH1 (VBool true) H7) => Hc. (* 前提の矛盾 *)
      + by apply: (IH2 v) H8.
    - move=> x e' v2 IH.
      by inversion IH; subst.
    - move=> f x e' v2 IH.
      by inversion IH; subst.
    - move=> g1 x e1 e2 e' v2 v H1 IH1 H2 IH2 H3 IH3 v' H.
      inversion H; subst.
      + move: (IH1 (VClos x0 e4 g2) H5) => IH1'.
        inversion IH1'; subst.
        move: (IH2 v0 H7) => IH2'; subst.
        move: (IH3 v' H9) => IH3'; subst.
        done.
      + move: (IH1 (VClosRec f x0 e4 g2) H5) => IH1'.
        by inversion IH1'.                  (* 矛盾 *)
    - move=> g1 x x' e1 e2 e' v2 v H1 IH1 H2 IH2 H3 IH3 v' H.
      inversion H; subst.
      + move: (IH1 (VClos x0 e4 g2) H5) => IH1'.
          by inversion IH1'.                  (* 矛盾 *)
      + move: (IH1 (VClosRec f x0 e4 g2) H5) => IH1'.          
        inversion IH1'; subst.
        move: (IH2 v0 H7) => IH2'; subst.
        move: (IH3 v' H9) => IH3'; subst.
        done.
  Qed.
  
  Fixpoint MML_NS_interpreter (dep : nat) (g : MML_env) (e : MML_exp)
           {struct dep} : option MML_val :=
    match dep with
    | O => None
    | dep.+1 =>
      match e with
      | eNat n => Some (VNat n)
      | eBool b => Some (VBool b)
      | ePlus  e1 e2 => match MML_NS_interpreter dep g e1 with
                        | Some (VNat m) => match MML_NS_interpreter dep g e2 with
                                           | Some (VNat n) => Some (VNat (m + n))
                                           | _ => None
                                           end
                        | _ => None
                        end
      | eMinus e1 e2 => match MML_NS_interpreter dep g e1 with
                        | Some (VNat m) => match MML_NS_interpreter dep g e2 with
                                           | Some (VNat n) => Some (VNat (m - n))
                                           | _ => None
                                           end
                        | _ => None
                        end
      | eTimes e1 e2 => match MML_NS_interpreter dep g e1 with
                        | Some (VNat m) => match MML_NS_interpreter dep g e2 with
                                           | Some (VNat n) => Some (VNat (m * n))
                                           | _ => None
                                           end
                        | _ => None
                        end
      | eEq    e1 e2 => match MML_NS_interpreter dep g e1 with
                        | Some (VNat m) => match MML_NS_interpreter dep g e2 with
                                           | Some (VNat n) => Some (VBool (m == n))
                                           | _ => None
                                           end
                        | _ => None
                        end
      | eVar v => Some (lookup v g)
      | eLet x e1 e2 => match MML_NS_interpreter dep g e1 with
                        | Some v1 =>
                          MML_NS_interpreter dep ((x, v1) :: g) e2
                        | _ => None
        end
      | eIf e1 e2 e3 => match MML_NS_interpreter dep g e1 with
                        | Some (VBool true) => MML_NS_interpreter dep g e2
                        | Some (VBool false) => MML_NS_interpreter dep g e3
                        | _ => None
                        end
      | eLam x e => Some (VClos x e g)
      | eMuLam f x e => Some (VClosRec f x e g)
      | eApp e1 e2 => match MML_NS_interpreter dep g e2 with
                      | Some v2 =>
                        match MML_NS_interpreter dep g e1 with
                        | Some (VClos x e g1) =>
                          MML_NS_interpreter dep ((x, v2) :: g1) e
                        | Some (VClosRec f x e g1) =>
                          MML_NS_interpreter
                            dep ((x, v2) :: (f, (VClosRec f x e g1)) :: g1) e
                        | _ => None
                        end
                      | _ => None
                      end
      end
    end.
  
  Compute MML_NS_interpreter 10 [::] (eNat 10). (* = Some (VNat 10) *)
  Compute MML_NS_interpreter 10 [::] (eBool true). (* = Some (VBool true) *)
  Compute MML_NS_interpreter 10 [::] (ePlus (eNat 2) (eNat 3)).
  Compute MML_NS_interpreter 10 [::] (eMinus (eNat 3) (eNat 3)).
  Compute MML_NS_interpreter 10 [::] (eTimes (eNat 2) (eNat 3)).
  Compute MML_NS_interpreter 10 [::] (eEq    (eNat 2) (eNat 3)).
  Compute MML_NS_interpreter 10 [:: (X, VNat 10)] (eVar X).
  Compute MML_NS_interpreter 10 [::] (eLet X (eNat 2) (ePlus (eVar X) (eNat 3))).
  Compute MML_NS_interpreter 10 [::] (eIf (eEq (eNat 2) (eNat 3)) (eNat 2) (eNat 3)).
  Compute MML_NS_interpreter 10 [::] (eIf (eEq (eNat 2) (eNat 2)) (eBool true) (eNat 3)).
  Compute MML_NS_interpreter 10 [::] (eLam X (ePlus (eVar X) (eNat 1))).
  Compute MML_NS_interpreter 10 [::] (eMuLam F X (ePlus (eVar X) (eNat 1))).
  Compute MML_NS_interpreter 10 [::] (eApp (eLam X (ePlus (eVar X) (eNat 2))) (eNat 3)).
  Definition clos :=
    (VClosRec F X
              (eIf (eEq (eVar X) (eNat 0)) (eNat 1)
                   (eTimes (eVar X) (eApp (eVar F) (eMinus (eVar X) (eNat 1))))) [::]).
  Compute MML_NS_interpreter 19 [:: (X, VNat 5); (F, clos)] (eApp (eVar F) (eNat 5)).
  
  Definition example :=
    (eApp
       (eMuLam F X
               (eIf (eEq (eVar X) (eNat 0))
                    (eNat 1)
                    (eTimes (eVar X)
                            (eApp (eVar F)
                                  (eMinus (eVar X) (eNat 1))))))
       (eNat 5)).
  Compute MML_NS_interpreter 19 [::] example.
  
  Lemma MML_NS_same dep1 dep2 g e :
    dep1 = dep2 ->
    MML_NS_interpreter dep1 g e = MML_NS_interpreter dep2 g e.
  Proof.
  Admitted.
  
  Lemma MML_NS_interpreter_correctness :
    forall g e v, MML_NS g e v -> exists dep, MML_NS_interpreter dep g e = Some v.
  Proof.
    move=> g e v.
    elim.
    - move=> g' n. by exists 1.
    - move=> g' b. by exists 1.
    - move=> g' e1 e2 m n H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists dep1.+1.
      rewrite /= IH1 (MML_NS_same dep1 dep2 g' e2).
      + by rewrite IH2.
      + admit.          (* IH2 の dep2 が dep1 なら書き換えられる。 *)
    - move=> g' e1 e2 m n H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists dep1.+1.
      rewrite /= IH1 (MML_NS_same dep1 dep2 g' e2).
      + by rewrite IH2.
      + admit.          (* IH2 の dep2 が dep1 なら書き換えられる。 *)
    - move=> g' e1 e2 m n H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists dep1.+1.
      rewrite /= IH1 (MML_NS_same dep1 dep2 g' e2).
      + by rewrite IH2.
      + admit.
    - move=> g' e1 e2 m n H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists dep1.+1.
      rewrite /= IH1 (MML_NS_same dep1 dep2 g' e2).
      + by rewrite IH2.
      + admit.
    - move=> g' x.
        by exists 1.
    - move=> g' x e1 e2 v1 v2 H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists dep1.+1.
      rewrite /= IH1 (MML_NS_same dep1 dep2 ((x, v1) :: g') e2).
      + by rewrite IH2.
      + admit.
    - move=> g' e1 e2 e3 v2 H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists dep1.+1.
      rewrite /= IH1 (MML_NS_same dep1 dep2 g' e2).
      + by rewrite IH2.
      + admit.
    - move=> g' e1 e2 e3 v3 H1 IH1 H3 IH3.
      case: IH1 => dep1 IH1.
      case: IH3 => dep3 IH3.
      exists dep1.+1.
      rewrite /= IH1 (MML_NS_same dep1 dep3 g' e3).
      + by rewrite IH3.
      + admit.
    - move=> g' x e1.
      exists 1.
        by rewrite /=.
    - move=> g' x e1.
      exists 1.
        by rewrite /=.
    - move=> g1 g2 x e1 e2 e' v2 v' H1 IH1 H2 IH2 H3 IH3.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      case: IH3 => dep3 IH3.
      exists dep1.+1.
      rewrite /= IH1 (MML_NS_same dep1 dep2 g1 e2).
      rewrite /= IH2 (MML_NS_same dep1 dep3 ((x, v2) :: g2) e').
      + by rewrite /= IH3.
      + admit.
      + admit.
    - move=> g1 g2 x f e1 e2 e' v1 v' H1 IH1 H2 IH2 H3 IH3.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      case: IH3 => dep3 IH3.
      exists dep1.+1.
      rewrite /= IH1 (MML_NS_same dep1 dep2 g1 e2).
      rewrite IH2
              (MML_NS_same dep1 dep3 [:: (x, v1), (f, VClosRec f x e' g2) & g2] e').
      + by rewrite IH3.
      + admit.
      + admit.
  Admitted.
  
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
      dB_translation_NS (x :: p) e d ->
      dB_translation_NS p (eMuLam f x e) (dMuLam d)
  | dB_translation_NS_App   (p : ctx) (e1 e2 : MML_exp) (d1 d2 : MML_dB_exp) :
      dB_translation_NS p e1 d1 ->
      dB_translation_NS p e2 d2 ->
      dB_translation_NS p (eApp e1 e2) (dApp d1 d2).

  (* g から変数だけ取り出す。 *)
  Fixpoint mkctx (g : MML_env) : ctx := [seq fst xv | xv <- g].
  Compute mkctx [:: (X, VNat 1); (Y, VNat 2); (Z, VNat 3)].
  (* ==> [:: X; Y; Z] *)

  Inductive dB_translation_NS_env : MML_env -> MML_dB_env -> Prop :=
  | dB_translation_NS_env_nil : dB_translation_NS_env [::] [::]
  | dB_translation_NS_env_cons (x : Var) (v : MML_val) (g : MML_env)
                               (vd : MML_dB_val) (o : MML_dB_env) :
      dB_translation_NS_val v vd ->
      dB_translation_NS_env g o ->
      dB_translation_NS_env ((x, v) :: g) (vd :: o)
  
  with dB_translation_NS_val : MML_val -> MML_dB_val -> Prop :=
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
      dB_translation_NS (f :: x :: (mkctx g)) e d ->
      dB_translation_NS_val (VClosRec f x e g) (vClosRec d o).
  

  Theorem dB_translation_NS_correctness g e v :
    MML_NS g e v ->
    forall o, dB_translation_NS_env g o ->
              forall d, dB_translation_NS (mkctx g) e d ->
                        forall vd, dB_translation_NS_val v vd -> MML_dB_NS o d vd.
  Proof.
    elim.
    - move=> g' n o He d H.
      inversion H; subst=> vd Hv.
      inversion Hv; subst.
        by apply: MML_dB_NS_Nat.
    - move=> g' n o He d H.
      inversion H; subst=> vd Hv.
      inversion Hv; subst.
        by apply: MML_dB_NS_Bool.
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
      inversion H; subst=> vd Hv.
      inversion Hv; subst.
      apply: MML_dB_NS_Plus.
      + apply: IH1 => //.
        by apply: dB_translation_NS_val_Nat.
      + apply: IH2 => //.
        by apply: dB_translation_NS_val_Nat.
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
      inversion H; subst=> vd Hv.
      inversion Hv; subst.
      apply: MML_dB_NS_Minus.
      + apply: IH1 => //.
        by apply: dB_translation_NS_val_Nat.
      + apply: IH2 => //.
        by apply: dB_translation_NS_val_Nat.
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
      inversion H; subst=> vd Hv.
      inversion Hv; subst.
      apply: MML_dB_NS_Times.
      + apply: IH1 => //.
        by apply: dB_translation_NS_val_Nat.
      + apply: IH2 => //.
        by apply: dB_translation_NS_val_Nat.
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
        by inversion H.
    - move=> g' x o He d H.
      inversion H; subst=> vd Hv.
      inversion Hv; subst.
      + have test1 i : lookup_dB i o = vNat n by admit.
        rewrite -(test1 (index x (mkctx g'))).
          by apply: MML_dB_NS_Var.
      + have test1 i : lookup_dB i o = vBool b by admit.
        rewrite -(test1 (index x (mkctx g'))).
        (* MML_dB_NS o (dVar (index x (mkctx g'))) (lookup_dB (index x (mkctx g')) o) *)
          by apply: MML_dB_NS_Var.
      + have test1 i : lookup_dB i o = vClos d o0 by admit.
        rewrite -(test1 (index x (mkctx g'))).
          by apply: MML_dB_NS_Var.
      + have test1 i : lookup_dB i o = vClosRec d o0 by admit.
        rewrite -(test1 (index x (mkctx g'))).
          by apply: MML_dB_NS_Var.
          
      (* 
  He : dB_translation_NS_env g' o
  H : dB_translation_NS (mkctx g') (eVar x) d
  Hv : dB_translation_NS_val (lookup x g') vd
  ============================
  MML_dB_NS o d vd
       *)

      (* 
  He : dB_translation_NS_env g' o
  H : dB_translation_NS (mkctx g') (eVar x) (dVar (index x (mkctx g')))
  Hv : dB_translation_NS_val (lookup x g') vd
  ============================
  MML_dB_NS o (dVar (index x (mkctx g'))) vd
       *)

      
    - admit.                                (* eLet *)
    - admit.                                (* eIf *)
    - admit.                                (* eIf *)
    - admit.                                (* eLam *)
    - admit.                                (* eMuLam *)
    - admit.                                (* eApp *)
    - admit.                                (* eApp *)



      Check dB_translation_NS_val_Nat.


      (* いつか使う！ *)
      move/dB_translation_NS_env_cons in Hv.


      
End MiniMLdB.

(* END *)

(* TODO
   
   証明を見直す。inversion を使わないようにする。
   
   letrec をいれる。let + mu.lam と同じであることを証明する。
   
   big step を cofix にする？
   
   lazy eval を追加する。
   
   継続を入れる。

   型と型推論を入れる。

   seq と pair を入れる。
   
   型のないlisp風のセマンティックスを入れる。
   
   lookup を Inductive な定義にする。
   
   パーサを作る。

 *)

