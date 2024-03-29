From HB Require Import structures.          (* MathComp2 *)
From mathcomp Require Import all_ssreflect.

(** A Correct Compiler from Mini-ML to a Big-Step Machine 
   Verified Using Natural Semantics in Coq *)
(** Angel Zuniga and Gemma Bel-Enguix *)

(** proof was written independently by @suharahiromichi *)

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
  
(*
  Definition Literal_eqMixin := EqMixin Literal_eqP.
  Canonical Literal_eqType := EqType Literal Literal_eqMixin.
*)
  HB.instance Definition _ := hasDecEq.Build Literal Literal_eqP. (* MathComp2 *)
  
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
  (* = Some (VNat 120) : option MML_val *)
  
  Lemma MML_NS_lt {dep1 dep2 g e v} :
    dep1 < dep2 ->
    MML_NS_interpreter dep1 g e = Some v ->
    MML_NS_interpreter dep2 g e = Some v.
  Proof.
    elim: dep1; elim: dep2 => //.
    move=> m IHm n IHn Hle H.
  Admitted.
  
  Lemma MML_NS_maxl {dep1 dep2 g e v} :
    MML_NS_interpreter dep1 g e = Some v ->
    MML_NS_interpreter (maxn dep1 dep2) g e = Some v.
  Proof.
    move=> H.
    rewrite /maxn.
    case: (leqP dep2 dep1) => Hlt.
    - done.
    - by apply: (MML_NS_lt Hlt).
  Qed.
  
  Lemma MML_NS_maxr {dep1 dep2 g e v} :
    MML_NS_interpreter dep2 g e = Some v ->
    MML_NS_interpreter (maxn dep1 dep2) g e = Some v.
  Proof.
    rewrite maxnC.
    by apply: MML_NS_maxl.
  Qed.
  (* dep が３つ以上の場合も、maxnAとmaxnC を使い、同様に証明する。 *)
  
  Theorem MML_NS_interpreter_correctnes :
    forall g e v, MML_NS g e v -> exists dep, MML_NS_interpreter dep g e = Some v.
  Proof.
    move=> g e v.
    elim.
    - move=> g' n. by exists 1.
    - move=> g' b. by exists 1.
    - move=> g' e1 e2 m n H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists (maxn dep1 dep2).+1.
      Check (MML_NS_maxl IH1).
      by rewrite /= (MML_NS_maxl IH1) (MML_NS_maxr IH2).
      
    - move=> g' e1 e2 m n H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists (maxn dep1 dep2).+1.
      by rewrite /= (MML_NS_maxl IH1) (MML_NS_maxr IH2).
      
    - move=> g' e1 e2 m n H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists (maxn dep1 dep2).+1.
      by rewrite /= (MML_NS_maxl IH1) (MML_NS_maxr IH2).

    - move=> g' e1 e2 m n H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists (maxn dep1 dep2).+1.
      by rewrite /= (MML_NS_maxl IH1) (MML_NS_maxr IH2).

    - move=> g' x.
      by exists 1.
    - move=> g' x e1 e2 v1 v2 H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists (maxn dep1 dep2).+1.
      by rewrite /= (MML_NS_maxl IH1) (MML_NS_maxr IH2).
      
    - move=> g' e1 e2 e3 v2 H1 IH1 H2 IH2.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      exists (maxn dep1 dep2).+1.
      by rewrite /= (MML_NS_maxl IH1) (MML_NS_maxr IH2).
      
    - move=> g' e1 e2 e3 v3 H1 IH1 H3 IH3.
      case: IH1 => dep1 IH1.
      case: IH3 => dep3 IH3.
      exists (maxn dep1 dep3).+1.
      by rewrite /= (MML_NS_maxl IH1) (MML_NS_maxr IH3).
      
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
      exists (maxn dep1 (maxn dep2 dep3)).+1.
      rewrite maxnC -maxnA.
      rewrite /= (MML_NS_maxl IH2).
      rewrite maxnA.
      rewrite (MML_NS_maxr IH1).
      rewrite maxnC maxnA.
      rewrite (MML_NS_maxr IH3).
      done.
      
    - move=> g1 g2 x f e1 e2 e' v1 v' H1 IH1 H2 IH2 H3 IH3.
      case: IH1 => dep1 IH1.
      case: IH2 => dep2 IH2.
      case: IH3 => dep3 IH3.
      exists (maxn dep1 (maxn dep2 dep3)).+1.
      rewrite maxnC -maxnA.
      rewrite /= (MML_NS_maxl IH2).
      rewrite maxnA.
      rewrite (MML_NS_maxr IH1).
      rewrite maxnC maxnA.
      rewrite (MML_NS_maxr IH3).
      done.
  Qed.
  
  Theorem MML_NS_interpreter_correctnes2 :
    forall g e v, (exists dep, MML_NS_interpreter dep g e = Some v) -> MML_NS g e v.
  Proof.
    move=> g e v.
    case=> dep.
    elim: dep => // n.
    elim: e => //=.
    - move=> n' IHe H.
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
    inversion He; subst.
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
  
  Fixpoint dB_translation_NS_compiler (p : ctx) (e : MML_exp) : option MML_dB_exp :=
    match e with
    | eNat n => Some (dNat n)
    | eBool b => Some (dBool b)
    | ePlus e1 e2 =>
      match dB_translation_NS_compiler p e1 with
      | Some d1 => match dB_translation_NS_compiler p e2 with
                   | Some d2 => Some (dPlus d1 d2)
                   | _ => None
                   end
      | _ => None
      end
    | eMinus e1 e2 =>
      match dB_translation_NS_compiler p e1 with
      | Some d1 => match dB_translation_NS_compiler p e2 with
                   | Some d2 => Some (dMinus d1 d2)
                   | _ => None
                   end
      | _ => None
      end
    | eTimes e1 e2 =>
      match dB_translation_NS_compiler p e1 with
      | Some d1 => match dB_translation_NS_compiler p e2 with
                   | Some d2 => Some (dTimes d1 d2)
                   | _ => None
                   end
      | _ => None
      end
    | eEq e1 e2 =>
      match dB_translation_NS_compiler p e1 with
      | Some d1 => match dB_translation_NS_compiler p e2 with
                   | Some d2 => Some (dEq d1 d2)
                   | _ => None
                   end
      | _ => None
      end
    | eVar x => Some (dVar (index x p))        
    | eLet x e1 e2 =>
      match dB_translation_NS_compiler p e1 with
      | Some d1 => match dB_translation_NS_compiler (x :: p) e2 with
                   | Some d2 => Some (dLet d1 d2)
                   | _ => None
                   end
      | _ => None
      end
    | eIf e1 e2 e3 =>
      match dB_translation_NS_compiler p e1 with
      | Some d1 => match dB_translation_NS_compiler p e2 with
                   | Some d2 => match dB_translation_NS_compiler p e3 with
                                | Some d3 => Some (dIf d1 d2 d3)
                                | _ => None
                                end
                   | _ => None
                   end
      | _ => None
      end
    | eLam x e =>
      match dB_translation_NS_compiler (x :: p) e with
      | Some d => Some (dLam d)
      | _ => None
      end
    | eMuLam f x e =>
      match dB_translation_NS_compiler (x :: f :: p) e with
      | Some d => Some (dMuLam d)
      | _ => None
      end
    | eApp e1 e2 =>
      match dB_translation_NS_compiler p e1 with
      | Some d1 => match dB_translation_NS_compiler p e2 with
                   | Some d2 => Some (dApp d1 d2)
                   | _ => None
                   end
      | _ => None
      end
    end.

  Compute dB_translation_NS_compiler [::] example.
  (*
     = Some
         (dApp
            (dMuLam
               (dIf (dEq (dVar 0) (dNat 0)) (dNat 1)
                  (dTimes (dVar 0) (dApp (dVar 1) (dMinus (dVar 0) (dNat 1))))))
            (dNat 5)) : option MML_dB_exp
   *)

  Theorem dB_translation_NS_correctness g e v :
    MML_NS g e v ->
    forall o, dB_translation_NS_env g o ->
              forall d, dB_translation_NS (mkctx g) e d ->
                        exists vd, dB_translation_NS_val v vd /\ MML_dB_NS o d vd.
  Proof.
    elim.
    (* Nat *)
    - move=> g' n o He d H.
      exists (vNat n).
      inversion H; subst.
      split.
      * by apply: dB_translation_NS_val_Nat.
      * by apply: MML_dB_NS_Nat.

    (* Bool *)
    - move=> g' b o He d H.
      exists (vBool b).
      inversion H; subst.
      split.
      * by apply: dB_translation_NS_val_Bool.
      * by apply: MML_dB_NS_Bool.

    (* Plus *)
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
      inversion H; subst.
      case: (IH1 o He d0 H5) => d1' [H11 H12].
      inversion H11; subst.
      case: (IH2 o He d3 H7) => d2' [H21 H22].
      inversion H21; subst.
      exists (vNat (m + n)).
      split.
      + by apply: dB_translation_NS_val_Nat.
      + apply: MML_dB_NS_Plus.
        * by apply: H12.
        * by apply: H22.

    (* Minus *)
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
      inversion H; subst.
      case: (IH1 o He d0 H5) => d1' [H11 H12].
      inversion H11; subst.
      case: (IH2 o He d3 H7) => d2' [H21 H22].
      inversion H21; subst.
      exists (vNat (m - n)).
      split.
      + by apply: dB_translation_NS_val_Nat.
      + apply: MML_dB_NS_Minus.
        * by apply: H12.
        * by apply: H22.

    (* Times *)
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
      inversion H; subst.
      case: (IH1 o He d0 H5) => d1' [H11 H12].
      inversion H11; subst.
      case: (IH2 o He d3 H7) => d2' [H21 H22].
      inversion H21; subst.
      exists (vNat (m * n)).
      split.
      + by apply: dB_translation_NS_val_Nat.
      + apply: MML_dB_NS_Times.
        * by apply: H12.
        * by apply: H22.

    (* Eq *)
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
      by inversion H.

    (* Var *)
    - move=> g' x o He d H.
      inversion H; subst.
      exists (olookup (index x (mkctx g')) o).
      split.
      * inversion He; subst.
        by apply: H0.
      * by apply: MML_dB_NS_Var.
        
    (* Let *)
    - move=> g' x e1 e2 v1 v2 H1 IH1 H2 IH2 o He d H.
      inversion H; subst.
      (* 定義部は、普通に評価する。その結果がv1' *)
      case: (IH1 o He d1 H7) => v1' [H11 H12].
      (* 本体は、(x,v1)を追加して評価する。その結果がv2' *)
      have He2 : dB_translation_NS_env ((x, v1) :: g') (v1' :: o)
        by apply: dB_translation_NS_env_cons.
      have H82 : dB_translation_NS (mkctx ((x, v1) :: g')) e2 d2 by apply: H8.
      (* (mkctx ((x, v1) :: g') = x :: mkctx g') は、simpl で証明できる。 *)
      case: (IH2 (v1' :: o) He2 d2 H82) => v2' [H21 H22].
      exists v2'.
      split.
      * by apply: H21.
      * apply: (MML_dB_NS_Let o d1 d2 v1' v2').
        ** by apply: H12.                   (* 定義部 *)
        ** by apply: H22.                   (* 本体 *)
           
    (* If true *)
    - move=> g' e1 e2 e3 v2 H1 IH1 H2 IH2 o He d H.
      (* v2 は then 節 *)
      inversion H; subst.
      case: (IH1 o He d1 H6) => v1' [H11 H12].
      inversion H11; subst.
      case: (IH2 o He d2 H8) => v2' [H21 H22].
      exists v2'.
      split.
      + by apply: H21.
      + apply: MML_dB_NS_Iftrue.
        * inversion H12; subst => //.
          ** by apply: MML_dB_NS_Eq.
          ** by apply: MML_dB_NS_Var.
        * by apply: H22.
          
    (* If false *)
    - move=> g' e1 e2 e3 v3 H1 IH1 H3 IH3 o He d H.
      (* v3 は else 節 *)
      inversion H; subst.
      case: (IH1 o He d1 H6) => v1' [H11 H12].
      inversion H11; subst.
      case: (IH3 o He d3 H9) => v3' [H31 H32].
      exists v3'.
      split.
      + by apply: H31.
      + apply: MML_dB_NS_Iffalse.
        * inversion H12; subst => //.
          ** by apply: MML_dB_NS_Eq.
          ** by apply: MML_dB_NS_Var.
        * by apply: H32.
          
    (* Lam *)
    - move=> g' x e' o He d H.
      inversion H; subst.
      exists (vClos d0 o).
      split.
      + by apply: db_translation_NS_val_Clos.
      + by apply: MML_dB_NS_Lam.

    (* MuLam *)
    - move=> g' f x e' o He d H.
      inversion H; subst.
      exists (vClosRec d0 o).
      split.
      + apply: db_translation_NS_val_ClosRec.
        * by apply: He.
        * by apply: H5.
      + by apply: MML_dB_NS_MuLam.

    (* App Clos *)
    - move=> g' g3 x e1 e2 e3 v2 v3 H1 IH1 H2 IH2 H3 IH3 o He d H.
      inversion H; subst.
      case: (IH1 o He d1 H6) => v1' [H11 H12] {IH1}. (* 関数部 *)
      inversion H11; subst.
      case: (IH2 o He d2 H8) => v2' [H21 H22] {IH2}. (* 引数部 *)
      
      (* クロージャの中身を評価する環境 *)
      Check dB_translation_NS_env ((x, v2) :: g3) (v2' :: o0).
      have He3 : dB_translation_NS_env ((x, v2) :: g3) (v2' :: o0).
      + apply: dB_translation_NS_env_cons.
        * by apply: H9.
        * by apply: H21.
          
      (* クロージャの中身を変換する。 *)
      Check (IH3 (v2' :: o0) He3).
      have H30 : dB_translation_NS (mkctx ((x, v2) :: g3)) e3 d by apply: H10.
      
      Check (IH3 (v2' :: o0) He3 d H30).
      case: (IH3 (v2' :: o0) He3 d H30) => v3' [H31 H32] {IH3}.
      
      exists v3'.
      split.
      + by apply: H31.
      + apply: MML_dB_NS_App.
        * by apply: H12.
        * by apply: H22.
        * by apply: H32.

    (* App ClosRec *)
    - move=> g' g3 x f e1 e2 e3 v2 v3 H1 IH1 H2 IH2 H3 IH3 o He d H.
      inversion H; subst.
      case: (IH1 o He d1 H6) => v1' [H11 H12] {IH1}. (* 関数部 *)
      inversion H11; subst.
      case: (IH2 o He d2 H8) => v2' [H21 H22] {IH2}. (* 引数部 *)
      
      (* クロージャの中身を評価する環境 *)
      Check (VClosRec f x e3 g3).
      have He3 : dB_translation_NS_env
                   ((x, v2) :: (f, (VClosRec f x e3 g3)) :: g3)
                   (v2' :: (vClosRec d o0) :: o0).
      + apply: dB_translation_NS_env_cons.
        * apply: dB_translation_NS_env_cons.
          ** by apply: H10.
          ** by apply: H11.
        * by apply: H21.
          
      (* クロージャの中身を変換する。 *)
      Check (IH3 (v2' :: (vClosRec d o0) :: o0) He3 d).
      have H30 : dB_translation_NS
                   (mkctx ((x, v2) :: (f, VClosRec f x e3 g3) :: g3)) e3 d
        by apply: H13.
      
      Check (IH3 (v2' :: (vClosRec d o0) :: o0) He3 d H30).
      case: (IH3 (v2' :: (vClosRec d o0) :: o0) He3 d H30) => v3' [H31 H32] {IH3}.
      
      exists v3'.
      split.
      + by apply: H31.
      + apply: MML_dB_NS_AppRec.
        * by apply: H12.
        * by apply: H22.
        * by apply: H32.
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

  Lemma Compiler_SS_env_cons m o' mv1 e :
    Compiler_SS_env o' e ->
    Compiler_SS_val m mv1 ->
    Compiler_SS_env (m :: o') (mv1 :: e).
  Proof.
    move=> He Hv.
    apply: Compiler_SS_env_all.
    inversion He; subst.
    elim=> [| i IHi].                       (* i *)
    - by rewrite /=.
    - rewrite /=.
        by apply: H0.
  Qed.
  
  Theorem CorrectnessSS o d v :
    MML_dB_NS o d v ->
    forall c, Compiler_SS d c ->
              forall d, Compiler_SS_env o d ->
                        exists mv, Compiler_SS_val v mv /\
                                   forall s k, RTC_MSECD_SS (c ++ k, d, s)
                                                            (k, d, (V mv) :: s).
  Proof.
    elim.
    (* Nat *)
    - move=> o' n c H d' He.
      exists (mNat n).
      split.
      + by apply: Compiler_SS_val_Nat.
      + inversion H; subst=> s k.
        Check RTC_MSECD_SS_Step ([:: iNat n] ++ k, d', s)
              (k, d', V (mNat n) :: s) (k, d', V (mNat n) :: s).
        apply: (RTC_MSECD_SS_Step _ (k, d', V (mNat n) :: s) _).
        * by apply: MSECD_SS_Nat.
        * by apply: RTC_MSECD_SS_Refl.
          
    (* Bool *)
    - move=> o' b c H d' He.
      exists (mBool b).
      split.
      + by apply: Compiler_SS_val_Bool.
      + move=> s k.
        apply: (RTC_MSECD_SS_Step _ (k, d', V (mBool b) :: s) _).
        inversion H; subst.                 (* inv は後でもよい。 *)
        * by apply: MSECD_SS_Bool.
        * by apply: RTC_MSECD_SS_Refl.
          
    (* Plus *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inversion H; subst=> e He.
      
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'].
      inversion Hc1; subst.               (* mv1 を mNat m にする。 *)
      case: (IH2 c2 H6 e He) => mv2 [Hc2 H2'].
      inversion Hc2; subst.               (* mv2 を mNat n にする。 *)
      
      exists (mNat (m + n)).
      split.
      + by apply: Compiler_SS_val_Nat.
      + move=> s k.
        rewrite -catA.
        apply: RTC_MSECD_SS_Trans.
        * by apply: H1'.
        * rewrite -catA.
          apply: RTC_MSECD_SS_Trans.
          ** by apply: H2'.
          ** apply: (RTC_MSECD_SS_Step _ (k, e, V (mNat (m + n)) :: s) _).
             *** by apply: MSECD_SS_Add.
             *** by apply: RTC_MSECD_SS_Refl.

    (* Minus *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inversion H; subst=> e He.
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'].
      inversion Hc1; subst.
      case: (IH2 c2 H6 e He) => mv2 [Hc2 H2'].
      inversion Hc2; subst.
      exists (mNat (m - n)).
      split.
      + by apply: Compiler_SS_val_Nat.
      + move=> s k.
        rewrite -catA.
        apply: RTC_MSECD_SS_Trans.
        * by apply: H1'.
        * rewrite -catA.
          apply: RTC_MSECD_SS_Trans.
          ** by apply: H2'.
          ** apply: (RTC_MSECD_SS_Step _ (k, e, V (mNat (m - n)) :: s) _).
             *** by apply: MSECD_SS_Sub.
             *** by apply: RTC_MSECD_SS_Refl.
                 
    (* Times *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inversion H; subst=> e He.
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'].
      inversion Hc1; subst.
      case: (IH2 c2 H6 e He) => mv2 [Hc2 H2'].
      inversion Hc2; subst.
      exists (mNat (m * n)).
      split.
      + by apply: Compiler_SS_val_Nat.
      + move=> s k.
        rewrite -catA.
        apply: RTC_MSECD_SS_Trans.
        * by apply: H1'.
        * rewrite -catA.
          apply: RTC_MSECD_SS_Trans.
          ** by apply: H2'.
          ** apply: (RTC_MSECD_SS_Step _ (k, e, V (mNat (m * n)) :: s) _).
             *** by apply: MSECD_SS_Mul.
             *** by apply: RTC_MSECD_SS_Refl.                 
                 
    (* Eq *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inversion H; subst=> e He.
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'].
      inversion Hc1; subst.
      case: (IH2 c2 H6 e He) => mv2 [Hc2 H2'].
      inversion Hc2; subst.
      exists (mBool (m == n)).
      split.
      + by apply: Compiler_SS_val_Bool.
      + move=> s k.
        rewrite -catA.
        apply: RTC_MSECD_SS_Trans.
        * by apply: H1'.
        * rewrite -catA.
          apply: RTC_MSECD_SS_Trans.
          ** by apply: H2'.
          ** apply: (RTC_MSECD_SS_Step _ (k, e, V (mBool (m == n)) :: s) _).
             *** by apply: MSECD_SS_Eq.
             *** by apply: RTC_MSECD_SS_Refl.                 
                 
    (* Var *)
    - move=> o' i c H.
      inversion H; subst=> e He.
      exists (dlookup i e).
      split.
      + inversion He; subst.
          by apply: H0.
      + move=> s k.
        apply: (RTC_MSECD_SS_Step _ (k, e, V(dlookup i e) :: s) _).
        * by apply: MSECD_SS_Acc.
        * by apply: RTC_MSECD_SS_Refl. 
          
    (* Let *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inversion H; subst=> e He.
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'].
      have He2 : Compiler_SS_env (m :: o') (mv1 :: e)
        by apply: Compiler_SS_env_cons.
      case: (IH2 c2 H6 (mv1 :: e) He2) => mv2 [Hc2 H2'].
      exists mv2.
      split.
      + done.
      + move=> s k.
        rewrite -catA.
        apply: RTC_MSECD_SS_Trans.
        * by apply: H1' => //.
        * apply: RTC_MSECD_SS_Step.
          ** by apply: MSECD_SS_Let.
          ** rewrite -/cat -catA.            (* fold cat *)
            apply: RTC_MSECD_SS_Trans.
             *** by apply: H2' => //.
             *** apply: RTC_MSECD_SS_Step.
              **** by apply: MSECD_SS_EndLet.
              **** by apply: RTC_MSECD_SS_Refl.
      
      (* IF-THEN *)
      - move=> o' d1 d2 d3 v' H1 IH1 H2 IH2 k H.
        inversion H; subst => e He.
        case: (IH1 c1 H5 e He) => mv1 [Hc1 H1'].
        inversion Hc1; subst.               (* mv1 を mBool にする。 *)
        case: (IH2 c2 H7 e He) => mv2 [Hc2 H2'].
        (* mv2 はそのまま *)
        exists mv2.
        split.
        + done.
        + move=> s k.
          rewrite -catA.
          apply: RTC_MSECD_SS_Trans.
          (* If 節 *)
          + by apply: H1'.
          (* Then 節 *)
          + apply: RTC_MSECD_SS_Step.
            * by apply: MSECD_SS_Seltrue.
            * apply: RTC_MSECD_SS_Trans.
              ** by apply: H2'.
              ** apply: RTC_MSECD_SS_Step.
                 *** by apply: MSECD_SS_Join.
                 *** by apply: RTC_MSECD_SS_Refl.
                     
      (* IF-ELSE *)
      - move=> o' d1 d2 d3 v' H1 IH1 H3 IH3 k H.
        inversion H; subst => e He.
        case: (IH1 c1 H5 e He) => mv1 [Hc1 H1'].
        inversion Hc1; subst.               (* mv1 を mBool にする。 *)
        case: (IH3 c3 H8 e He) => mv3 [Hc3 H3'].
        (* mv3 はそのまま *)
        exists mv3.
        split.
        + done.
        + move=> s k.
          rewrite -catA.
          apply: RTC_MSECD_SS_Trans.
          (* If 節 *)
          * by apply: H1'.
          (* Else 節 *)
          * apply: RTC_MSECD_SS_Step.
            ** by apply: MSECD_SS_Selfalse.
            ** apply: RTC_MSECD_SS_Trans.
               *** by apply: H3'.
               *** apply: RTC_MSECD_SS_Step.
                   **** by apply: MSECD_SS_Join.
                   **** by apply: RTC_MSECD_SS_Refl.
               
    (* Clos *)
    - move=> o' d' c H.
      inversion H; subst=> e He.
      exists (mClos (c0 ++ [:: iRet]) e).
      split.
      + by inversion H1; subst; apply: Compiler_SS_val_Clos => //.
      + move=> s k.
        apply: (RTC_MSECD_SS_Step
                  _ (k, e, V (mClos (c0 ++ [:: iRet]) e) :: s) _).
        ** by apply MSECD_SS_Clos.
        ** by apply: RTC_MSECD_SS_Refl.
           
    (* ClosRec *)
    - move=> o' d' c H.
      inversion H; subst=> e He.
      exists (mClosRec (c0 ++ [:: iRet]) e).
      split.
      + by inversion H1; subst; apply: Compiler_SS_val_ClosRec => //.
      + move=> s k.
        apply: (RTC_MSECD_SS_Step
                  _ (k, e, V (mClosRec (c0 ++ [:: iRet]) e) :: s) _).
        ** by apply: MSECD_SS_ClosRec.
        ** by apply: RTC_MSECD_SS_Refl.
           
    (* App *)
    - move=> o' o1 d1 d2 d' m n H1 IH1 H2 IH2 H' IH' k H.
      inversion H; subst=> e He.
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'].
      inversion Hc1; subst.
      case: (IH2 c2 H6 e He) => mv2 [Hc2 H2'].
      have He' : Compiler_SS_env (m :: o1) (mv2 :: e0)
        by apply: Compiler_SS_env_cons.
      case: (IH' c H5 (mv2 :: e0) He') => mv' [Hc' H''].
      exists mv'.
      move=> {H1} {H2} {IH1} {IH2}.
      split.
      + by apply: Hc'.
      + move=> s k.
        rewrite -catA.
        apply: RTC_MSECD_SS_Trans.
        (* 関数部 *)
        * by apply: H1'.
        (* 引数部 *)
        * rewrite -catA.
          apply: RTC_MSECD_SS_Trans.
          ** by apply: H2'.
          ** apply: RTC_MSECD_SS_Step.
             *** by apply: MSECD_SS_App.
             *** apply: RTC_MSECD_SS_Trans.
                 (* 全体 *)
                 **** by apply: H''.
                 **** apply: RTC_MSECD_SS_Step.
                      ***** by apply: MSECD_SS_Ret.
                      ***** by apply: RTC_MSECD_SS_Refl.
    (* AppRec *)
    - move=> o' o1 d1 d2 d' m n H1 IH1 H2 IH2 H' IH' k H.
      inversion H; subst=> e He.
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'].
      inversion Hc1; subst.
      case: (IH2 c2 H6 e He) => mv2 [Hc2 H2'].
      move=> {H1} {H2} {IH1} {IH2}.
      Check (mClosRec (c ++ [:: iRet]) e0).
      have He' : Compiler_SS_env (m :: (vClosRec d' o1) :: o1)
                                 (mv2 :: (mClosRec (c ++ [:: iRet]) e0) :: e0).
      + apply: Compiler_SS_env_cons.
        * apply: Compiler_SS_env_cons.
          ** done.
          ** done.
        * done.
          
      Check IH' c H5 (mv2 :: (mClosRec (c ++ [:: iRet]) e0) :: e0) He'.
      case: (IH' c H5 (mv2 :: (mClosRec (c ++ [:: iRet]) e0) :: e0) He') => mv' [Hc' H''].
      exists mv'.
      split.
      + by apply: Hc'.
      + move=> s k.
        rewrite -catA.
        apply: RTC_MSECD_SS_Trans.
        (* 関数部 *)
        * by apply: H1'.
        (* 引数部 *)
        * rewrite -catA.
          apply: RTC_MSECD_SS_Trans.
          ** by apply: H2'.
          ** apply: RTC_MSECD_SS_Step.
             *** by apply: MSECD_SS_AppRec.
             *** apply: RTC_MSECD_SS_Trans.
                 (* 全体 *)
                 **** by apply: H''.
                 **** apply: RTC_MSECD_SS_Step.
                      ***** by apply: MSECD_SS_Ret.
                      ***** by apply: RTC_MSECD_SS_Refl.
  Qed.

End Compiler.


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
   
   RTC_MSECD_SSのクロージャーをCoqのライブラリを使用する。
   
   変数の使い方を統一する。

   コンパイラやシムレータの関数を作成する。Propとの完全性健全性を証明する。

   ド・ブラウンの扱いに習熟するために：
   リストの要素それぞれが関係Rを満たすことと、nth i のすべてで満たすことの証明。
   AllR は Indextive な定義の場合と、Fixpoint Prop の場合の両方について。
   AllR R s1 s2 <-> forall i, R (nth i s1) (nth i s2)
 *)

