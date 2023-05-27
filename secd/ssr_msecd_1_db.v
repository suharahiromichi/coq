From mathcomp Require Import all_ssreflect.
From common Require Import ssrinv.
Require Import ssr_msecd_1_defs.

(** de Bruijn notation MiniMLdB *)

Section MiniMLdB.
  
  Theorem dB_translation_NS_correctness g t u :
    MML_NS g t u ->
    forall o, dB_translation_NS_env g o ->
              forall d, dB_translation_NS (mkctx g) t d ->
                        exists v, dB_translation_NS_val u v /\ MML_dB_NS o d v.
  Proof.
    elim.
    (* Nat *)
    - move=> g' n o He d H.
      exists (vNat n).
      inv: H.
        by split.
      
    (* Bool *)
    - move=> g' b o He d H.
      exists (vBool b).
      inv: H.
        by split.
      
    (* Plus *)
    - move=> g' t1 t2 m n H1 IH1 H2 IH2 o He d H.
      inv: H => H1' H2'.
      case: (IH1 o He d1 H1') => v1 [H11 H12].
      inv: H11.
      case: (IH2 o He d2 H2') => v2 [H21 H22].
      inv: H21.
      exists (vNat (m + n)).
      split=> //.
        by apply: MML_dB_NS_Plus.
        
    (* Minus *)
    - move=> g' t1 t2 m n H1 IH1 H2 IH2 o He d H.
      inv: H => H1' H2'.
      case: (IH1 o He d1 H1') => v1 [H11 H12].
      inv: H11.
      case: (IH2 o He d2 H2') => v2 [H21 H22].
      inv: H21.
      exists (vNat (m - n)).
      split=> //.
        by apply: MML_dB_NS_Minus.
        
    (* Times *)
    - move=> g' t1 t2 m n H1 IH1 H2 IH2 o He d H.
      inv: H => H1' H2'.
      case: (IH1 o He d1 H1') => v1 [H11 H12].
      inv: H11.
      case: (IH2 o He d2 H2') => v2 [H21 H22].
      inv: H21.
      exists (vNat (m * n)).
      split=> //.
        by apply: MML_dB_NS_Times.

    (* Eq *)
    - move=> g' t1 t2 m n H1 IH1 H2 IH2 o He d H.
        by inv: H.

    (* Var *)
    - move=> g' x o He d H.
      inv: H.
      exists (olookup (index x (mkctx g')) o).
      split=> //.
        by inv: He => H0.
        
    (* Let *)
    - move=> g' x g1 g2 u1 u2 H1 IH1 H2 IH2 o He d H.
      inv: H => H1' H2'.
      case: (IH1 o He d1 H1') => v1 [H11 H12].
      have He1 : dB_translation_NS_env ((x, u1) :: g') (v1 :: o)
        by apply: dB_translation_NS_env_cons.
      have H'' : dB_translation_NS (mkctx ((x, u1) :: g')) g2 d2 by [].
      case: (IH2 (v1 :: o) He1 d2 H'') => v2 [H21 H22].
      exists v2.
      split=> //.
        by apply: (MML_dB_NS_Let o d1 d2 v1 v2).
        
    (* If true *)
    - move=> g' t1 t2 t3 u2 H1 IH1 H2 IH2 o He d H.
      inv: H => H1' H2' H3'.
      case: (IH1 o He d1 H1') => v1 [H11 H12].
      inv: H11.
      case: (IH2 o He d2 H2') => v2 [H21 H22].
      exists v2.
      split=> //.
        by apply: MML_dB_NS_Iftrue.
        
    (* If false *)
    - move=> g' t1 t2 t3 u3 H1 IH1 H3 IH3 o He d H.
      inv: H => H1' H2' H3'.
      case: (IH1 o He d1 H1') => v1 [H11 H12].
      inv: H11.
      case: (IH3 o He d3 H3') => v3 [H31 H32].
      exists v3.
      split=> //.
        by apply: MML_dB_NS_Iffalse.
        
    (* Lam *)
    - move=> g' x t' o He d H.
      inv: H.
      exists (vClos d0 o).
      split=> //.
        by apply: db_translation_NS_val_Clos.
        
    (* MuLam *)
    - move=> g' f x t' o He d H.
      inv: H.
      exists (vClosRec d0 o).
      split=> //.
        by apply: db_translation_NS_val_ClosRec.
        
    (* App Clos *)
    - move=> g' g3 x t1 t2 t3 u2 v3 H1 IH1 H2 IH2 H3 IH3 o He d H.
      inv: H => H1' H2'.
      case: (IH1 o He d1 H1') => v1 [H11 H12] {IH1}. (* 関数部 *)
      inv: H11 => He3 H3'.
      case: (IH2 o He d2 H2') => v2 [H21 H22] {IH2}. (* 引数部 *)
      (* クロージャの中身を評価する環境 *)
      have He2 : dB_translation_NS_env ((x, u2) :: g3) (v2 :: o0)
        by apply: dB_translation_NS_env_cons.
      (* クロージャの中身を変換する。 *)
      have H'' : dB_translation_NS (mkctx ((x, u2) :: g3)) t3 d by [].
      case: (IH3 (v2 :: o0) He2 d H'') => u3 [H31 H32] {IH3}.
      exists u3.
      split=> //.
        (* eauto でもよい。 *)
        by apply: MML_dB_NS_App; [apply: H12 | apply: H22 | apply: H32].
        
    (* App ClosRec *)
    - move=> g' g3 f x t1 t2 t3 u2 v3 H1 IH1 H2 IH2 H3 IH3 o He d H.
      inv: H => H1' H2'.
      case: (IH1 o He d1 H1') => v1 [H11 H12] {IH1}.
      inv: H11 => He3 H3'.                  (* keep する。 *)
      case: (IH2 o He d2 H2') => v2 [H21 H22] {IH2}.
      have He2 : dB_translation_NS_env
                   ((x, u2) :: (f, (uClosRec f x t3 g3)) :: g3)
                   (v2 :: (vClosRec d o0) :: o0)
        by apply: dB_translation_NS_env_cons; [apply: dB_translation_NS_env_cons |].
      have H'' : dB_translation_NS
                   (mkctx ((x, u2) :: (f, uClosRec f x t3 g3) :: g3)) t3 d by [].
      case: (IH3 (v2 :: (vClosRec d o0) :: o0) He2 d H'') => u3 [H31 H32] {IH3}.
      exists u3.
      split=> //.
        by apply: MML_dB_NS_AppRec; [apply: H12 | apply: H22 | apply: H32].
  Qed.
  
  Corollary c_dB_translation_NS_correctness t u :
    MML_NS [::] t u ->
    forall d, dB_translation_NS [::] t d ->
              exists v, dB_translation_NS_val u v /\ MML_dB_NS [::] d v.  
  Proof.
    move=> H d Hd.
    case: (dB_translation_NS_correctness
             [::] t u H [::] dB_translation_NS_env_nil d Hd) => x Hvs.
    exists x.
    case: Hvs => Hv Hs.
      by split.
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
  
  Theorem dB_translation_NS_compiler_correctness ctx t d :
    dB_translation_NS ctx t d -> 
    dB_translation_NS_compiler ctx t = Some d.
  Proof.
    elim=> //=.
    - move=> p t1 t2 d1 d2 H1 IH1 H2 IH2 /=. (* plus *)
      by rewrite IH1 IH2.
    - move=> p t1 t2 d1 d2 H1 IH1 H2 IH2 /=. (* minus *)
      by rewrite IH1 IH2.
    - move=> p t1 t2 d1 d2 H1 IH1 H2 IH2 /=. (* times *)
      by rewrite IH1 IH2.
    - move=> p x t1 t2 d1 d2 H1 IH1 H2 IH2 /=. (* let *)
      by rewrite IH1 IH2.
    - move=> p t1 t2 t3 d1 d2 d3 H1 IH1 H2 IH2 H3 IH3. (* if *)
      by rewrite IH1 IH2 IH3.
    - move=> p x e d' H IH.                 (* lam *)
      by rewrite IH.
    - move=> p f x e d' H IH.               (* mulam *)
      by rewrite IH.
    - move=> p t1 t2 d1 d2 H1 IH1 H2 IH2.   (* app *)
      by rewrite IH1 IH2.
  Qed.
  
  Definition example :=
    (eApp
       (eMuLam F X
               (eIf (eEq (eVar X) (eNat 0))
                    (eNat 1)
                    (eTimes (eVar X)
                            (eApp (eVar F)
                                  (eMinus (eVar X) (eNat 1))))))
       (eNat 5)).
  
  Compute dB_translation_NS_compiler [::] example.
  (*
     = Some
         (dApp
            (dMuLam
               (dIf (dEq (dVar 0) (dNat 0)) (dNat 1)
                  (dTimes (dVar 0) (dApp (dVar 1) (dMinus (dVar 0) (dNat 1))))))
            (dNat 5)) : option MML_dB_exp
   *)

End MiniMLdB.

(* END *)
