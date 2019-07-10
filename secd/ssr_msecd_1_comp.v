From mathcomp Require Import all_ssreflect.
Require Import ssrinv.
Require Import ssr_msecd_1_defs.
(*
Require Import ssr_msecd_1_db.
*)

Section Compiler.
  
  Theorem Correctnessss o d v :
    MML_dB_NS o d v ->
    forall c, Compiler_SS d c ->
              forall e, Compiler_SS_env o e ->
                        exists m, Compiler_SS_val v m /\
                                  forall s k,
                                     RTC_MSECD_SS (c ++ k, e, s) (k, e, (V m) :: s).
  Proof.
    elim.
    (* Nat *)
    - move=> o' n c H e' He.
      exists (mNat n).
      split=> // s k.
      inv: H.
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* Bool *)
    - move=> o' b c H e' He.
      exists (mBool b).
      split=> // s k.
      inv: H.
        by apply: RTC_MSECD_SS_Step => /=.
      
    (* Plus *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.                        (* m1 を mNat m にする。 *)
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22].
      inv: Hc2.                        (* m2 を mNat n にする。 *)
      exists (mNat (m + n)).
      split=> // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H21 |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H22 |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* Minus *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22].
      inv: Hc2.
      exists (mNat (m - n)).
      split=> // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H21 |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H22 |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* Times *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22].
      inv: Hc2.
      exists (mNat (m * n)).
      split=> // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H21 |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H22 |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* Eq *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22].
      inv: Hc2.
      exists (mBool (m == n)).
      split=> // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H21 |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H22 |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* Var *)
    - move=> o' i k H.
      inv: H => e He.
      exists (elookup i e).
      split.
      + by inv: He => H0.
      + move=> s k.
          by apply: RTC_MSECD_SS_Step => /=.
          
    (* Let *)
    - move=> o' d1 d2 v1 v2 H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      have He2 : Compiler_SS_env (v1 :: o') (m1 :: e)
        by apply: Compiler_SS_env_cons.
      case: (IH2 c2 H12 (m1 :: e) He2) => m2 [Hc2 H22].
      exists m2.
      split => // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H21 |].
      apply: RTC_MSECD_SS_Step => //=.
      rewrite -/cat -catA.                  (* fold cat *)
      apply: RTC_MSECD_SS_Trans; [apply: H22 |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* IF-THEN *)
    - move=> o' d1 d2 d3 v' H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 H13 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.                          (* m1 を mBool にする。 *)
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22].
      (* m2 はそのまま *)
      exists m2.
      split => // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H21 |].
      apply: RTC_MSECD_SS_Step => //=.
      apply: RTC_MSECD_SS_Trans; [apply: H22 |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* IF-ELSE *)
    - move=> o' d1 d2 d3 v' H1 IH1 H3 IH3 k H.
      inv: H => H11 H12 H13 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.
      case: (IH3 c3 H13 e He) => m3 [Hc3 H23].
      exists m3.
      split => // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H21 |].
      apply: RTC_MSECD_SS_Step => //=.
      apply: RTC_MSECD_SS_Trans; [apply: H23 |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* Clos *)
    - move=> o' d' k H.
      inv: H => H1 e He.
      exists (mClos (c ++ [:: iRet]) e).
      split.
      + by apply: Compiler_SS_val_Clos.
      + move=> s k.
          by apply: RTC_MSECD_SS_Step => /=.
          
    (* ClosRec *)
    - move=> o' d' k H.
      inv: H => H1 e He.
      exists (mClosRec (c ++ [:: iRet]) e).
      split.
      + by apply: Compiler_SS_val_ClosRec.
      + move=> s k.
          by apply: RTC_MSECD_SS_Step => /=.
        
    (* App *)
    - move=> o' o1 d1 d2 d' v1 v2 H1 IH1 H2 IH2 H' IH' k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21] {H1 H11 IH1}.
      inv: Hc1 => Hv1 He1.
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22] {H2 H12 IH2}.
      have He' : Compiler_SS_env (v1 :: o1) (m2 :: e0)
        by apply: Compiler_SS_env_cons.
      case: (IH' c Hv1 (m2 :: e0) He') => m' [Hc' H''] {Hv1 IH'}.
      exists m'.
      split => // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H21 |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H22 |].
      apply: RTC_MSECD_SS_Step => //=.
      apply: RTC_MSECD_SS_Trans; [apply: H'' |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* AppRec *)
    - move=> o' o1 d1 d2 d' v1 v2 H1 IH1 H2 IH2 H' IH' k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21] {H1 H11 IH1}.
      inv: Hc1 => Hv1 He1.
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22] {H2 H12 IH2}.
      have He' : Compiler_SS_env (v1 :: (vClosRec d' o1) :: o1)
                                 (m2 :: (mClosRec (c ++ [:: iRet]) e0) :: e0).
        by apply: Compiler_SS_env_cons; [apply: Compiler_SS_env_cons |]. (* Hc1 使う *)
      case: (IH' c Hv1 (m2 :: (mClosRec (c ++ [:: iRet]) e0) :: e0) He')
        => m' [Hc' H''] {Hv1 IH'}.
      exists m'.
      split => // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H21 |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H22 |].
      apply: RTC_MSECD_SS_Step => //=.
      apply: RTC_MSECD_SS_Trans; [apply: H'' |].
        by apply: RTC_MSECD_SS_Step => /=.
  Qed.
  
  (* ********************************************* *)
  (* ************** 冗長に書いた ****************** *)
  (* とくに、メタ変数の使用を回避して、すべて埋めた。 *)
  (* ********************************************* *)
  
  Theorem Correctnessss' o d v :
    MML_dB_NS o d v ->
    forall c, Compiler_SS d c ->
              forall e, Compiler_SS_env o e ->
                        exists m, Compiler_SS_val v m /\
                                  forall s k,
                                     RTC_MSECD_SS (c ++ k, e, s) (k, e, (V m) :: s).
  Proof.
    elim.
    (* Nat *)
    - move=> o' n c H e' He.
      exists (mNat n).
      split.
      + by apply: Compiler_SS_val_Nat.
      + move=> s k.
        inv: H.
        apply: (RTC_MSECD_SS_Step _ (k, e', V (mNat n) :: s) _).
        * by apply: MSECD_SS_Nat.
        * by apply: RTC_MSECD_SS_Refl.
          
    (* Bool *)
    - move=> o' b c H e' He.
      exists (mBool b).
      split.
      + by apply: Compiler_SS_val_Bool.
      + move=> s k.
        inv: H.
        apply: (RTC_MSECD_SS_Step _ (k, e', V (mBool b) :: s) _).
        * by apply: MSECD_SS_Bool.
        * by apply: RTC_MSECD_SS_Refl.
      
    (* Plus *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.                        (* m1 を mNat m にする。 *)
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22].
      inv: Hc2.                        (* m2 を mNat n にする。 *)
      exists (mNat (m + n)).
      split.
      + by apply: Compiler_SS_val_Nat.
      + move=> s k.
        rewrite -catA.
        apply: (RTC_MSECD_SS_Trans _ ((c2 ++ [:: iAdd]) ++ k, e, V (mNat m) :: s) _).
        * by apply: H21.
        * rewrite -catA.
          apply: (RTC_MSECD_SS_Trans
                    _ ([:: iAdd] ++ k, e, V (mNat n) :: V (mNat m) :: s) _).
          ** apply: H22.
          ** apply: (RTC_MSECD_SS_Step _ (k, e, V (mNat (m + n)) :: s) _).
             *** by apply: MSECD_SS_Add.
             *** by apply: RTC_MSECD_SS_Refl.
                 
    (* Minus *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22].
      inv: Hc2.
      exists (mNat (m - n)).
      split.
      + by apply: Compiler_SS_val_Nat.
      + move=> s k.
        rewrite -catA.
        apply: (RTC_MSECD_SS_Trans _ ((c2 ++ [:: iSub]) ++ k, e, V (mNat m) :: s) _).
        * by apply: H21.
        * rewrite -catA.
          apply: (RTC_MSECD_SS_Trans
                    _ ([:: iSub] ++ k, e, V (mNat n) :: V (mNat m) :: s) _).
          ** apply: H22.
          ** apply: (RTC_MSECD_SS_Step _ (k, e, V (mNat (m - n)) :: s) _).
             *** by apply: MSECD_SS_Sub.
             *** by apply: RTC_MSECD_SS_Refl.
                 
    (* Times *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22].
      inv: Hc2.
      exists (mNat (m * n)).
      split.
      + by apply: Compiler_SS_val_Nat.
      + move=> s k.
        rewrite -catA.
        apply: (RTC_MSECD_SS_Trans _ ((c2 ++ [:: iMul]) ++ k, e, V (mNat m) :: s) _).
        * by apply: H21.
        * rewrite -catA.
          apply: (RTC_MSECD_SS_Trans
                    _ ([:: iMul] ++ k, e, V (mNat n) :: V (mNat m) :: s) _).
          ** apply: H22.
          ** apply: (RTC_MSECD_SS_Step _ (k, e, V (mNat (m * n)) :: s) _).
             *** by apply: MSECD_SS_Mul.
             *** by apply: RTC_MSECD_SS_Refl.
                 
    (* Eq *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22].
      inv: Hc2.
      exists (mBool (m == n)).
      split.
      + by apply: Compiler_SS_val_Bool.
      + move=> s k.
        rewrite -catA.
        apply: (RTC_MSECD_SS_Trans _ ((c2 ++ [:: iEq]) ++ k, e, V (mNat m) :: s) _).
        * by apply: H21.
        * rewrite -catA.
          apply: (RTC_MSECD_SS_Trans
                    _ ([:: iEq] ++ k, e, V (mNat n) :: V (mNat m) :: s) _).
          ** apply: H22.
          ** apply: (RTC_MSECD_SS_Step _ (k, e, V (mBool (m == n)) :: s) _).
             *** by apply: MSECD_SS_Eq.
             *** by apply: RTC_MSECD_SS_Refl.
                 
    (* Var *)
    - move=> o' i k H.
      inv: H => e He.
      exists (elookup i e).
      split.
      + by inv: He => H0.
      + move=> s k.
        apply: (RTC_MSECD_SS_Step _ (k, e, V(elookup i e) :: s) _).
        * by apply: MSECD_SS_Acc.
        * by apply: RTC_MSECD_SS_Refl. 
          
    (* Let *)
    - move=> o' d1 d2 v1 v2 H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      have He2 : Compiler_SS_env (v1 :: o') (m1 :: e)
        by apply: Compiler_SS_env_cons.
      case: (IH2 c2 H12 (m1 :: e) He2) => m2 [Hc2 H22].
      exists m2.
      split.
      + done.
      + move=> s k.
        rewrite -catA.
        apply: RTC_MSECD_SS_Trans.
        * by apply: H21.
        * apply: RTC_MSECD_SS_Step.
          ** by apply: MSECD_SS_Let.
          ** rewrite -/cat -catA.           (* fold cat *)
             apply: (RTC_MSECD_SS_Trans
                       _ ([:: iEndLet] ++ k, m1 :: e, V m2 :: s) _).
             *** by apply: H22.
             *** apply: (RTC_MSECD_SS_Step _ (k, e, V m2 :: s) _).
                 **** by apply: MSECD_SS_EndLet.
                 **** by apply: RTC_MSECD_SS_Refl.
                      
    (* IF-THEN *)
    - move=> o' d1 d2 d3 v' H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 H13 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.                          (* m1 を mBool にする。 *)
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22].
      (* m2 はそのまま *)
      exists m2.
      split.
      + done.
      + move=> s k.
        rewrite -catA.
        apply: (RTC_MSECD_SS_Trans
                  _ ([:: iSel (c2 ++ [:: iJoin]) (c3 ++ [:: iJoin])] ++ k,
                     e, V (mBool true) :: s) _).
        * by apply: H21.
        * apply: (RTC_MSECD_SS_Step
                       _ (c2 ++ [:: iJoin], e, S (k, [::]) :: s) _).
          ** by apply: MSECD_SS_Seltrue.
          ** apply: (RTC_MSECD_SS_Trans
                       _  ([:: iJoin], e, [:: V m2, S (k, [::]) & s]) _).
             *** by apply: H22.
             *** apply: (RTC_MSECD_SS_Step _ (k, e, V m2 :: s) _).
                 **** by apply: MSECD_SS_Join.
                 **** by apply: RTC_MSECD_SS_Refl.
                      
    (* IF-ELSE *)
    - move=> o' d1 d2 d3 v' H1 IH1 H2 IH2 k H.
      inv: H => H11 H12 H13 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21].
      inv: Hc1.
      case: (IH2 c3 H13 e He) => m3 [Hc3 H23].
      exists m3.
      split.
      + done.
      + move=> s k.
        rewrite -catA.
        apply: (RTC_MSECD_SS_Trans
                  _ ([:: iSel (c2 ++ [:: iJoin]) (c3 ++ [:: iJoin])] ++ k,
                     e, V (mBool false) :: s) _).
        * by apply: H21.
        * apply: (RTC_MSECD_SS_Step
                       _ (c3 ++ [:: iJoin], e, S (k, [::]) :: s) _).
          ** by apply: MSECD_SS_Selfalse.
          ** apply: (RTC_MSECD_SS_Trans
                       _  ([:: iJoin], e, [:: V m3, S (k, [::]) & s]) _).
             *** by apply: H23.
             *** apply: (RTC_MSECD_SS_Step _ (k, e, V m3 :: s) _).
                 **** by apply: MSECD_SS_Join.
                 **** by apply: RTC_MSECD_SS_Refl.
                      
    (* Clos *)
    - move=> o' d' k H.
      inv: H => H1 e He.
      exists (mClos (c ++ [:: iRet]) e).
      split.
      + by apply: Compiler_SS_val_Clos.
      + move=> s k.
        apply: (RTC_MSECD_SS_Step
                  _ (k, e, V (mClos (c ++ [:: iRet]) e) :: s) _).
        ** by apply MSECD_SS_Clos.
        ** by apply: RTC_MSECD_SS_Refl.
          
    (* ClosRec *)
    - move=> o' d' k H.
      inv: H => H1 e He.
      exists (mClosRec (c ++ [:: iRet]) e).
      split.
      + by apply: Compiler_SS_val_ClosRec.
      + move=> s k.
        apply: (RTC_MSECD_SS_Step
                  _ (k, e, V (mClosRec (c ++ [:: iRet]) e) :: s) _).
        ** by apply: MSECD_SS_ClosRec.
        ** by apply: RTC_MSECD_SS_Refl.
           
    (* App *)
    - move=> o' o1 d1 d2 d' v1 v2 H1 IH1 H2 IH2 H' IH' k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21] {H1 H11 IH1}.
      inv: Hc1 => Hv1 He1.
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22] {H2 H12 IH2}.
      have He' : Compiler_SS_env (v1 :: o1) (m2 :: e0)
        by apply: Compiler_SS_env_cons.
      case: (IH' c Hv1 (m2 :: e0) He') => m' [Hc' H''] {Hv1 IH'}.
      exists m'.
      split.
      + by apply: Hc'.
      + move=> s k.
        rewrite -catA.
        apply: (RTC_MSECD_SS_Trans
                  _ ((c2 ++ [:: iApp]) ++ k, e,  V (mClos (c ++ [:: iRet]) e0) :: s) _).
        (* 関数部 *)
        * by apply: H21.
        (* 引数部 *)
        * rewrite -catA.
          apply: (RTC_MSECD_SS_Trans
                    _ ([:: iApp] ++ k, e, V m2 :: V (mClos (c ++ [:: iRet]) e0) :: s) _).
          ** by apply: H22.
          ** apply: (RTC_MSECD_SS_Step
                       _ (c ++ [:: iRet], m2 :: e0, S(k, e) :: s) _).
             *** by apply: MSECD_SS_App.
             *** apply: (RTC_MSECD_SS_Trans
                           _ ([:: iRet], m2 :: e0, V m' :: S (k, e) :: s) _).
                 (* 全体 *)
                 **** by apply: H''.
                 **** apply: (RTC_MSECD_SS_Step _ (k, e, V m' :: s) _).
                      ***** by apply: MSECD_SS_Ret.
                      ***** by apply: RTC_MSECD_SS_Refl.
        
    (* AppRec *)
    - move=> o' o1 d1 d2 d' v1 v2 H1 IH1 H2 IH2 H' IH' k H.
      inv: H => H11 H12 e He.
      case: (IH1 c1 H11 e He) => m1 [Hc1 H21] {H1 H11 IH1}.
      inv: Hc1 => Hv1 He1.
      case: (IH2 c2 H12 e He) => m2 [Hc2 H22] {H2 H12 IH2}.
      have He' : Compiler_SS_env (v1 :: (vClosRec d' o1) :: o1)
                                 (m2 :: (mClosRec (c ++ [:: iRet]) e0) :: e0).
        by apply: Compiler_SS_env_cons; [apply: Compiler_SS_env_cons |]. (* Hc1 使う *)
      case: (IH' c Hv1 (m2 :: (mClosRec (c ++ [:: iRet]) e0) :: e0) He')
        => m' [Hc' H''] {Hv1 IH'}.
      exists m'.
      split.
      + by apply: Hc'.
      + move=> s k.
        rewrite -catA.
        apply: (RTC_MSECD_SS_Trans
                  _ ((c2 ++ [:: iApp]) ++ k, e,
                     V (mClosRec (c ++ [:: iRet]) e0) :: s) _).
        * by apply: H21.
        * rewrite -catA.
          apply: (RTC_MSECD_SS_Trans
                    _ ([:: iApp] ++ k, e,
                       V m2 :: V (mClosRec (c ++ [:: iRet]) e0) :: s) _).
          ** by apply: H22.
          ** apply: (RTC_MSECD_SS_Step
                       _ (c ++ [:: iRet],
                          m2 :: mClosRec (c ++ [:: iRet]) e0 :: e0, S(k, e) :: s) _).
             *** by apply: MSECD_SS_AppRec.
             *** apply: (RTC_MSECD_SS_Trans
                           _ ([:: iRet],
                              [:: m2, mClosRec (c ++ [:: iRet]) e0 & e0],
                              V m' :: S (k, e) :: s) _).
                 **** by apply: H''.
                 **** apply: (RTC_MSECD_SS_Step _ (k, e, V m' :: s) _).
                      ***** by apply: MSECD_SS_Ret.
                      ***** by apply: RTC_MSECD_SS_Refl.
  Qed.
  
  (** 本来の定理を証明する。 *)
  (** スタックと環境の初期状態をnilとし、終了時にcodeが空である。 *)
  
  Corollary c_Correctnessss d v :
    MML_dB_NS [::] d v ->
    forall c, Compiler_SS d c ->
              exists m, Compiler_SS_val v m /\
                        RTC_MSECD_SS (c, [::], [::]) ([::], [::], [:: (V m)]).
  Proof.
    move=> Hd c H.
    case: (Correctnessss [::] d v Hd c H [::] Compiler_SS_env_nil) => x Hvs.
    exists x.
    case: Hvs => Hv Hs.
    split=> //=.
    move: (Hs [::] [::]).
      by rewrite cats0.
  Qed.
  
  (** ******** *)
  (** compiler *)
  (** ******** *)
  
  Fixpoint compile (d : MML_dB_exp) : option MSECD_Code :=
    match d with
    | dNat n => Some [:: iNat n]
    | dBool b => Some [:: iBool b]
    | dPlus d1 d2 =>
      match compile d1 with
      | Some c1 => match compile d2 with
                   | Some c2 => Some (c1 ++ c2 ++ [:: iAdd])
                   | None => None
                   end
      | None => None
      end
    | dMinus d1 d2 =>
      match compile d1 with
      | Some c1 => match compile d2 with
                   | Some c2 => Some (c1 ++ c2 ++ [:: iSub])
                   | None => None
                   end
      | None => None
      end
    | dTimes d1 d2 =>
      match compile d1 with
      | Some c1 => match compile d2 with
                   | Some c2 => Some (c1 ++ c2 ++ [:: iMul])
                   | None => None
                   end
      | None => None
      end
    | dEq d1 d2 =>
      match compile d1 with
      | Some c1 => match compile d2 with
                   | Some c2 => Some (c1 ++ c2 ++ [:: iEq])
                   | None => None
                   end
      | None => None
      end
    | dVar i => Some [:: iAcc i]
    | dLet d1 d2 =>
      match compile d1 with
      | Some c1 => match compile d2 with
                   | Some c2 => Some (c1 ++ [:: iLet] ++ c2 ++ [:: iEndLet])
                   | None => None
                   end
      | None => None
      end
    | dIf d1 d2 d3 =>
      match compile d1 with
      | Some c1 => match compile d2 with
                   | Some c2 =>
                     match compile d3 with
                     | Some c3 =>
                       Some (c1 ++ [:: iSel (c2 ++ [:: iJoin]) (c3 ++ [:: iJoin])])
                     | None => None
                     end
                   | None => None
                   end
      | None => None
      end
    | dLam d =>
      match compile d with
      | Some c => Some [:: iClos (c ++ [:: iRet])]
      | None => None
      end
    | dMuLam d =>
      match compile d with
      | Some c => Some [:: iClosRec (c ++ [:: iRet])]
      | None => None
      end
    | dApp d1 d2 =>
      match compile d1 with
      | Some c1 => match compile d2 with
                   | Some c2 => Some (c1 ++ c2 ++ [:: iApp])
                   | None => None
                   end
      | None => None
      end
    end.
  
  Theorem compiler_correctness d c :
    Compiler_SS d c -> compile d = Some c.
  Proof.
    elim=> //=.
    - move=> d1 d2 c1 c2 H1 IH1 H2 IH2.
        by rewrite IH1 IH2.
    - move=> d1 d2 c1 c2 H1 IH1 H2 IH2.
        by rewrite IH1 IH2.
    - move=> d1 d2 c1 c2 H1 IH1 H2 IH2.
        by rewrite IH1 IH2.
    - move=> d1 d2 c1 c2 H1 IH1 H2 IH2.
        by rewrite IH1 IH2.
    - move=> d1 d2 c1 c2 H1 IH1 H2 IH2.
        by rewrite IH1 IH2.
    - move=> d1 d2 d3 c1 c2 c3 H1 IH1 H2 IH2 H3 IH3.
        by rewrite IH1 IH2 IH3.
    - move=> d' c' H IH.
        by rewrite IH.
    - move=> d' c' H IH.
        by rewrite IH.
    - move=> d1 d2 c1 c2 H1 IH1 H2 IH2.
        by rewrite IH1 IH2.
  Qed.
  
  Definition example_db :=
    (dApp
       (dMuLam
          (dIf (dEq (dVar 0) (dNat 0)) (dNat 1)
               (dTimes (dVar 0) (dApp (dVar 1) (dMinus (dVar 0) (dNat 1))))))
       (dNat 5)).
  
  Compute compile example_db.
  (* 
     = Some
         [:: iClosRec
               [:: iAcc 0; iNat 0; iEq;
                   iSel [:: iNat 1; iJoin]
                     [:: iAcc 0; iAcc 1; iAcc 0; iNat 1; iSub; iApp; iMul; iJoin]; iRet];
             iNat 5; iApp]
     : option MSECD_Code
   *)
  
End Compiler.

(* END *)
