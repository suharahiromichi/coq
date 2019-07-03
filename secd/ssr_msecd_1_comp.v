From mathcomp Require Import all_ssreflect.
Require Import ssrinv.
Require Import ssr_msecd_1_defs.
(*
Require Import ssr_msecd_1_db.
*)

Section Compiler.

  Theorem CorrectnessSS' o d v :
    MML_dB_NS o d v ->
    forall c, Compiler_SS d c ->
              forall d, Compiler_SS_env o d ->
                        exists mv, Compiler_SS_val v mv /\
                                   forall s k,
                                     RTC_MSECD_SS (c ++ k, d, s) (k, d, (V mv) :: s).
  Proof.
    elim.
    (* Nat *)
    - move=> o' n c H d' He.
      exists (mNat n).
      split.
      + by apply: Compiler_SS_val_Nat.
      + inv: H => s k.
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
      + inv: H => s k.
        apply: (RTC_MSECD_SS_Step _ (k, d', V (mBool b) :: s) _).
        * by apply: MSECD_SS_Bool.
        * by apply: RTC_MSECD_SS_Refl.
          
    (* Plus *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      (* pose ltac_mark; inversion H; subst; gen_until_mark. *)
      inv: H => H'1 H'2 e He.
      case: (IH1 c1 H'1 e He) => mv1 [Hc1 H1'].
      inv: Hc1.                        (* mv1 を mNat m にする。 *)
      case: (IH2 c2 H'2 e He) => mv2 [Hc2 H2'].
      inv: Hc2.                        (* mv2 を mNat n にする。 *)
      
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
      inv: H => H'1 H'2 e He.
      (* inverts keep H as H'1 H'2; subst=> e He. *)
      case: (IH1 c1 H'1 e He) => mv1 [Hc1 H1'].
      inv: Hc1.
      case: (IH2 c2 H'2 e He) => mv2 [Hc2 H2'].
      inv: Hc2.
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
      inv: H => H'1 H'2 e He.
      case: (IH1 c1 H'1 e He) => mv1 [Hc1 H1'].
      inv: Hc1.
      case: (IH2 c2 H'2 e He) => mv2 [Hc2 H2'].
      inv: Hc2.
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
      inv: H => H'1 H'2 e He.
      case: (IH1 c1 H'1 e He) => mv1 [Hc1 H1'].
      inv: Hc1.
      case: (IH2 c2 H'2 e He) => mv2 [Hc2 H2'].
      inv: Hc2.
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
      inv: H => e He.
      exists (elookup i e).
      split.
      + inv: He => H0.
          by apply: H0.
      + move=> s k.
        apply: (RTC_MSECD_SS_Step _ (k, e, V(elookup i e) :: s) _).
        * by apply: MSECD_SS_Acc.
        * by apply: RTC_MSECD_SS_Refl. 
          
    (* Let *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H4 H6 e He.
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
        inv: H => H5 H7 H8 e He.
        case: (IH1 c1 H5 e He) => mv1 [Hc1 H1'].
        inv: Hc1.                       (* mv1 を mBool にする。 *)
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
        inv: H => H5 H7 H8 e He.
        case: (IH1 c1 H5 e He) => mv1 [Hc1 H1'].
        inv: Hc1.                       (* mv1 を mBool にする。 *)
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
      inv: H => H1 e He.
      exists (mClos (c0 ++ [:: iRet]) e).
      split.
      + by apply: Compiler_SS_val_Clos.
      + move=> s k.
        apply: (RTC_MSECD_SS_Step
                  _ (k, e, V (mClos (c0 ++ [:: iRet]) e) :: s) _).
        ** by apply MSECD_SS_Clos.
        ** by apply: RTC_MSECD_SS_Refl.
           
    (* ClosRec *)
    - move=> o' d' c H.
      inv: H => H1 e He.
      exists (mClosRec (c0 ++ [:: iRet]) e).
      split.
      + by apply: Compiler_SS_val_ClosRec.
      + move=> s k.
        apply: (RTC_MSECD_SS_Step
                  _ (k, e, V (mClosRec (c0 ++ [:: iRet]) e) :: s) _).
        ** by apply: MSECD_SS_ClosRec.
        ** by apply: RTC_MSECD_SS_Refl.
           
    (* App *)
    - move=> o' o1 d1 d2 d' m n H1 IH1 H2 IH2 H' IH' k H.
      inv: H => H4 H6 e He.
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'].
      inv: Hc1 => H5 H8.
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
      inv: H => H4 H6 e He.
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'].
      move: (Hc1); inv=> H5 H8.             (* dup 複製する。 *)
      case: (IH2 c2 H6 e He) => mv2 [Hc2 H2'].
      move=> {H1} {H2} {IH1} {IH2}.
      Check (mClosRec (c ++ [:: iRet]) e0).
      have He' : Compiler_SS_env (m :: (vClosRec d' o1) :: o1)
                                 (mv2 :: (mClosRec (c ++ [:: iRet]) e0) :: e0).
      + apply: Compiler_SS_env_cons.
        * apply: Compiler_SS_env_cons.
          ** by apply: H8.
          ** by apply: Hc1.                 (* 複製を使う。 *)
        * by apply: Hc2.
          
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
  
  (* ***************************************** *)
  (* ***************************************** *)
  (* ***************************************** *)
  
  Theorem CorrectnessSS o d v :
    MML_dB_NS o d v ->
    forall c, Compiler_SS d c ->
              forall e, Compiler_SS_env o e ->
                        exists mv, Compiler_SS_val v mv /\
                                   forall s k,
                                     RTC_MSECD_SS (c ++ k, e, s) (k, e, (V mv) :: s).
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
      inv: H => H'1 H'2 e He.
      case: (IH1 c1 H'1 e He) => mv1 [Hc1 H1'].
      inv: Hc1.                        (* mv1 を mNat m にする。 *)
      case: (IH2 c2 H'2 e He) => mv2 [Hc2 H2'].
      inv: Hc2.                        (* mv2 を mNat n にする。 *)
      exists (mNat (m + n)).
      split=> // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H1' |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H2' |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* Minus *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H'1 H'2 e He.
      case: (IH1 c1 H'1 e He) => mv1 [Hc1 H1'].
      inv: Hc1.
      case: (IH2 c2 H'2 e He) => mv2 [Hc2 H2'].
      inv: Hc2.
      exists (mNat (m - n)).
      split=> // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H1' |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H2' |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* Times *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H'1 H'2 e He.
      case: (IH1 c1 H'1 e He) => mv1 [Hc1 H1'].
      inv: Hc1.
      case: (IH2 c2 H'2 e He) => mv2 [Hc2 H2'].
      inv: Hc2.
      exists (mNat (m * n)).
      split=> // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H1' |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H2' |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* Eq *)
    - move=> o' d1 d2 m n H1 IH1 H2 IH2 k H.
      inv: H => H'1 H'2 e He.
      case: (IH1 c1 H'1 e He) => mv1 [Hc1 H1'].
      inv: Hc1.
      case: (IH2 c2 H'2 e He) => mv2 [Hc2 H2'].
      inv: Hc2.
      exists (mBool (m == n)).
      split=> // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H1' |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H2' |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* Var *)
    - move=> o' i c H.
      inv: H => e He.
      exists (elookup i e).
      split.
      + by inv: He => H0.
      + move=> s k.
          by apply: RTC_MSECD_SS_Step => /=.
          
    (* Let *)
    - move=> o' d1 d2 v1 v2 H1 IH1 H2 IH2 k H.
      inv: H => H4 H6 e He.
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'].
      have He2 : Compiler_SS_env (v1 :: o') (mv1 :: e)
        by apply: Compiler_SS_env_cons.
      case: (IH2 c2 H6 (mv1 :: e) He2) => mv2 [Hc2 H2'].
      exists mv2.
      split => // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H1' |].
      apply: RTC_MSECD_SS_Step => //=.
      rewrite -/cat -catA.                  (* fold cat *)
      apply: RTC_MSECD_SS_Trans; [apply: H2' |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* IF-THEN *)
    - move=> o' d1 d2 d3 v' H1 IH1 H2 IH2 k H.
      inv: H => H5 H7 H8 e He.
      case: (IH1 c1 H5 e He) => mv1 [Hc1 H1'].
      inv: Hc1.                          (* mv1 を mBool にする。 *)
      case: (IH2 c2 H7 e He) => mv2 [Hc2 H2'].
      (* mv2 はそのまま *)
      exists mv2.
      split => // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H1' |].
      apply: RTC_MSECD_SS_Step => //=.
      apply: RTC_MSECD_SS_Trans; [apply: H2' |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* IF-ELSE *)
    - move=> o' d1 d2 d3 v' H1 IH1 H3 IH3 k H.
      inv: H => H5 H7 H8 e He.
      case: (IH1 c1 H5 e He) => mv1 [Hc1 H1'].
      inv: Hc1.
      case: (IH3 c3 H8 e He) => mv3 [Hc3 H3'].
      exists mv3.
      split => // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H1' |].
      apply: RTC_MSECD_SS_Step => //=.
      apply: RTC_MSECD_SS_Trans; [apply: H3' |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* Clos *)
    - move=> o' d' c H.
      inv: H => H1 e He.
      exists (mClos (c0 ++ [:: iRet]) e).
      split.
      + by apply: Compiler_SS_val_Clos.
      + move=> s k.
          by apply: RTC_MSECD_SS_Step => /=.
          
    (* ClosRec *)
    - move=> o' d' c H.
      inv: H => H1 e He.
      exists (mClosRec (c0 ++ [:: iRet]) e).
      split.
      + by apply: Compiler_SS_val_ClosRec.
      + move=> s k.
          by apply: RTC_MSECD_SS_Step => /=.
        
    (* App *)
    - move=> o' o1 d1 d2 d' v1 v2 H1 IH1 H2 IH2 H' IH' k H.
      inv: H => H4 H6 e He.
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'] {H1 H4 IH1}.
      inv: Hc1 => H5 H8.
      case: (IH2 c2 H6 e He) => mv2 [Hc2 H2'] {H2 H6 IH2}.
      have He' : Compiler_SS_env (v1 :: o1) (mv2 :: e0)
        by apply: Compiler_SS_env_cons.
      case: (IH' c H5 (mv2 :: e0) He') => mv' [Hc' H''] {H5 IH'}.
      exists mv'.
      split => // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H1' |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H2' |].
      apply: RTC_MSECD_SS_Step => //=.
      apply: RTC_MSECD_SS_Trans; [apply: H'' |].
        by apply: RTC_MSECD_SS_Step => /=.
        
    (* AppRec *)
    - move=> o' o1 d1 d2 d' v1 v2 H1 IH1 H2 IH2 H' IH' k H.
      inv: H => H4 H6 e He.
      case: (IH1 c1 H4 e He) => mv1 [Hc1 H1'] {H1 H4 IH1}.
      move: (Hc1); inv=> H5 H8.             (* dup 複製する。 *)
      case: (IH2 c2 H6 e He) => mv2 [Hc2 H2'] {H2 H6 IH2}.
      have He' : Compiler_SS_env (v1 :: (vClosRec d' o1) :: o1)
                                 (mv2 :: (mClosRec (c ++ [:: iRet]) e0) :: e0).
        by apply: Compiler_SS_env_cons; [apply: Compiler_SS_env_cons |].
      case: (IH' c H5 (mv2 :: (mClosRec (c ++ [:: iRet]) e0) :: e0) He')
        => mv' [Hc' H''] {H5 IH'}.
      exists mv'.
      split => // s k.
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H1' |].
      rewrite -catA.
      apply: RTC_MSECD_SS_Trans; [apply: H2' |].
      apply: RTC_MSECD_SS_Step => //=.
      apply: RTC_MSECD_SS_Trans; [apply: H'' |].
        by apply: RTC_MSECD_SS_Step => /=.
  Qed.

End Compiler.


(* END *)
