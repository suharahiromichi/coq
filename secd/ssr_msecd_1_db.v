From mathcomp Require Import all_ssreflect.
Require Import ssrinv.
Require Import ssr_msecd_1_defs.

(** de Bruijn notation MiniMLdB *)

Section MiniMLdB.
  
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
      inv: H.
      split.
      * by apply: dB_translation_NS_val_Nat.
      * by apply: MML_dB_NS_Nat.

    (* Bool *)
    - move=> g' b o He d H.
      exists (vBool b).
      inv: H.
      split.
      * by apply: dB_translation_NS_val_Bool.
      * by apply: MML_dB_NS_Bool.

    (* Plus *)
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
      inv: H => H5 H7.
      case: (IH1 o He d0 H5) => d1' [H11 H12].
      inv: H11.
      case: (IH2 o He d3 H7) => d2' [H21 H22].
      inv: H21.
      exists (vNat (m + n)).
      split.
      + by apply: dB_translation_NS_val_Nat.
      + apply: MML_dB_NS_Plus.
        * by apply: H12.
        * by apply: H22.

    (* Minus *)
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
      inv: H => H5 H7.
      case: (IH1 o He d0 H5) => d1' [H11 H12].
      inv: H11.
      case: (IH2 o He d3 H7) => d2' [H21 H22].
      inv: H21.
      exists (vNat (m - n)).
      split.
      + by apply: dB_translation_NS_val_Nat.
      + apply: MML_dB_NS_Minus.
        * by apply: H12.
        * by apply: H22.

    (* Times *)
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
      inv: H => H5 H7.
      case: (IH1 o He d0 H5) => d1' [H11 H12].
      inv: H11.
      case: (IH2 o He d3 H7) => d2' [H21 H22].
      inv: H21.
      exists (vNat (m * n)).
      split.
      + by apply: dB_translation_NS_val_Nat.
      + apply: MML_dB_NS_Times.
        * by apply: H12.
        * by apply: H22.

    (* Eq *)
    - move=> g' d1 d2 m n H1 IH1 H2 IH2 o He d H.
      by inv: H.

    (* Var *)
    - move=> g' x o He d H.
      inv: H.
      exists (olookup (index x (mkctx g')) o).
      split.
      * inv: He => H0.
        by apply: H0.
      * by apply: MML_dB_NS_Var.
        
    (* Let *)
    - move=> g' x e1 e2 v1 v2 H1 IH1 H2 IH2 o He d H.
      inv: H => H7 H8.
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
      inv: H => H6 H8 H9.
      case: (IH1 o He d1 H6) => v1' [H11 H12].
      inv: H11.
      case: (IH2 o He d2 H8) => v2' [H21 H22].
      exists v2'.
      split.
      + by apply: H21.
      + apply: MML_dB_NS_Iftrue.
        * invs: H12 => [m n H0 H5 H | H].
          ** by apply: MML_dB_NS_Eq.
          ** by apply: MML_dB_NS_Var.
        * by apply: H22.
          
    (* If false *)
    - move=> g' e1 e2 e3 v3 H1 IH1 H3 IH3 o He d H.
      (* v3 は else 節 *)
      inv: H => H6 H8 H9.
      case: (IH1 o He d1 H6) => v1' [H11 H12].
      inv: H11.
      case: (IH3 o He d3 H9) => v3' [H31 H32].
      exists v3'.
      split.
      + by apply: H31.
      + apply: MML_dB_NS_Iffalse.
        * invs: H12.
          ** move=> m n H0 H5 H.
               by apply: MML_dB_NS_Eq.
          ** move=> H.
               by apply: MML_dB_NS_Var.
        * by apply: H32.
          
    (* Lam *)
    - move=> g' x e' o He d H.
      inv: H.
      exists (vClos d0 o).
      split.
      + by apply: db_translation_NS_val_Clos.
      + by apply: MML_dB_NS_Lam.

    (* MuLam *)
    - move=> g' f x e' o He d H.
      inv: H.
      exists (vClosRec d0 o).
      split.
      + apply: db_translation_NS_val_ClosRec.
        * by apply: He.
        * by apply: H5.
      + by apply: MML_dB_NS_MuLam.

    (* App Clos *)
    - move=> g' g3 x e1 e2 e3 v2 v3 H1 IH1 H2 IH2 H3 IH3 o He d H.
      inv: H => H6 H8.
      case: (IH1 o He d1 H6) => v1' [H11 H12] {IH1}. (* 関数部 *)
      inv: H11 => H9 H10.
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
      inv: H => H6 H8.
      case: (IH1 o He d1 H6) => v1' [H11 H12] {IH1}. (* 関数部 *)
      move: (H11); inv=> H10 H13. (* keep、 あらかじめ複製 duplicate *)
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


(* END *)
