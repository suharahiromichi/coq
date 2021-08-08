From mathcomp Require Import all_ssreflect.
Require Import ssrstring.                   (* Ascii String *)
Require Import ssrstar.                     (* S-EXP *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Map2.

  Variable T1 T2 : Type.
  
  Check @seq_ind2.

  Fixpoint map2 op (s1 s2 : seq T1) : seq T2 :=
    match s1, s2 with
    | [::], _ => [::]
    | _, [::] => [::]
    | (x1 :: s1), (x2 :: s2) => (op x1 x2) :: map2 op s1 s2
    end.

End Map2.

Section Data.

  Inductive data :=
  | v_n of nat
  | v_l of seq data.

  Fail Fixpoint eqData (x y : data) : bool :=
    match (x, y) with
    | (v_n x, v_n y) => x == y
    | (v_l x, v_l y) => foldr andb true
                              (map2 (fun x1 y1 => eqData x1 y1) x y)
    | (_, _) => false
    end.

End Data.

Section Compile.

  Inductive instr :=
  | iAdd
  | iSel of nat                        (* Dのnth要素をSにpushする。 *)
  | iDDup                              (* Dをコピーする。 *)
  | iDDrp                              (* Dの先頭を捨てる。 *)
(*| iDtoS                              (* DをSに移動する。 *) *)
  | iStoD                              (* SをDに移動する。 *)
  | iList of nat                       (* Sのn個をpopしてリストにする。 *)
  .

  Definition code := seq instr.

  Inductive intrinsics :=
  | add
  | sel of nat
  .
  
  Inductive program :=
  | intrin of intrinsics
  | compos of program & program
  | constr of seq program
  | condit of program & program & program
  | insert of program
  | alpha of program                        (* apply all *)
  .    

(**
プログラムの引数は D に、結果は S に置かれる。
*)
  
  Fixpoint compile (p : program) : code :=
    match p with
    | intrin add => [:: iAdd]
    | intrin (sel n) => [:: iSel n.-1]
    | compos p1 p2 => compile p2 ++ [:: iDDrp; iStoD] ++ compile p1
    | constr l =>
      flatten (map (fun q => [:: iDDup] ++ compile q ++ [:: iDDrp]) l)
              ++ [:: iList (size l)] 
    | _ => [::]
    end.
  
End Compile.

Section Test.

  Definition p1 := compos (intrin add)
                          (constr [:: intrin (sel 2); intrin (sel 1)]).
  Compute compile p1.
  (* = [:: iDDup; iSel 1; iDDrp; iDDup; iSel 0; iDDrp; iList 2; iDDrp; iStoD; iAdd] *)

  Definition p2 := compos (intrin add)
                          (constr
                             [::
                                (compos (intrin add)
                                        (constr [:: intrin (sel 2); intrin (sel 1)]));
                                (compos (intrin add)
                                        (constr [:: intrin (sel 2); intrin (sel 1)]))]).

  Compute compile p2.
  (* D には最初の入力がある。 *)
  Check [::
           iDDup;
               iDDup; iSel 2; iDDrp;
               iDDup; iSel 1; iDDrp;
           iList 2;
           iDDrp;

           iStoD; iAdd; iDDrp;
           iDDup;
               iDDup; iSel 2; iDDrp;
               iDDup; iSel 1; iDDrp;
           iList 2;
           iDDrp;

           iStoD; iAdd; iDDrp;
             
           iList 2;
           iDDrp;                           (* 最初の入力を捨てる。 *)
           
           iStoD; iAdd].

End Test.

Definition VN99 := v_n 99.

Section Emulator.
  Fixpoint scd (c : code) (d s : seq data) {struct c} :=
    match (c, d, s) with
    | (iAdd :: c', v_l [:: v_n n2; v_n n1] :: d', s') => scd c' d  (v_n  (n1 + n2) :: s')
    | (iSel n :: c',               (v_l e) :: d', s') => scd c' d    (nth VN99 e n :: s')
    | (iDDup :: c',                      e :: d', s') => scd c' (e :: e :: d')        s'
    | (iDDrp :: c',                      e :: d', s') => scd c' d'                    s'

    | (iStoD :: c',                d', e :: s') => scd c' (e :: d')              s'

    | (iList 1 :: c', d',             v1 :: s') => scd c' d'     (v_l [:: v1] :: s')
    | (iList 2 :: c', d',       v2 :: v1 :: s') => scd c' d' (v_l [:: v1; v2] :: s')
    | (iList 3 :: c', d',       v3 :: v2 :: v1 :: s') =>
      scd c' d' (v_l [:: v1; v2; v3] :: s')
    | (iList 4 :: c', d', v4 :: v3 :: v2 :: v1 :: s') =>
      scd c' d' (v_l [:: v1; v2; v3; v4] :: s')

    | ([::],          d',        v :: s') => ([::], d', v :: s')
    | (c', e', s') =>                        (c', e', s') (* error *)
    end.
  
  Compute scd (compile p1) [:: v_l [:: v_n 1; v_n 2]] [::].
  Compute scd [:: iDDup; iSel 1; iDDrp; iDDup; iSel 0; iDDrp; iList 2; iDDrp; iStoD; iAdd]
    [:: v_l [:: v_n 1; v_n 2]] [::].
  
  Compute scd (compile p2) [:: v_l [:: v_n 1; v_n 2]] [::].  

End Emulator.

(* END *)
