From mathcomp Require Import all_ssreflect.
Require Import ssrstring.                   (* Ascii String *)
Require Import Recdef.                      (* Function *)

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

Section Sexp.

  Inductive sexp :=
  | v_n of nat
  | v_b of bool
  | v_l of seq sexp.

  Function ssize (l : sexp) : nat :=
    match l with
    | v_n _ => 1
    | v_b _ => 1
    | v_l l => (foldr (fun x y => addn (ssize x) y) 0 l).+1
    end.

  Compute ssize (v_n 0).                    (* 1 *)
  Compute ssize (v_l [:: v_n  0]).          (* 2 *)
  
  Fail Function eqSexp (x y : sexp) {measure ssize x} : bool :=
    match (x, y) with
    | (v_n x, v_n y) => x == y
    | (v_l x, v_l y) => foldr andb true
                              (map2 (fun x1 y1 => eqSexp x1 y1) x y)
    | (_, _) => false
    end.
  
End Sexp.

Section Program.

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
  | none                                    (* constr' の基底 *)
  | constr' of program & program            (* XXX evaluator XXX *)
  | constr of seq program                   (* XXX compiler XXX *)
  | condit of program & program & program
  | insert of program                       (* foldr *)
  | alpha of program                        (* map / apply all *)
  .    

  Function psize (p : program) : nat :=
    match p with
    | intrin _ => 1
    | compos p1 p2 => psize p1 + psize p2
    | none => 0
    | constr' p1 p2 => psize p1 + psize p2
    | constr ps => (foldr (fun x y => addn (psize x) y) 0 ps).+1
    | condit p1 p2 p3 =>  psize p1 + psize p2 + psize p3
    | insert p => 1
    | alpha p => 1
    end.
  
End Program.

Definition VN99 := v_n 99.

Section Evaluator.

  (* notu *)
  Function ApplyMapC f (ps : seq program) {measure size ps} : option sexp :=
    match ps with
    | [::] => Some (v_l [::])
    | p1 :: p2 =>
      match f p1 with
      | Some y1 =>
        match ApplyMapC f p2 with
        | Some (v_l y2) => Some (v_l (y1 :: y2))
        | _ => None
        end
      | _ => None
      end
    end.
  Proof.
      by move=> f l1 x1 x2 IH1 y1 IH2.
  Qed.
  
  Function ApplyFold f (l : seq sexp) {measure size l} : option sexp :=
    match l with
    | [::] => None
    | [:: x] => Some x
    | x :: y :: l =>
      match ApplyFold f (y :: l) with
      | Some v => f x v
      | _ => None
      end
    end.
  Proof.
      by move=> _ l1 x l2 y l3 IHl1 IHl2.
  Qed.
  
  Function ApplyMapA f (l : seq sexp) {measure size l} : option sexp :=
    match l with
    | [::] => Some (v_l [::])
    | x1 :: x2 =>
      match f x1 with
      | Some y1 =>
        match ApplyMapA f x2 with
        | Some (v_l y2) => Some (v_l (y1 :: y2))
        | _ => None
        end
      | _ => None
      end
    end.
  Proof.
      by move=> f l1 x1 x2 IH1 y1 IH2.
  Qed.
  
(**
map と fold を使うと、相互再帰にしなくても済む。
*)
  Fixpoint Apply (p : program) (x : sexp) : option sexp :=
    match p with
    | intrin add =>
      match x with
      | v_l [:: v_n x; v_n y] => Some (v_n (x + y))
      | _ => None
      end
    | intrin (sel n) =>
      match x with
      | v_l l => Some (nth VN99 l n.-1)
      | _ => None
      end
    | none => Some (v_l [::])               (* constr' の基底 *)
    | constr' p1 p2 =>
      match Apply p1 x with
      | Some y1 =>
        match Apply p2 x with
        | Some (v_l y2) => Some (v_l (y1 :: y2))
        | _ => None
        end
      | _ => None
      end
(*
    | constr ps => ApplyMapC (fun p => Apply p x) ps
*)      
    | condit p1 p2 p3 =>
      match (Apply p1 x) with
      | Some (v_b true) => Apply p2 x
      | Some (v_b false) => Apply p3 x
      | _ => None
      end
    | insert p =>
      match x with
      | v_l l => ApplyFold (fun x y => Apply p (v_l [:: x; y])) l
      | _ => None
      end
    | alpha p =>
      match x with
      | v_l l => ApplyMapA (fun x => Apply p x) l
      | _ => None
      end
    | _ => None
    end.
  
End Evaluator.

Section Compile.
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
  
(**
mapall (alpha) や foldr (insert) は、
Dのデータのサイズで動作を変えるインストラクションを追加する必要がある
*)
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

Section Emulator.
  Fixpoint scd (c : code) (d s : seq sexp) {struct c} :=
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

Section Step.

  Inductive ns : option sexp -> program -> option sexp -> Prop :=
  | ns_add_ok x y :
      ns (Some (v_l [:: v_n x; v_n y]))
         (intrin add)
         (Some (v_n (x + y)))
  | ns_sel_ok l n :
      ns (Some (v_l l))
         (intrin (sel n))
         (Some (nth VN99 l n.-1))
  | ns_constr x ps y :
      ns_mapc (Some x) ps (Some y) ->
      ns (Some x)
         (constr ps)
         (Some (v_l y))
  | ns_condit_true x p1 p2 p3 y :
      ns (Some x) p1 (Some (v_b true)) ->
      ns (Some x) p2 (Some y) ->
      ns (Some x) (condit p1 p2 p3) (Some y)
  | ns_condit_false x p1 p2 p3 y :
      ns (Some x) p1 (Some (v_b false)) ->
      ns (Some x) p3 (Some y) ->
      ns (Some x) (condit p1 p2 p3) (Some y)
  | ns_insert x p y :
      ns_fold (Some x) p (Some y) ->
      ns (Some (v_l x))
         p
         (Some y)
  | ns_alpha x p y :
      ns_mapa (Some x) p (Some y) ->
      ns (Some (v_l x))
         (alpha p)
         (Some (v_l y))
  with ns_mapc : option sexp -> seq program -> option (seq sexp) -> Prop :=
       | ns_constr_nil x :
           ns_mapc (Some x) [::] (Some [::])
       | ns_constr_cons x p1 p2 y1 y2 :
           ns (Some x) p1 (Some y1) ->
           ns_mapc (Some x) p2 (Some y2) ->
           ns_mapc (Some x) (p1 :: p2) (Some (y1 :: y2))
  with ns_fold : option (seq sexp) -> program -> option sexp -> Prop :=
       | ns_fold_nil a p :
           ns_fold (Some [:: a]) p (Some a)
       | ns_fold_cons x1 x2 p y1 y2 :
           ns_fold (Some x2) p (Some y2) ->
           ns (Some (v_l [:: x1; y2])) p y1 ->
           ns_fold (Some (x1 :: x2)) p y1
  with ns_mapa : option (seq sexp) -> program -> option (seq sexp) -> Prop :=
       | ns_mapa_nil p :
           ns_mapa (Some [::]) p (Some [::])
       | ns_mapa_cons x1 x2 p y1 y2 :
           ns (Some x1) p (Some y1) ->
           ns_mapa (Some x2) p (Some y2) ->
           ns_mapa (Some (x1 :: x2)) p (Some (y1 :: y2))
  .
End Step.
  
(* END *)
