From mathcomp Require Import all_ssreflect.
Require Import ssrstring.                   (* Ascii String *)
Require Import Recdef.                      (* Function *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Options.
  
  Variable T : Type.
  
  Fixpoint option_nth (s : seq T) (n : nat) : option T :=
    match s with
    | [::] => None
    | x :: s' => match n with
                 | 0 => Some x
                 | n'.+1 => option_nth s' n'
                 end
    end.
  
  Fixpoint option_nth1 (s : seq T) (n : nat) : option T :=
    match s with
    | [::] => None
    | x :: s' => match n with
                 | 0 => None
                 | 1 => Some x
                 | n'.+1 => option_nth s' n'
                 end
    end.

End Options.

Section Data.

  Inductive sexp :=
  | on of nat
  | ob of bool
  | oc of ascii
  | os of string
  | ol of seq sexp.

  Definition object := option sexp.
End Data.

Section Program.

  Inductive program :=
  | add
  | sub
  | mul
  | div
  | atom
  | equals
  | sel of nat
  | compos of program & program
  | constr of seq program
  | condit of program & program & program
  | insert of program                       (* foldr *)
  | alpha of program                        (* map / apply all *)
  .    

End Program.

(**
# Big Step (Natural semantics)
*)
Section BigStep.
  
  Inductive ns : object -> program -> object -> Prop :=
  | ns_add x y :
      ns (Some (ol [:: on x; on y]))     add               (Some (on (x + y)))
  | ns_sub x y :
      ns (Some (ol [:: on x; on y]))     sub               (Some (on (x - y)))
  | ns_mul x y :
      ns (Some (ol [:: on x; on y]))     mul               (Some (on (x * y)))
  | ns_div x y :
      ns (Some (ol [:: on x; on y]))     div               (Some (on (x %/ y)))
  | ns_atom_nat x :
      ns (Some (on x))                   atom              (Some (ob false))
  | ns_atom_bool x :
      ns (Some (ob x))                   atom              (Some (ob false))
  | ns_atom_char x :
      ns (Some (oc x))                   atom              (Some (ob false))
  | ns_atom_string x :
      ns (Some (os x))                   atom              (Some (ob false))
  | ns_atom_list x :
      ns (Some (ol x))                   atom              (Some (ob true))
  | ns_equal_true x :
      ns (Some (ol [:: x; x]))           equals            (Some (ob true))
  | ns_equal_false x y :
      x <> y ->
      ns (Some (ol [:: x; y]))           equals            (Some (ob false))
  | ns_sel l n :
      ns (Some (ol l))                   (sel n)           (option_nth1 l n)
  | ns_constr x ps y :
      ns_mapc (Some x)                   ps                (Some y) ->
      ns (Some x)                        (constr ps)       (Some (ol y))
  | ns_condit_true x p1 p2 p3 y :
      ns (Some x)                        p1                (Some (ob true)) ->
      ns (Some x)                        p2                (Some y) ->
      ns (Some x)                        (condit p1 p2 p3) (Some y)
  | ns_condit_false x p1 p2 p3 y :
      ns (Some x)                        p1                (Some (ob false)) ->
      ns (Some x)                        p3                (Some y) ->
      ns (Some x)                        (condit p1 p2 p3) (Some y)
  | ns_insert x p y :
      ns_fold (Some x)                   p                 (Some y) ->
      ns (Some (ol x))                   (insert p )       (Some y)
  | ns_alpha x p y :
      ns_mapa (Some x)                   p                 (Some y) ->
      ns (Some (ol x))                   (alpha p)         (Some (ol y))
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
           ns (Some (ol [:: x1; y2])) p y1 ->
           ns_fold (Some (x1 :: x2)) p y1
  with ns_mapa : option (seq sexp) -> program -> option (seq sexp) -> Prop :=
       | ns_mapa_nil p :
           ns_mapa (Some [::]) p (Some [::])
       | ns_mapa_cons x1 x2 p y1 y2 :
           ns (Some x1) p (Some y1) ->
           ns_mapa (Some x2) p (Some y2) ->
           ns_mapa (Some (x1 :: x2)) p (Some (y1 :: y2))
  .

End BigStep.

Hint Constructors ns.
Hint Constructors ns_fold.

Lemma test1 : ns (Some (ol [:: on 1; on 2])) add (Some (on 3)).
Proof.
  by apply: ns_add.
Qed.  

Lemma test2 : ns (Some (ol [:: on 1; on 2; on 3])) (insert add) (Some (on 6)).
Proof.
  apply: ns_insert.
  apply: ns_fold_cons.
  - apply: ns_fold_cons.
    + apply: ns_fold_nil.
    + apply: ns_add.
  - apply: ns_add.
Qed.

(* END *)
