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
  | sel of nat
  | tl
  | id
  | atom
  | equals
  | null
  | reverse
  | distl
  | distr
  | length      
  | add
  | sub
  | mul
  | div
  | and
  (* trans *) (* transpose *)
  | or
  | not
  | apndl                                   (* cons *)
  | apndr                                   (* snoc *)
  (* rsel of nat *)
  (* rotl of nat *)
  (* rotr of nat *)
  | compose of program & program
  | cons of seq program
  | cond of program & program & program
  | const of object
  | insert of program                       (* foldr *)
  | alpha of program                        (* map / apply all *)
  | bu of program & object                  (* binary to unary *)
  | while of program & program
  .    
  (* 再帰呼び出し。 *)
  
End Program.

(**
# Big Step (Natural semantics)
*)
Check map  (fun x => [:: 1; x]) [::1; 2; 3].
Section BigStep.
  
  Inductive ns : object -> program -> object -> Prop :=
  | ns_none f :
      ns None                            f                 None
  (* *** *)
  | ns_sel xs n :
      ns (Some (ol xs))                  (sel n)           (option_nth1 xs n)
  | ns_tl x xs :
      ns (Some (ol (x :: xs)))           tl                (Some (ol xs))
  | ns_id x :
      ns (Some x)                        id                (Some x)
  | ns_atom_nat m :
      ns (Some (on m))                   atom              (Some (ob false))
  | ns_atom_bool x :
      ns (Some (ob x))                   atom              (Some (ob false))
  | ns_atom_char x :
      ns (Some (oc x))                   atom              (Some (ob false))
  | ns_atom_string x :
      ns (Some (os x))                   atom              (Some (ob false))
  | ns_atom_list x :
      ns (Some (ol x))                   atom              (Some (ob true))
  | ns_equals_true y :
      ns (Some (ol [:: y; y]))           equals            (Some (ob true))
  | ns_equals_false y z :
      y <> z ->
      ns (Some (ol [:: y; z]))           equals            (Some (ob false))
  | ns_null_true :
      ns (Some (ol [::]))                null              (Some (ob true))
  | ns_null_false x l :
      ns (Some (ol (x :: l)))            null              (Some (ob false))
  | ns_reverse l  :
      ns (Some (ol l))                   reverse           (Some (ol (rev l)))
  | ns_distl y zs :
      ns (Some (ol [:: y; ol zs]))       distl  (Some (ol [seq ol [:: y; z] | z <- zs]))
  | ns_distr ys z :
      ns (Some (ol [:: ol ys; z]))       distl  (Some (ol [seq ol [:: y; z] | y <- ys]))
  | ns_length xs :
      ns (Some (ol xs))                  length            (Some (on (size xs)))
  | ns_add m n :
      ns (Some (ol [:: on m; on n]))     add               (Some (on (m + n)))
  | ns_sub m n :
      ns (Some (ol [:: on m; on n]))     sub               (Some (on (m - n)))
  | ns_mul m n :
      ns (Some (ol [:: on m; on n]))     mul               (Some (on (m * n)))
  | ns_div m n :
      n <> 0 ->
      ns (Some (ol [:: on m; on n]))     div               (Some (on (m %/ n)))
  | ns_div_zero m :
      ns (Some (ol [:: on m; on 0]))     div               None
  | ns_and b c :
      ns (Some (ol [:: ob b; ob c]))     and               (Some (ob (b && c)))
  | ns_or b c :
      ns (Some (ol [:: ob b; ob c]))     or                (Some (ob (b || c)))
  | ns_not b :
      ns (Some (ob b))                   not               (Some (ob (~~ b)))
  | ns_apndl y zs :
      ns (Some (ol [:: y; ol zs]))       apndl             (Some (ol (y :: zs)))
  | ns_apndr ys z :
      ns (Some (ol [:: ol ys; z]))       apndr             (Some (ol (rcons ys z)))
  (* *** *)
  (* composition *)
  | ns_compose f g x y z :
      ns (Some x)                        g                 (Some y) ->
      ns (Some y)                        f                 z ->
      ns (Some x)                        (compose f g)     z
  | ns_compose_none f g x :
      ns (Some x)                        g                 None ->
      ns (Some x)                        (compose f g)     None
  (* construction *)
  | ns_cons x fs y :
      ns_mapc (Some x)                   fs                (Some y) ->
      ns (Some x)                        (cons fs)         (Some (ol y))
  | ns_cons_none x fs :
      ns_mapc (Some x)                   fs                None ->
      ns (Some x)                        (cons fs)         None
  (* condition *)
  | ns_cond_true x p f g y :
      ns (Some x)                        p                (Some (ob true)) ->
      ns (Some x)                        f                y ->
      ns (Some x)                        (cond p f g)     y
  | ns_cond_false x p f g y :
      ns (Some x)                        p                (Some (ob false)) ->
      ns (Some x)                        g                y ->
      ns (Some x)                        (cond p f g)     y
  | ns_cond_none x p f g :
      ns (Some x)                        p                None ->
      ns (Some x)                        (cond p f g)     None
  (* constant *)
  (* 与えられた定数 y によらず、スタック上の引数がNoneならNoneにする。
     一方、定数としてNoneを与えることも可能とする。 *)
  | ns_const x y :
      ns (Some x)                        (const y)         y
  (* insert, foldr *)
  | ns_insert x f y :
      ns_foldr (Some x)                  f                 y ->
      ns (Some (ol x))                   (insert f)        y
  (* alpha, apply-all *)
  | ns_alpha x f y :
      ns_mapa (Some x)                   f                 (Some y) ->
      ns (Some (ol x))                   (alpha f)         (Some (ol y))
  | ns_alpha_none x f :
      ns_mapa (Some x)                   f                 None ->
      ns (Some (ol x))                   (alpha f)         None
  (* bu *)
  | ns_bu f x y z :
      ns (Some (ol [:: x; y]))           f                 (Some z) ->
      ns (Some y)                        (bu f (Some x))   (Some y)
  | ns_bu_none f y :
      ns (Some y)                        (bu f None)       None
  (* while *)
  | ns_while_true p f x y z :
      ns (Some x)                        p                 (Some (ob true)) ->
      ns (Some x)                        f                 (Some y) ->
      ns (Some y)                        (while p f)       z ->
      ns (Some x)                        (while p f)       z
  | ns_while_false p f x :
      ns (Some x)                        p                 (Some (ob false)) ->
      ns (Some x)                        (while p f)       (Some x)
  | ns_while_none p f x :
      ns (Some x)                        p                 None ->
      ns (Some x)                        (while p f)       None
  with ns_mapc : option sexp -> seq program -> option (seq sexp) -> Prop :=
       | ns_constr_nil x :
           ns_mapc (Some x) [::] (Some [::])
       | ns_constr_cons x f1 f2 y1 y2 :
           ns (Some x) f1 (Some y1) ->
           ns_mapc (Some x) f2 (Some y2) ->
           ns_mapc (Some x) (f1 :: f2) (Some (y1 :: y2))
  with ns_foldr : option (seq sexp) -> program -> option sexp -> Prop :=
       (* [::] に対する fold は intrinsics に限定する。 *)
       | ns_foldr_nil_equals : ns_foldr (Some [::]) add (Some (ob true))
       | ns_foldr_nil_add : ns_foldr (Some [::]) add (Some (on 0))
       | ns_foldr_nil_sub : ns_foldr (Some [::]) sub (Some (on 0))
       | ns_foldr_nil_mul : ns_foldr (Some [::]) mul (Some (on 1))
       | ns_foldr_nil_div : ns_foldr (Some [::]) div (Some (on 1))
       | ns_foldr_nil_and : ns_foldr (Some [::]) and (Some (ob true))
       | ns_foldr_nil_or : ns_foldr (Some [::]) and (Some (ob false))
       | ns_foldr_nil_apndl : ns_foldr (Some [::]) apndl (Some (ol [::]))
       (* *** *)
       | ns_foldr_one a f :
           ns_foldr (Some [:: a]) f (Some a)
       | ns_foldr_cons x1 x2 f y1 y2 :
           ns_foldr (Some x2) f (Some y2) ->
           ns (Some (ol [:: x1; y2])) f y1 ->
           ns_foldr (Some (x1 :: x2)) f y1
  with ns_mapa : option (seq sexp) -> program -> option (seq sexp) -> Prop :=
       | ns_mapa_nil f :
           ns_mapa (Some [::]) f (Some [::])
       | ns_mapa_cons x1 x2 f y1 y2 :
           ns (Some x1) f (Some y1) ->
           ns_mapa (Some x2) f (Some y2) ->
           ns_mapa (Some (x1 :: x2)) f (Some (y1 :: y2))
  .

End BigStep.

Hint Constructors ns. 
Hint Constructors ns_foldr.

Lemma test1 : ns (Some (ol [:: on 1; on 2])) add (Some (on 3)).
Proof.
  by apply: ns_add.
Qed.  

Lemma test2 : ns (Some (ol [:: on 1; on 2; on 3])) (insert add) (Some (on 6)).
Proof.
  apply: ns_insert.
  apply: ns_foldr_cons.
  - apply: ns_foldr_cons.
    + apply: ns_foldr_one.
    + apply: ns_add.
  - apply: ns_add.
Qed.

(* END *)
