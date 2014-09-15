(* http://ilyasergey.net/pnp/ *)

(** * 「Hoare Type Theory の基礎」から抜粋 *)
(** * Elements of Hoare Type Theory *)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import prelude pred pcm unionmap heap heaptac
        stmod stsep stlog stlogR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Specifying and verifying programs with linked lists *)
(** リンクリストのプログラムの仕様記述と検証 *)

Definition llist (T : Type) := ptr.

Section LList.
Variable T : Type.
Notation llist := (llist T).

(**
ヒープがどのように格納されているかと、seq との関係を明確にする。
ポインタpとqはリストの先頭と末尾を指す。
論理的な要素 xs は、そのリストに保存される。
*)

Fixpoint lseg (p q : ptr) (xs : seq T) : Pred heap := 
  if xs is x::xt then 
    [Pred h | exists r h',
              (h = p :-> x \+ ((p .+ 1 :-> r) \+ h')) /\ h' \In lseg r q xt]
  else
    [Pred h | p = q /\ h = Unit].

(** 
[Pred h | ..] は、heap -> Prep 型である。
h \In f は、f h と同義である。

次の補題は、リンクスリトに関係づけられたヒープhが与えられたとき、
先頭ポインタpがnullならば、
末尾ポインタqがnullで、リスト全体が[::]であることを示す。
*)

Lemma lseg_null xs q h : 
  valid h -> h \In lseg null q xs -> 
  [/\ q = null, xs = [::] & h = Unit].
Proof.
  case: xs.
  - move=> /= D H.
    by case: H => <- ->.
  - move=> x xs /= D H.
    case: H D => r [] h' [] -> _.
    (* =>の右の最初の[]はexist、次の[]は/\を場合分けする。
       最後は、h=... でrewriteする。*)
    Check   hvalidPtUn.                     (* heap.v で定義 *)
    rewrite hvalidPtUn => /=.
    (* -> の左を書き換えると false になる。 *)
    done.
Qed.

(**  
linked listの典型例であるnullターミネートされた場合について、
単純な挿入のプログラム、
新しいメモリセルをアロケートしてそれをリストの新しい先頭にする、
の仕様を証明する。
*)

Definition lseq p := lseg p null.

(** pが先頭のリストに、値がxのセルを追加する。新しい先頭はqでそれを返値とする。 *)
Program Definition insert p x :
  {xs},
  STsep (lseq p xs,                         (* 事前 *)
         [vfun y => lseq y (x::xs)]) :=     (* 事後 *)
  Do (q <-- allocb p 2; 
      q ::= x;;
      ret q).
Next Obligation.
  apply: ghR => h' xs H _.

  heval=> x1.
  Undo 1.
  apply: bnd_allocbR => /= q.
  apply: bnd_writeR => /=.

  rewrite unitR -joinA.
  
  heval.
  Undo 1.
  apply: val_ret => /=.
  rewrite /lseq /lseq /= => D.
  exists p, h'.
  split.
  - by [].
  - rewrite /lseq in H.
    by apply H.
Qed.

(** 
beheading (リストの最初の要素を取り除く) プログラムの仕様を与える。
ふたつの補題を証明する。
（補足：最初のひとつは、先頭ポインタがnillなら、リスト全体が[::]で、
ヒープも空であることを示す。）
*)

Lemma lseq_null xs h :
  valid h ->
  h \In lseq null xs -> xs = [::] /\ h = Unit.
Proof.
    by move=> D; case/(lseg_null D) => _ ->.
Qed.

(** 
次の補題は、heepで与えられたlinked listの先頭がnullでないなら、
beheadedできることを示す。
先頭の値xと、次のポインタrと、残りのヒープh'が存在して、
ヒープh'は、リストのtail(SSReflect の behead関数で表される)に対応する。
*)

Lemma lseq_pos xs p h : 
        p != null -> h \In lseq p xs -> 
        exists x, exists r, exists h', 
          [/\ xs = x :: behead xs, 
              p :-> x \+ (p .+ 1 :-> r \+ h') = h & h' \In lseq r (behead xs)].
Proof.
  case: xs => [|x xs] /= H [].
  - move => E.
      by rewrite E eq_refl in H.
  - by move => y [h'][->] H1; heval.
    Undo 1.
    rewrite -/lseg.
    move => y [h'][->] H1.
    exists x, y, h'.
    split.
    + by [].
    + by [].
    + rewrite /lseq.
        by apply H1.
Qed.

(** 
remove手続は、リストの現在の先頭を取り除き、
次の要素（またはリストが空のときnull）を返す。
*)

Program Definition 
remove p :
  {xs},
  STsep (lseq p xs,
         [vfun y => lseq y (behead xs)]) :=
  Do (if p == null then
        ret p 
      else
        pnext <-- !(p .+ 1);
        dealloc p;; 
        dealloc p .+ 1;;
        ret pnext).
(** 
証明は簡単であり、リストがnullのときに、lesq_nullを適用し、
リストがひとつ以上の要素を持つとき、lseq_posを適用する。
*)

Next Obligation.
  apply: ghR => i xs H V.
  Check ifP.
  case: ifP H => H1.

  - rewrite (eqP H1); case/(lseq_null V) => -> ->.
    heval. 
    Undo 1.
    Search _ (verify _ (ret _) _).
    apply: val_ret => /= D.
    rewrite /lseq /lseg /=.
    by [].

  - case/(lseq_pos (negbT H1)) => x [q][h][->] <- /= H2.
    heval.
    Undo 1.
    apply: bnd_readR => /=.
    apply: bnd_deallocR => /=.
    apply: bnd_deallocR => /=.
    apply: val_ret => /=.

    rewrite 2!unitL.
    by [].
    Undo 1.
    move=> D. by apply: H2.
Qed.

End LList.

(** 例題 *)

(** 
---------------------------------------------------------------------
Exercise [Value-returning list beheading]
---------------------------------------------------------------------

Define and verify function [remove_val] which is similar to [remove],
but also returns the value of the last "head" of the list before
removal, in addition to the "next" pointer. Use Coq's [option] type to
account for the possibility of an empty list in the result.

*)

(** 
---------------------------------------------------------------------
Exercise [Imperative in-place map]
---------------------------------------------------------------------

Define, specify and verify the imperative higher-order function
[list_map] that takes arguments two types, [S] and [T], a pure
function [f : T -> S] and a head [p] of a single-linked list,
described by a predicate [lseq], and changes the list in place by
applying [f] to each of its elements, while preserving the list's
structure. The specification should reflect the fact that the new
"logical" contents of the single-linked list are an [f] map-image of
the old content.

Hint: The lemmas [lseq_null] and [lseq_pos], proved previously, might
be useful in the proof of the established specification.

Hint: A tail-recursive call can be verified via HTT's [val_do] lemma,
reminiscent to the rule %\Rule{App}%. However, the heap it operates
with should be "massaged" appropriately via PCM's lemmas [joinC] and
[joinA].

Hint: A boolean lemma [negbT] can be useful to switch between
different representations of inequality.

*)

(**
---------------------------------------------------------------------
Exercise [In-place list reversal]
---------------------------------------------------------------------

Let us define the following auxiliary predicates, where [shape_rev]
splits the heap into two disjoint linked lists (by means of the
separating conjunction [#]).

*)

Definition shape_rev T p s := [Pred h | h \In @lseq T p.1 s.1 # @lseq T p.2 s.2].

(** 

Then the in-place list reversal is implemented by means of the
recursive function [reverse] with a loop invariant expressed using the
type [revT].

*)

Definition revT T : Type := 
  forall p, {ps}, STsep (@shape_rev T p ps, [vfun y => lseq y (rev ps.1 ++ ps.2)]).

Program Definition 
reverse T p : {xs}, STsep (@lseq T p xs, [vfun y => lseq y (rev xs)]) :=
  Do (let: reverse := Fix (fun (reverse : revT T) p =>
                        Do (if p.1 == null then ret p.2 
                            else xnext <-- !p.1 .+ 1;
                                 p.1 .+ 1 ::= p.2;;
                                 reverse (xnext, p.1)))
      in reverse (p, null)).

(** 

You're invited to conduct the verification of [reverse], proving
that it satisfies the given specification.

Hint: It might be a good idea to make use of the previously proved
lemmas [lseq_null] and [lseq_pos].

Hint: Be careful with the logical values of variables passed to the
[gh_ex] lemma before verifying a recursive call of [reverse].

Hint: A verification goal to a function defined via [Fix] can be
reduced via the [val_doR] lemma or similar ones.

Hint: The [shape_rev] predicate is in fact an existential in disguise:
it can be proved by providing appropriate witnesses.

Hint: Lemmas [rev_cons], [cat_rcons] and [cats0] from the [seq]
library will be useful for establishing equalities between lists.

*)

Next Obligation.
(* fill in your proof here instead of [admit] *)
admit.
Qed.

Next Obligation.
(* fill in your proof here instead of [admit] *)
admit.
Qed.

(* END *)
