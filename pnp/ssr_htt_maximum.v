(* http://ilyasergey.net/pnp/ *)

(** * 「Hoare Type Theory の基礎」から *)
(** * Elements of Hoare Type Theory *)
(** リストの最大値を求めるプログラムの証明 *)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import prelude pred pcm unionmap heap heaptac
        stmod stsep stlog stlogR.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** リストの最大値 *)
Fixpoint maximum_pure (l : seq nat) : nat :=
  match l with
    | a :: xs => maxn a (maximum_pure xs)
    | [::] => 0
  end.

Fixpoint lseg (p q : ptr) (xs : seq nat) : Pred heap := 
  if xs is x::xt then 
    [Pred h | exists r h',
              (h = p :-> x \+ ((p .+ 1 :-> r) \+ h')) /\ h' \In lseg r q xt]
  else
    [Pred h | p = q /\ h = Unit].

Definition lseq p := lseg p null.

(** リストに関する補題 (Elements of Hoare Type Theoryより) *)
Lemma lseg_null xs q h : 
  valid h -> h \In lseg null q xs -> 
  [/\ q = null,
   xs = [::] & h = Unit].
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

Lemma lseq_null xs h :
  valid h ->
  h \In lseq null xs -> xs = [::] /\ h = Unit.
Proof.
    by move=> D; case/(lseg_null D) => _ ->.
Qed.

Lemma lseq_pos xs p h : 
        p != null -> h \In lseq p xs -> 
        exists x, exists r, exists h', 
          [/\ xs = x :: behead xs, 
              p :-> x \+ (p .+ 1 :-> r \+ h') = h &
              h' \In lseq r (behead xs)].
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

(** プログラムの証明 *)
(* acc は、 maximumを保持する。 *)
(* s は、領域の先頭を保持する。 *)
Definition maximum_inv s acc (l : seq nat) h : Prop := 
  exists a : nat,             (* acc の中身 *)
    exists p : ptr,           (* 実際のリストの先頭 *)
      exists xs : seq nat,    (* リストの内容の論理表現。 *)
        exists h' : heap,
          exists h'' : heap,
            [/\ h = acc :-> a \+ (s :-> p \+ (h' \+ h'')),
             lseq p xs h'' &
                  maxn a (maximum_pure xs) = maximum_pure l].

Definition maximum_acc_tp p acc := 
  unit -> {l : seq nat}, 
  STsep (maximum_inv p acc l,
         [vfun (res : nat) h =>
          maximum_inv p acc l h /\ res = maximum_pure l]).

Program Definition maximum_acc (s acc : ptr) : maximum_acc_tp s acc := 
  Fix (fun (loop : maximum_acc_tp s acc) (_ : unit) => 
         Do (p <-- read ptr s;
             a <-- read nat acc;
             if (p == null) then
               ret a
             else
               x <-- read nat p;
               nextp <-- read ptr (p .+ 1); (* 「.+1」 ではなく、2項の「.+」。 *)
               acc ::= maxn a x;;           (* maxn をここで使っていい。 *)
               s ::= nextp;;
               loop tt)).
Next Obligation.
  apply: ghR => {H} h l H V.                (* conseq を消す。 *)
  case: H => a [p] [xs] [h'] [h''].         (* ループ不変式での場合分け。 *)
  case=> -> Hh Hi.                          (* ループ不変式由来のヒープ *)
  apply: bnd_readR => //=.                  (* x <-- !p0 *)
  apply: bnd_readR => //=.                  (* nextp <-- !p0.+1 *)
  case H1: (p == null).
  - apply: val_ret => //=.                  (* ret a *)
    move=> D.
    split.
    + rewrite /maximum_inv.
      exists a, p, xs, h', h''.
      split; by [].
    + move/eqP : H1 => Z. rewrite Z in Hh.  (* 前提H1から p = null を反映する。 *)
      Check (@lseq_null xs _ _).
      eapply (@lseq_null xs _ _) in Hh.
      case: Hh Hi => Hxs'.
      rewrite Hxs' => _ /=.
      rewrite maxn0.
        by [].
  - move: Hh.
    case/(lseq_pos (negbT H1))
    => x [r] [h'''] [Hxs] Hh Hr.            (* xs = x :: behead xs は残しておく。 *)
    rewrite -Hh.                            (* lseg 由来のヒープ *)
    apply: bnd_readR => //=.                (* x0 <-- !p *)
    apply: bnd_readR => //=.                (* nextp <-- !p0.+1 *)
    apply: bnd_writeR => //=.               (* acc ::= maxn a x *)
    apply: bnd_writeR => //=.               (* s ::= r *)
    apply: (gh_ex l).                       (* loop を Do loop にする。 *)
    apply: val_doR => /=.                   (* Do loop tt からループ不変式を取り出す。 *)
    + move=> D.
      rewrite /maximum_inv.
      (* ループ実行後の値を設定する。 *)
      exists (maxn a x), r, (behead xs).
      exists (h' \+ p :-> x \+ (p .+ 1 :-> r)), h'''.
      split.
      * rewrite -2!joinA. by [].            (* ヒープの一致 *)
      * apply: Hr.                          (* rの指すリスト *)
      * rewrite -maxnA -Hi.                 (* maximum_pure *)
        congr (maxn a _).
        have -> : (exists xs', xs = x :: xs') ->
                  maxn x (maximum_pure (behead xs)) = maximum_pure xs.
          by case => xs' ->.
        + by [].
        + exists (behead xs).
          by [].                            (* xs = x :: behead xs は残しておく。 *)
      * by [].                              (* ループ不変式 *)
    + by [].                                (* admitが残る限り、エラーになる。 *)
Qed.

(* END *)
