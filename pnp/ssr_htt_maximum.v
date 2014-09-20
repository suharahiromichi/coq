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

(* リストの最大値 *)
Fixpoint maximum_pure (l : seq nat) : nat :=
  match l with
    | a :: xs => max a (maximum_pure xs)
    | [::] => 0
  end.

Fixpoint lseg (p q : ptr) (xs : seq nat) : Pred heap := 
  if xs is x::xt then 
    [Pred h | exists r h',
              (h = p :-> x \+ ((p .+ 1 :-> r) \+ h')) /\ h' \In lseg r q xt]
  else
    [Pred h | p = q /\ h = Unit].

Definition lseq p := lseg p null.

(** リストに関する補題 *)
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

(** max に関する補題 *)
Lemma max0r : forall a,
  max a 0 = a.
Proof.
  apply: Max.max_0_r.
Qed.

Lemma max0l : forall a,
  max 0 a = a.
Proof.
  apply/Max.max_0_l.
Qed.

Lemma maxS : forall a b,
  max a.+1 b.+1 = (max a b).+1.
Proof.
  move=> a b.
  by rewrite Max.succ_max_distr.
Qed.  

Lemma max_assoc : forall a b c,
  max a (max b c) = max (max a b) c.
Proof.
  apply/Max.max_assoc.
Qed.

Lemma max_nil : 
  maximum_pure [::] = 0.
Proof.
  by [].
Qed.

Lemma max_hdtl_equation : forall (a : nat) (xs : seq nat),
  max a (maximum_pure xs) = maximum_pure (a :: xs).
Proof.
  by [].
Qed.

(** プログラムの証明 *)
Definition maximum_inv p acc (l : seq nat) h : Prop := 
  exists a1 : nat,
    exists xs : seq nat,
      exists h' : heap,
        [/\ h = acc :-> a1 \+ h',
         lseq p xs h' &
              max a1 (maximum_pure xs) = maximum_pure l].

Definition maximum_acc_tp p acc := 
  unit -> {l : seq nat}, 
     STsep (maximum_inv p acc l,
           [vfun (res : nat) h => maximum_inv p acc l h /\ res = maximum_pure l]).

Program Definition maximum_acc (p acc : ptr) : maximum_acc_tp p acc := 
  Fix (fun (loop : maximum_acc_tp p acc) (_ : unit) => 
         Do (if (p == null) then
               a0 <-- read nat acc;
               ret a0
             else
               a1 <-- read nat acc;
               a2 <-- read nat p;
               nextp <-- read ptr (p .+ 1); (* 「.+1」 ではなく、2項の「.+」。 *)
               p ::= nextp;;
               acc ::= max a1 a2;;
               loop tt)).
Next Obligation.
  apply: ghR => {H} h l H V.               (* conseq を消す。 *)
  case: H => a1 [] xs' [] h'.              (* ループ不変式での場合分け。 *)
  case H1: (p == null).
  - move=> [] -> q Hmax.
    apply: bnd_readR => //=.
    apply: val_ret => //=.
    move=> D.
    split.
    + rewrite /maximum_inv.
      exists a1, xs', h'.
      split; by [].
    + move/eqP : H1 => Z; subst.              (* 前提H1から p = null を反映する。 *)
      eapply (@lseq_null xs' _ _) in q.
      case: q Hmax => Hxs'.
      rewrite Hxs' => _ /=.
      rewrite max0r.
        by [].
  - move=> [] => H2 H3 H4.
    rewrite H2.                             (* ループ不変式由来のヒープ *)
    apply: bnd_readR => //=.
    move: H3.                          
    case/(lseq_pos (negbT H1)) => x [q2][h3][->] /= H5 H6.
    rewrite -H5.
    apply: bnd_readR => //=.
    apply: bnd_readR => //=.
    apply: bnd_writeR => //=.
    apply: bnd_writeR => //=.
    apply: (gh_ex [::]).
    apply: val_do => /=.        
    + move=> D.
      admit.
    + 
    + admit.
Qed.

(* テスト *)
Program Definition nop' p :
  {xs},
  STsep (lseq p xs,
         [vfun res => lseq res xs]) :=
  Do (ret p).
Next Obligation.
  apply: ghR => i xs H V.
  heval. 
Qed.

Program Definition nop p :
  {xs},
  STsep (lseq p xs,
         [vfun res => lseq res xs]) :=
  Do (if p == null then
        ret null
      else
        ret p).
Next Obligation.
  apply: ghR => i xs H V.
  case: ifP H => H1.
  - rewrite (eqP H1); case/(lseq_null V) => -> ->.
    heval. 
  - case/(lseq_pos (negbT H1)) => x [q][h][->] <- /= H2.
    heval.
Qed.

(* うまく証明できない。 *)
Definition deallocall_acc_tp p := 
  unit -> {xs},
  STsep (lseq p xs,
         [vfun res h => lseq p [::] h /\ res = null]).

Program Definition deallocall_acc (p : ptr) : deallocall_acc_tp p := 
  Fix (fun (loop : deallocall_acc_tp p) (_ : unit) => 
         Do (if p == null then
               ret null
             else
               nextp <-- read ptr (p .+ 1);
               p ::= nextp;;
               loop tt)).
Next Obligation. 
  apply: ghR => {H} h xs H V.                  (* conseq を消す。 *)
  case: ifP H => H1.
  - rewrite (eqP H1); case/(lseq_null V) => _ ->.
    heval.
  - case/(lseq_pos (negbT H1)) => x [] nextp [] h' [] -> <- /= H2.
    apply: bnd_readR => /=.
    apply: bnd_writeR => /=.
    apply: (gh_ex [::]).
    apply: val_doR => /=.
(*
  H2 : h' \In lseq nextp (behead xs)
  ============================
   valid (p :-> nextp \+ (p.+1 :-> nextp \+ h')) ->
   lseq p [::] (p :-> nextp \+ (p.+1 :-> nextp \+ h'))
*)
    + admit.
    + by [].
    + by [].
Qed.

(* END *)
