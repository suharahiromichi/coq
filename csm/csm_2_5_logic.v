From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensiv.
(* Set Printing All. *)

  (**

## 論理ゲーム(3)

### 前提が。。。なら、ゴールが。。。なら。

- 前提が \/ なら、それを case
- 前提が /\ なら、それを case
- 前提が -> なら、それに適当な前提を apply
- 前提が forall なら、それに適当な値を apply
- 前提が exists なら、それを case
- 前提が not なら(ゴールをexfalsoしてから)、それを apply

- ゴールが <-> なら、split
- ゴールが /\ なら、split
- ゴールが \/ なら、left か right
- ゴールが not なら、intro
- ゴールが forall なら、intro
- ゴールが exists なら、適当な値を exists

- ゴールと前提が同じなら、done
- 前提に P と not P があるなら、（矛盾で）done

- 前提が。。。は、ゴールが。。。に優先する。


### case はまとめられる。moveでも代用できる（同じではない）。

- case=> [H1 H2].     move=> [H1 H2].
- case=> [H1 | H2].   move=> [H1 | H2].
- case=> H1 H2.       case; move=> H1 H2 で case=> [H1 H2] と同じ意味。

[]や[|]は入れ子にでき、空も許される。

   *)

Section Logic.

  Variable A B C : Prop.
  
  (** ********** *)
  (** 対偶の証明 *)
  (** ********** *)
  
  (** テキストの答え *)
  
  Lemma contrap : (A -> B) -> (~B -> ~A).
  Proof.
    rewrite /not.
    move=> AtoB notB.
      by move/AtoB.
  Qed.
  
  (** 細かく説明 *)
  
  Lemma contrap' : (A -> B) -> (~B -> ~A).
  Proof.
    (* intros する。 *)
    move=> AtoB notB.
    (* ゴールが not なら intro する。 *)
    move=> HA.
    (* 前提が not で ゴールが False なら apply する。 *)
    apply: notB.
    (* 以降は、ModusPonens の証明と同じ。 *)
    apply: AtoB.
    (* 前提とゴールが同じ。 *)
    done.
  Qed.
  
  (** 逆 <- は証明できますか？ *)
  
  Lemma contrap_inv' : (~B -> ~A) -> (A -> B).
  Proof.
    move=> notBtonotA HA.
    Admitted.
  
  (** ******************** *)
  (** AND と OR の 左分配則 *)
  (** ******************** *)
  
  (** テキストの答え *)
  
  Lemma AndOrDistL : (A /\ C) \/ (B /\ C) <-> (A \/ B) /\ C.
  Proof.
    rewrite /iff.
    apply: conj.
    - case.
      + case=> AisTrue CisTrue.
          by apply: conj; [apply: or_introl | ].
      + case=> AisTrue BisTrue.
          by apply: conj; [apply: or_intror | ].
    - case=> AorBisTrue CisTrue.
      case: AorBisTrue => [AisTrue | BisTrue].
      + by apply: or_introl.
      + by apply: or_intror.
  Qed.
  
  (** 細かく説明 *)
  
  Lemma AndOrDistL'' : (A /\ C) \/ (B /\ C) <-> (A \/ B) /\ C.
  Proof.
    rewrite /iff.                           (* 省略してもよい。 *)
    (* P<->Q は、P->Q /\ Q->P であることが解る。 *)
    (* すなわち、ゴールが <-> のときは、/\と同じことをする。 *)
    
    (* ゴールが <-> なら split *)
    split.                                  (* apply: conj とおなじ。 *)

    (* 前提が \/ なら case *)
    - case.
      (* 前提が /\ なら case *)
      + case.
        (* やることがないので、intro する。 *)
        move=> AisTrue CisTrue.
        (* ゴールが /\ なら split *)
        split.                    (* apply: conj とおなじ。 *)
        (* ゴールが \/ なら left か right *)
        * left.                      (* apply: or_introl とおなじ。 *)
          (* ゴールと前提が同じなら done *)
          done.
        (* ゴールと前提が同じなら done *)
        * done.
          
      (* 前提が /\ なら case *)
      + case.
        (* やることがないので、intro する。 *)
        move=> BisTrue CisTrue.
        (* ゴールが /\ なら split *)
        split.
        (* ゴールが \/ なら left か right *)
        * right.                     (* apply: or_intror とおなじ。 *)
          (* ゴールと前提が同じなら done *)
          done.
        (* ゴールと前提が同じなら done *)
        * done.
          
    (* 前提が /\ なら case *)
    - case.
      (* 前提が \/ なら case *)
      case.
      (* やることがないので、intro する。  *)
      + move=> AisTrue CisTrue.
        (* ゴールが \/ なので left *)
        left.
        (* ゴールと前提が同じなら done *)
        done.
        
      (* やることがないので、intro する。  *)
      + move=> BisTrue CisTrue.
        (* ゴールが \/ なので left *)
        right.
        (* ゴールと前提が同じなら done *)
        done.
  Qed.
  
  (** 直前の例をまとめる。 *)
  
  Lemma AndOrDistL''' : (A /\ C) \/ (B /\ C) <-> (A \/ B) /\ C.
  Proof.
    split.
    - case.
      + case=> AisTrue CisTrue.
        by split; [left | ].
      + case=> BisTrue CisTrue.
        by split; [right | ].
    - case.
      case=> AorBisTrue CisTrue.
      + by left.
      + by right.
  Qed.
  
  (** case をさらにまとめる。これが「正解」だろう。 *)
  (** この場合、case は move でもよい。 *)
  
  Lemma AndOrDistL'''' : (A /\ C) \/ (B /\ C) <-> (A \/ B) /\ C.
  Proof.
    split.
    - case=> [[AisTrue CisTrue] | [BisTrue CisTrue]].
      + by split; [left | ].
      + by split; [right | ].
    - case=> [[AisTrue | BisTrue] CisTrue].
      + by left.
      + by right.
  Qed.

  (** split, left, right を使わない例 *)
  
  Lemma AndOrDistL''''' : (A /\ C) \/ (B /\ C) <-> (A \/ B) /\ C.
  Proof.
    split.
    - case=> [[AisTrue CisTrue] | [BisTrue CisTrue]].
      + by apply: conj; [apply/or_introl | ].
      + by apply: conj; [apply/or_intror | ].
    - case=> [[AisTrue | BisTrue] CisTrue].
      + by apply/or_introl.
      + by apply/or_intror.
  Qed.
  
  (** ***************** *)
  (** ド・モルガンの定理 *)
  (** ***************** *)
  
  (** テキストの答え *)
  
  Lemma JDM (T : Type) (P : T -> Prop) :
    ~ (exists (x : T), P x) <-> forall x, ~P x.
  Proof.
    apply: conj => Hyp.
    - move=> x0 HPx0.
      apply: Hyp.
      by apply: (ex_intro P x0).
    - by case.
  Qed.
  
  (** split と exists を使う *)
  
  Lemma JDM' (T : Type) (P : T -> Prop) :
    ~ (exists (x : T), P x) <-> forall x, ~P x.
  Proof.
    split=> Hyp.                            (* apply: conj とおなじ。 *)
    - move=> x0 HPx0.
      apply: Hyp.
      by exists x0.             (* apply: (ex_intor _ x0) とおなじ。 *)
    - by case.
  Qed.
  
  (** 細かく説明 *)
  
  Lemma JDM'' (T : Type) (P : T -> Prop) :
    ~ (exists (x : T), P x) <-> forall x, ~P x.
  Proof.
    split.        (* ゴールが <-> なら split する。 *)
    - move=> Hyp. (* やることがないので、intro する。 *)
      move=> x0.  (* ゴールが forall なら intro する。 *)
      move=> HPx. (* ゴールが not なら intro する。 *)
      apply: Hyp. (* 前提が not で ゴールが False なら apply する。 *)
      exists x0.  (* ゴールが exists なら、適当な値を exists する。 *)
      done.       (* 前提とゴールが同じ。 *)
    - move=> Hyp. (* やることがないので、intro する。 *)
      move=> HeP. (* ゴールが not なら intro する。 *)
      case: HeP.  (* 前提が exists なら、case する。 *)
      (* ここで、done できる。 *)
      move=> x0.      (* ゴールが forall なら intro する。 *)
      move=> HPx.     (* やることがないので、intro する。 *)
      move: (Hyp x0). (* 前提が forall なら、適当な値を apply する。 *)
      move=> nHPx.   (* やることがないので、intro する。 *)
      done.          (* 前提に P と not P があるなら、done *)
  Qed.
  
  (** ************ *)
  (** 二重否定除去 *)
  (** ************ *)
  
  Hypothesis ExMidLow : forall P : Prop, P \/ ~P. (* 排中律 *)
  (** バニラCoqでは、Logic/Classical.v で公理として定義されている。
      バニラCoqでは、パッケージのインポートで公理が増えてしまうことがあるので、注意。
   *)
  (** 蛇足。
      Mathcomp では、このようなことは、意図して排除されている。axiom free。
      Mathcomp の場合は、boolean にリフレクトして、
      boolean の二重否定除去を使うべきとされる。
   *)
  
  (** テキストの答え *)
  
  Lemma notnotEq (P : Prop) : ~ ~ P -> P.
  Proof.
    move=> HnotnotP.
    case: (ExMidLow (~ P)).
    - by move /HnotnotP.
    - by case: (ExMidLow P).
  Qed.
  
  (** 細かく説明 *)
  
  Lemma notnotEq' (P : Prop) : ~ ~ P -> P.
  Proof.
    move=> HnotnotP.        (* やることがないので、intro する。 *)
    Check (ExMidLow (~ P)).
    move: (ExMidLow (~ P)). (* 前提が forall なら、適当な値を apply する。 *)
    case.                   (* 前提が \/ なら case する。 *)
    - move=> HnotP.         (* やることがないので、intro する。 *)
      done.                 (* 前提に P と not P があるなら、done *)
    - move: (ExMidLow P).   (* 前提が forall なら、適当な値を apply する。 *)
      case.                 (* 前提が \/ なら case *)
      + move=> HP _.        (* やることがないので、intro する。 *)
        done.               (* 前提とゴールが同じ。 *)
      + move=> HnotP _.     (* やることがないので、intro する。 *)
        done.               (* 前提に P と not P があるなら、done *)
  Qed.
  
  (** intro するのを減らす。  *)
  
  Lemma notnotEq'' (P : Prop) : ~ ~ P -> P.
  Proof.
    move=> HnotnotP.
    case: (ExMidLow (~ P)).
    - done.
    - by case: (ExMidLow P).
  Qed.
  
  (** 対偶の逆が証明できるようになる。 *)
  
  Lemma contrap_inv : (~B -> ~A) -> (A -> B).
  Proof.
    move=> notBtonotA HA.
    apply: notnotEq.
    move=> HnB.
    move: (notBtonotA HnB) => HnA.
    apply: HnA.
    done.
  Qed.
  
End Logic.

(********* *)
(** おまけ *)
(********* *)

(** Prop と bool の違い  *)

Section Test.

  Variable A B C : Prop.
  Variable a b c : bool.
  
  Goal True \/ A.
  Proof.
    simpl.
    (* Goal : True \/ A で変化しない。 *)
    left.
    done.
  Qed.
  
  Goal true || a.
  Proof.
    simpl.
    (* Goal : true となり、証明が終わる。 *)
    done.
  Qed.
  
  (** Prop 型の変数そのものに対しては、case による場合分けができない。  *)
  Goal (A -> B) -> (~B -> ~A).
  Proof.
    Fail case: A.
  Admitted.
  
  (** bool 型の変数は、case による場合分けができる。 *)
  (** ただし ~ fales -> ~ true は成り立たない。 *)
  Goal (a -> b) -> (~b -> ~a).
  Proof.
    case: a; case: b.
    - done.               (* (true -> true) -> ~ true -> ~ true *)
    - admit.              (* (true -> false) -> ~ false -> ~ true *)
    - done.               (* (false -> true) -> ~ true -> ~ false *)
    - done.               (* (false -> false) -> ~ false -> ~ false *)
  Admitted.
  

  (** ************* *)
  (** bool 版の対偶 *)
  (** ************* *)
  Goal (a ==> b) ==> (~~b ==> ~~a).
  Proof.
    case: a; case: b.
    - done.               (* (true ==> true) ==> ~~ true ==> ~~ true *)
    - done.               (* (true ==> false) ==> ~~ false ==> ~~ true *)
    - done.               (* (false ==> true) ==> ~~ true ==> ~~ false *)
    - done.               (* (false ==> false) ==> ~~ false ==> ~~ false *)
  Qed.
  
  (** == も成り立つ。  *)
  Lemma contrab : (a ==> b) == (~~b ==> ~~a).
  Proof.
      by case: a; case: b.
  Qed.
  
  (** ****************************** *)
  (** bool 版の AND と OR の 左分配則 *)
  (** ****************************** *)
  Lemma AndOrDistLb : (a && c) || (b && c) == (a || b) && c.
  Proof.
      by case: a; case: b; case: c.
  Qed.
  
  (** ************* *)
  (** bool 版の JDM *)
  (** ************* *)
  
  Lemma JDMb (T : finType) (p : pred T) :   (* p : T -> bool *)
    ~~ [exists x, p x] == [forall x, ~~ p x].
  Proof.
      by rewrite negb_exists /=.            (* fintype.v *)
  Qed.
  
  (** ********************* *)
  (** bool 版の二重否定除去 *)
  (** ********************** *)
  Lemma notnotEqb : b == ~~ ~~ b.
  Proof.
      by case: b.
  Qed.

  (** Prop と bool の違い：
      Prop の eq、「=」は、定義が同じであること（ライプニッツの等式）。
      bool の eqn、「==」は、値として同じであること。
      自然数は、両者が同値であことが証明されている。
   *)
  Check @eqnP : forall m n, reflect (m = n) (m == n).

End Test.

(* END *)
