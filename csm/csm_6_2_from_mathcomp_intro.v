(**
https://www.jstage.jst.go.jp/article/jssst/34/2/34_2_64/_pdf

https://github.com/affeldt/mathcomp-intro
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Sect. 5: Overview of Finite Groups *)

Local Open Scope group_scope.

Section sect5.

  Variable gT : finGroupType.
  Variables G : {group gT}.

  (* p.69 右 l.2 *)
  Variables g h : gT.
  Hypotheses (gG : g \in G) (hG : h \in G).
  Check g * h : gT.
  Check groupM gG hG : g * h \in G.
End sect5.

Section coset_bijection.

  Variable gT : finGroupType.
  Variables G H : {group gT}.               (* これが reprs の引数 *)
  Hypothesis HG : H \subset G.
  
  (** Sect. 6: Left-cosets are disjoint *)
  
(**
剰余群の任意のふたつの元は、まったく同じか、重ならない別のものである。
*)
  Lemma coset_disjoint L0 L1 :
    L0 \in lcosets H G ->
           L1 \in lcosets H G ->
                  L0 :&: L1 != set0 -> L0 = L1.
  Proof.
(*
    case/lcosetsP => g0 g0G -> {L0}.         (* p.69 右 l.14 *)
 *)
    Check @lcosetsP gT H G L0.
    move/(@lcosetsP gT H G L0).             (* move/lcosetsP *)
    case.                                   (* 前提が exists のときは case *)
    move=> g0.
    move=> g0G.
    move=> TMP.
    rewrite TMP.
    clear TMP.                              (* rewrite {TMP} *)
    clear L0.                               (* rewrite {L0} *)
    
    case/lcosetsP => g1 g1G -> {L1}.
    move=> g0_g1_disj.
    apply/lcoset_eqP.
    case/set0Pn : g0_g1_disj => /= g.
    rewrite in_setI => /andP[].
    rewrite 3!mem_lcoset => g_g0 g_g1.
    rewrite -(mul1g g0).
    rewrite -(mulgV g).
    rewrite 2!mulgA.
    rewrite -mulgA.
    rewrite groupM //.
    rewrite groupVl //.
    rewrite invMg.
      by rewrite invgK.
  Qed.
  
  (** Sect. 7: Injection into the set of left-cosets *)
  
  Lemma mem_repr_coset x : x \in G -> repr (x *: H) \in G.
  Proof.
    move=> xG.
    rewrite /repr.
    case: ifPn => // x1.
    case: pickP => /=.
    move=> g0.
    case/lcosetP => g1 g1H ->.
    rewrite groupM //.
      by move/subsetP : (HG); apply.
      move/(_ x).
        by rewrite lcoset_refl.
  Qed.

End coset_bijection.

Section coset_bijection2.
  
  Variable gT : finGroupType.

(**
repr は、 代表元 representative を求める関数である。
剰余群の元（剰余類）には重なりがないので、代表元から剰余類の関数は、単射である。

``reprs G H`` は、代表元を求める関数の剰余群 ``H \ G`` の像である。
つまり、剰余類からぞれぞれ代表元を取り出して集めたものになる。

「（剰余群の）元の代表元の集合」と呼ぶ。
*)
  Definition reprs (G H : {group gT}) := repr @: lcosets H G.  (* p.70 右 l.24 *)

  (* p.71 左 l.5 *)
  Lemma injective_coset (G H : {group gT}) :
    {in reprs G H &, injective (fun g => g *: H)}.
  Proof.
    move=> /= g g'.
    (* goal : *)
(**
g と g' が ``H \ G`` の元（剰余類）の代表元であるなら、剰余類を求める関数

``g |-> g *: H``

は単射である。
*)
    Check g \in reprs G H ->
                g' \in reprs G H ->
                       g *: H = g' *: H -> g = g'.
    
    move=> /(@imsetP (set_of_finType gT) gT repr (mem (lcosets H G)) g).
    Check (@imsetP (set_of_finType gT) gT repr (mem (lcosets H G)) g).
    move=> [] /=.
    
    (* goal : *)
    Check forall x : {set gT},
        x \in lcosets H G -> g = repr x ->
              g' \in reprs G H ->
                     g *: H = g' *: H -> g = g'.
    move=> L LHG gL.
    move=> /imsetP [] /= K KHG g'K.
    move=> abs.
  Admitted.
  
End coset_bijection2.

(** Sect. 8: Transitivity of the group index *)

Notation "#| G : H |" := #| lcosets H G |.

Section index.
  
  Variable gT : finGroupType.
  Variables G H K : {group gT}.
  Hypotheses (HG : H \subset G) (KG : K \subset G) (HK : K \proper H).
  
  Check reprs G H.                      (* G / H の元の代表元の集合 *)
  Check reprs H K.                      (* H / K の元の代表元の集合 *)

  (* p.71 右 l.24 *)
  Lemma index_trans : #| G : K | = (#| G : H | * #| H : K |)%N.
  Proof.
    rewrite /=.
    
    set calG := reprs G H.         (* G / H の元の代表元の集合 *)
    pose alpha := fun x => x *: H. (* から Hについての剰余類への関数α *)
    have calG_H_inj : {in calG &, injective alpha}. (* 関数αが単射である。 *)
      by apply: injective_coset.
      
    set calH := reprs H K.        (* H / K の元の代表元の集合 *)
    pose beta := fun x => x *: K. (* から Kについての剰余類への関数β *)
    have calH_K_inj : {in calH &, injective (fun x=> x *: K)} (* 関数βが単射である。 *)
      by apply: injective_coset.

    Check @proper_sub _ H K : H \proper K -> H \subset K.
    move/proper_sub : HK.                   (* K ⊆ H *)

    (* p.72 左 l.19 *)
    pose phi :=                   (* calG × calH から K についての剰余類への関数φ *)
      fun gh : gT * gT => let: (g, h) := gh in (g * h) *: K.
    have phi_injective :                    (* 関数φが単射である。 *)
      {in setX calG calH & , injective phi}.
    - case=> g h.
      rewrite inE /=.
      case=> g' h' /andP [gG hH].
      rewrite /phi inE /= => /andP [g'G h'H] ghK.

      (* p.72 左 l.30 *)
      have step1 : (g'^-1 * g * h) *: K = h' *: K.
      + move: ghK.
        (* よく使われるシノニム、congr に関数 f を渡す。 *)
        Check congr1                        (* f は、1変数関数 *)
          : forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
        Check congr2                        (* f は、2変数関数 *)
          : forall (A1 A2 B : Type) (f : A1 -> A2 -> B) (x1 y1 : A1) (x2 y2 : A2),
            x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
        move/(congr1 (fun X => g'^-1 *: X)).
          by rewrite -2!lcosetM !mulgA mulVg mul1g.
  Admitted.

End index.

(* Sect. 9: Lagrange Theorem *)

Section lagrange.
  
  Variable gT : finGroupType.
  Variables G H : {group gT}.
  Hypotheses (HG : H \subset G).
  
  Lemma coset1 g : g *: (1%G : {group gT}) = [set g].
  Proof.
    apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP => j.
    case/lcosetP => x.
    rewrite !inE => /eqP ->.
      by rewrite mulg1 => /eqP.
      rewrite in_set1 => /eqP ->.
      apply/lcosetP.
      exists 1 => //.
        by rewrite mulg1.
  Qed.
  
  Lemma lcosets1 (K : {group gT}) : lcosets 1%G K = (set1) @: K.
  Proof.
    apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP => i.
    case/lcosetsP => g gK ->{i}.
    apply/imsetP.
    exists g => //.
      by apply coset1.
      case/imsetP => g gK ->{i}.
      apply/lcosetsP.
      exists g => //.
        by rewrite coset1.
  Qed.
  
  (* p.73 左 l.11 *)
  (* 部分群の指数の推移関係の系である。 *)
  Theorem Lagrange : #| G | = (#| H | * #| G : H |)%N.
  Proof.
    case/boolP : (1%G \proper H) => H1.
    
    (* ``{1} ⊂ H`` の場合 *)
    - have G1 : 1%G \subset G.              (* {1} ⊆ H である。 *)
      + apply/subsetP => h.
          by rewrite inE => /eqP ->.

      (* K = {1} とすると推移律が成り立ち、そこからラグランジュの定理が成り立つ。 *)
      Check index_trans HG G1 H1 : #| G : 1%G | = (#| G : H | * #| H : 1%G |)%N.
      Check (card_imset G set1_inj).
      + move: (index_trans HG G1 H1).
        rewrite lcosets1 (card_imset G set1_inj).
        rewrite mulnC lcosets1 card_imset //.
        exact: set1_inj.
        
    (* ``〜 {1} ⊂ H`` の場合 *)
    - have -> : H = 1%G.                    (* {1} = H である。 *)
      + apply/trivGP.
        move: H1.
          by rewrite proper1G negbK => /eqP ->.

      (* 左剰余類は {1} となり、そこからラグランジュの定理が成り立つ。 *)
      Check #| G | = (#| 1%G | * #| G : 1%G |)%N.
      + rewrite cards1 mul1n lcosets1 // card_imset //.
        exact: set1_inj.
  Qed.
  
End lagrange.

(* END *)
