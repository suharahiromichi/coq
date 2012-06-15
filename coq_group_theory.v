(*
   雪江明彦「代数学1群論入門」日本評論社
   本文に沿って、coqにて展開する。
   
   2011_03_19 Sectionを使い、群に共通の定義をまとめて定義した。
   2011_03_20 Ltac でtacticsをまとめた。
   *)


Require Import Setoid.                      (* rewrite at *)


Section Group.
  Variable G : Set.
  (* 演算子 *)
  Variable App : G -> G -> G.
  Infix "**" := App (at level 61, left associativity).
  (* 定義 2.1.1 (1) *) (* 単位元 *)
  Variable E : G.
  (* 定義 2.1.1 (2) *) (* 逆元 *)
  Variable Inv : G -> G.
  
  (* 定義 2.1.1 (1) *) (* 単位元 *)
  Axiom identity_r :
    forall x, x ** E = x.
  Axiom identity_l :
    forall x, E ** x = x.
  
  (* 定義 2.1.1 (2) *) (* 逆元 *)
  Axiom inverse_r :
    forall x, x ** (Inv x) = E.
  Axiom inverse_l :
    forall x, (Inv x) ** x = E.
  
  (* 定義 2.1.1 (3) *) (* 結合則 *)
  Axiom associative_law :
    forall x y z, x ** (y ** z) = (x ** y) ** z.
  
  (* 暗黙の裏公理。両辺にxを掛ける *)
  Axiom right_law :
    forall a b x, a = b -> a ** x = b ** x.
  Axiom left_law :
    forall a b x, a = b -> x ** a = x ** b.
  
  (* 例題 2.1.7 *)
  Goal forall x y z w : G,
    x ** ((y ** z) ** w) = (x ** y) ** (z ** w).
  Proof.
    intros.
    rewrite <- associative_law.
    rewrite associative_law.
    reflexivity.
  Qed.


  Ltac insert_inv_l B A :=                  (* B の左に (Inv A) ** A を掛ける *)
    rewrite <- (identity_l B);
      rewrite <- (inverse_l A).
  
  Ltac insert_inv_r B A :=                  (* B の右に A ** (Inv A) を掛ける *)
    rewrite <- (identity_r B);
      rewrite <- (inverse_r A).
  
  (* 命題 2.1.8 (1) *) (* 簡約法則 *)
  Theorem reduce_law_l :
    forall a b c : G, a ** b = a ** c -> b = c.
  Proof.
    intros.
    insert_inv_l b a.
    insert_inv_l c a.
    rewrite <- associative_law.
    rewrite <- associative_law.
    eapply (left_law _ _ (Inv a)).
    apply H.
  Qed.
  
  Theorem reduce_law_r :
    forall b c a : G, b ** a = c ** a -> b = c.
  Proof.
    intros.
    insert_inv_r b a.
    insert_inv_r c a.
    rewrite associative_law.
    rewrite associative_law.
    eapply (right_law _ _ (Inv a)).
    apply H.
  Qed.
  
  (*
     b = Inv a ** c
     --------------
     a ** b = c
     *)
  Ltac r_to_l A :=
    eapply (reduce_law_l A _ _);
      repeat (rewrite associative_law);
        try (rewrite inverse_r);            (* rewrite (inverse_r a). *)
          try (rewrite inverse_l);          (* 実行されないかも *)
            try (rewrite identity_l).       (* rewrite (identity_l c). *)
  
  (*
     a = c ** Inv b
     --------------
     a ** b = c
     *)
  Ltac l_to_r B :=
    eapply (reduce_law_r _ _ B);
      repeat (rewrite <- associative_law);
        try (rewrite inverse_l);            (* rewrite (inverse_l b). *)
          try (rewrite inverse_r);          (* 実行されないかも *)
            try (rewrite identity_r).       (* rewrite (identity_r c). *)


  (* 命題 2.1.8 (2) *)
  Goal forall a b c,
    a ** b = c -> b = (Inv a) ** c.
  Proof.
    intros.
    r_to_l a.
    apply H.
  Qed.
  
  Goal forall a b c,
    a ** b = c -> a = c ** (Inv b).
  Proof.
    intros.
    l_to_r b.
    apply H.
  Qed.
  
  (* 例題 2.1.9 *)
  Goal forall x y z,
    x ** (Inv y) ** z ** x ** y ** x = E ->
    z = y ** (Inv x) ** (Inv x) ** (Inv y) ** (Inv x).
  Proof.
    intros.
    r_to_l (Inv y).
    (*
       eapply (reduce_law_l (Inv y) _ _).
       repeat rewrite associative_law.
       rewrite inverse_l.
       rewrite identity_l.
       *)
    r_to_l x.
    (*
       eapply (reduce_law_l x _ _).
       repeat rewrite associative_law.
       rewrite inverse_r.
       rewrite identity_l.
       *)
    l_to_r x.
    (*
       eapply (reduce_law_r _ _ x).
       repeat rewrite <- associative_law.
       rewrite inverse_l.
       rewrite identity_r.
       *)
    l_to_r y.
    (*
       eapply (reduce_law_r _ _ y).
       repeat rewrite <- associative_law.
       rewrite inverse_l.
       rewrite identity_r.
       *)
    l_to_r x.
    (*
       eapply (reduce_law_r _ _ x).
       repeat rewrite <- associative_law.
       rewrite inverse_l.
       *)    
    repeat rewrite associative_law.
    apply H.
  Qed.
  
  (* 命題 2.1.10 (1) *) (* 単位元の唯一性 *)
  Theorem identity_uniqueness :
    forall x E',
      E' ** x = x -> E' = E.
  Proof.
    intros.
    eapply (reduce_law_r _ _ x).
    rewrite (identity_l x).
    apply H.
  Qed.
  
  (* 命題 2.1.10 (2) *) (* 逆元の一意性 *)
  Goal forall b b',
    b ** b' = E -> b' = Inv b.
  Proof.
    intros.
    eapply (reduce_law_l b _ _).
    rewrite inverse_r.
    apply H.
  Qed.
  
  (* 命題 2.1.10 (3) *)
  Theorem inv_inv:
    forall a b,
      (Inv b) ** (Inv a) = Inv (a ** b).
  Proof.
    assert (forall a b, (Inv b) ** (Inv a) ** a ** b = E).
    intros.
    r_to_l b.
    (*
       apply (reduce_law_l b _ _).
       repeat rewrite associative_law.
       rewrite inverse_r.
       rewrite identity_l.
       *)
    rewrite identity_r.
    r_to_l a.
    (*
       apply (reduce_law_l a _ _).
       repeat rewrite associative_law.
       rewrite inverse_r.
       rewrite identity_l.
       *)
    reflexivity.
    (* END assert *)
    
    intros.
    apply (reduce_law_r _ _ (a ** b)).
    rewrite (inverse_l (a ** b)).
    repeat rewrite associative_law.
    eapply H.
  Qed.
  
  (* 命題 2.1.10 (4) *)
  Axiom inverse_inverse :
    forall x, Inv (Inv x) = x.
End Group.


(* 群 G *)
Variable G : Set.
(* 演算子 *)
Variable AppG : G -> G -> G.
Infix "**" := AppG (at level 61, left associativity).
(* 定義 2.1.1 (1) *) (* 単位元 *)
Variable EG : G.
(* 定義 2.1.1 (2) *) (* 逆元 *)
Variable InvG : G -> G.
(* 公理や定理 *)
Let identity_g_r := identity_r G AppG EG.
Let identity_g_l := identity_l G AppG EG.
Check identity_g_l.
Let inverse_g_r := inverse_r G AppG EG InvG.
Let inverse_g_l := inverse_l G AppG EG InvG.
Check inverse_g_l.
Let associative_g_law := associative_law G AppG.
Let right_law_g := right_law G AppG.
Let left_law_g := left_law G AppG.
Let reduce_law_g_r :=  reduce_law_r G AppG EG InvG.
Let reduce_law_g_l :=  reduce_law_l G AppG EG InvG.
Check reduce_law_g_l.
Let inv_inv_g := inv_inv G AppG EG InvG.


(* 群 H *)
Variable H : Set.
Variable AppH : H -> H -> H.
Infix "++" := AppH (at level 61, left associativity).
Variable EH : H.
Variable InvH : H -> H.
Let identity_h_r := identity_r H AppH EH.
Let identity_h_l := identity_l H AppH EH.
Check identity_h_l.
Let inverse_h_r := inverse_r H AppH EH InvH.
Let inverse_h_l := inverse_l H AppH EH InvH.
Check inverse_h_l.
Let associative_h_law := associative_law H AppH.
Let right_law_h := right_law H AppH.
Let left_law_h := left_law H AppH.
Let reduce_law_h_r :=  reduce_law_r H AppH EH InvH.
Let reduce_law_h_l :=  reduce_law_l H AppH EH InvH.


(* phi : G -> H が群の準同型写像 *)
Variable phi : G -> H.


Axiom homomorphism_phi :
  forall a b : G, phi (a ** b) = (phi a) ++ (phi b).


(* 命題 2.5.2 *)
(* 全単射写像 phi : G -> H が群の準同型写像なら、GとHは同型である *)


(* phi が全単射なら、phi は単射である。 *)
Axiom injective_phi :
  forall a b, (phi a) = (phi b) -> a = b.


(* phi が全単射なら、逆写像 psi が存在する *)
Variable psi : H -> G.
Axiom inverse_phi :
  forall x, phi (psi x) = x.


(* 逆写像 psi は準同型写像である。 *)
Lemma t_2_5_2 :
  forall x y,
    (psi x) ** (psi y) = psi (x ++ y).
Proof.
  intros.
  apply injective_phi.
  rewrite inverse_phi.
  rewrite homomorphism_phi.
  rewrite inverse_phi.
  rewrite inverse_phi.
  reflexivity.
Qed.
(*
   題意から、phi : G -> H は準同型写像である。
   Lemma t_2_5_2から、phiの逆写像 psi : H -> G は準同型写像である。
   写像とその逆写像の両方が準同型写像であるので、G と H は同型である。
   *)


Theorem homomorphism_phi_identity :
  phi EG = EH.
Proof.
  eapply (reduce_law_h_r _ _ (phi EG)).
  rewrite identity_h_l.
  rewrite <- homomorphism_phi.
  rewrite identity_g_l.
  reflexivity.
Qed.


(* 命題 2.5.3 (2) *)
Theorem homomorphism_phi_inverse :
  forall x, phi (InvG x) = InvH (phi x).
Proof.
  intros.
  eapply (reduce_law_h_r _ _ (phi x)).
  rewrite inverse_h_l.
  rewrite <- homomorphism_phi.
  rewrite inverse_g_l.
  apply homomorphism_phi_identity.
Qed.


(* Img(phi) = {(phi x) | x : G} は、Hの(部分)群である *)
Goal forall x y, exists z,
  (phi x) ++ (phi y) = phi z.
Proof.
  intros.
  exists (x ** y).
  rewrite <- homomorphism_phi.
  reflexivity.
Qed.


Goal forall x, exists y,
  InvH (phi x) = phi y.
Proof.
  intros.
  exists (InvG x).
  rewrite <- homomorphism_phi_inverse.
  reflexivity.
Qed.


(* 恒等写像は、準同型写像である *)
Variable IdG : G -> G.
Axiom Identity_function : forall a, a = IdG a.


Goal forall x y : G, (IdG x) ** (IdG y) = IdG (x ** y).
Proof.
  intros.
  repeat (rewrite <- Identity_function).
  reflexivity.
Qed.


(* 群GからGへの同型写像をGの自己同型写像とよぶ。その集合をAut(G)で表す。
   恒等写像は同型写像であるから、自己同型写像である。IdG∈Aut(G)。
   同型写像と同型写像の合成の演算を @@ とおく。
   自己同型写像は @@ に対して閉じている（同型でなくても閉じているから）。
   自己同型写像の集合 Aut(G) は、IdG を単位元とした群である。
*)


(* 命題 2.5.17 *)
(* Tht : G -> Aut(G) を下記のとおり定義する。
   （g∈Gに対して、(Tht g)∈Aut(G)である）
   任意のgが固定されたとき、(Tht g)は、群Gの自己同型写像であることを示す。
   *)


Variable Tht : G -> (G -> G).               (* G -> Aut(G) *)
Axiom define_tht :
  forall g h : G, Tht g h = g ** h ** (InvG g).


Lemma p2_5_17 : forall g h1 h2 : G,
  Tht g (h1 ** h2) = (Tht g h1) ** (Tht g h2).
Proof.
  intros.
  repeat (rewrite define_tht).
  repeat (rewrite associative_g_law).
  rewrite <- associative_g_law at 1.
  (* rewriteはできるところはすべてrewriteするので、最初のところだけに限定する。 *)
  rewrite <- (identity_g_l (h2 ** InvG g)).  
  rewrite <- (inverse_g_l g).
  repeat (rewrite associative_g_law).
  reflexivity.
Qed.


(* 命題 2.5.22 *)
(* Tht : G -> Aut(G) を上記のとおり定義する。
   （g∈Gに対して、(Tht g)∈Aut(G)である）
   Thtは、群Gから群Aut(G)への準同型写像であることを示す。
   ただし、群Aut(G)の積は、写像の合成（以下のDot）で定義する。
*)


Variable Dot : (G -> G) -> (G -> G) -> (G -> G).
Infix "@@" := Dot (at level 51, right associativity).
Axiom define_dot :
  forall f g : G -> G,
    forall x : G, (f @@ g) x = f (g x).


Lemma p2_5_22 : forall g1 g2 h : G,
  ((Tht g1) @@ (Tht g2)) h = Tht (g1 ** g2) h.
Proof.
  intros.
  rewrite define_dot.
  repeat (rewrite define_tht).
  rewrite <- inv_inv_g.
  repeat (rewrite associative_g_law).
  reflexivity.
Qed.


(* END *)