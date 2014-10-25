(**
SSReflectのViewとView Hintについてのメモ
=========

2014_10_25 @suharahiromichi
*)

(**
ProofCafe Nr.42 で、
「An introduction to small scale reflection in Coq」

https://hal.inria.fr/inria-00515548/PDF/main-rr.pdf

の4章「4 Small scale reflection, first examples」の説明をしましたが、
その補足（訂正を含む）を以下にまとめます。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(**
# View

CoqのSSReflct拡張では、move/V や apply/V のかたちで前提（スタックトップ）や、ゴールの書き換
えができますが、このときのVをViewと呼びます。

実際は 前提またはゴールに対する apply の略記であり、おなじことがStandard Coqでもできることがわかります。
*)

Section Sample1.
  Variable P Q : bool -> Prop.
  Hypothesis P2Q : forall a, P a -> Q a.
  
(**
仮定の書き換え：Interpreting assumptions

ゴール「△->○」のとき、△の部分を書き換えます。
*)
  Goal forall a, P a -> Q a.
  Proof.
    move=> a.
    move/P2Q.                               (* Q a -> Q a *)
    Undo 1.
    move=> HPa; move: {HPa} (P2Q a HPa).
    Undo 1.
    move=> HPa; apply P2Q in HPa; move: HPa.
    apply.
    Undo 2.
    intro HPa; apply P2Q in HPa; apply HPa. (* Standard Coq風 *)
  Qed.
  
(**
ゴールの書き換え：Interpreting goals

ゴール全体を書き換えます。
ゴールが△->○の場合でもその全体が対象になるが、通常はintroして○だけを対象にします。
*)
  Goal forall a, P a -> Q a.
  Proof.
    move=> a HPa.
    (* Goal : Q a *)
    apply/P2Q; apply HPa.                   (* 最初のapplyの後、HPa : P a |- P a *)
    Undo 1.
    apply: (P2Q a HPa).
    Undo 1.
    apply P2Q; apply HPa.                   (* Standard Coq風 *)
  Qed.
End Sample1.

(**
# View Hint

View には、前節に加えてView Hintとして宣言された定理（補題）を自動的に補う機能があります。
View Hint のひとつに、iffLR があります。
*)

Check iffLR.                          (* iffLR : forall P Q : Prop, (P <-> Q) -> P -> Q *)

(**
「P<->Q」のかたちをした述語をViewとして使った場合、iffLRが自動的に補われて、「P->Q」として適用されるわけです。
*)

Section Sample2.
  Variable P Q : bool -> Prop.
  Hypothesis PQequiv : forall a, P a <-> Q a.

(**
仮定の書き換え：Interpreting assumptions
*)
  Goal forall a, P a -> Q a.
  Proof.
    move=> a.
    move/PQequiv.                           (* Q a -> Q a *)
    Undo 1.
    Check (iffLR (PQequiv a)).
    move/(iffLR (PQequiv a)).               (* a は _ でもよい。 *)
    Undo 1.
    move=> HPa; move: {HPa} (iffLR (PQequiv a) HPa).
    Undo 1.
    move=> HPa; apply (iffLR (PQequiv a)) in HPa; move: HPa.
    apply.
  Qed.

(**
ゴールの書き換え：Interpreting goals
*)
  Goal forall a, P a -> Q a.
  Proof.
    move=> a HPa.
    (* Goal : Q a *)
    apply/PQequiv; apply HPa.
    Undo 1.
    Check (iffLR (PQequiv a)).
    apply/(iffLR (PQequiv a)); apply HPa.
    Undo 1.
    apply: (iffLR (PQequiv a) HPa).
    Undo 1.
    apply (iffLR (PQequiv a)); apply HPa.
  Qed.
End Sample2.

(**
# 標準のView Hint の例 (iffLRn, iffRLn, iffLR, iffRL)

これらは、SSReflectのソースコードを見ると、theories/ssreflect.v の最後で宣言されています。
*)

Check iffLR.                              (* forall P Q : Prop, (P <-> Q) -> P -> Q *)
Check iffRL.                              (* forall P Q : Prop, (P <-> Q) -> Q -> P *)
Check iffLRn.                             (* forall P Q : Prop, (P <-> Q) -> ~ P -> ~ Q *)
Check iffRLn.                             (* forall P Q : Prop, (P <-> Q) -> ~ Q -> ~ P *)

Section Sample3.
  Variable P Q : bool -> Prop.
  Variable a : bool.
  Hypothesis PQequiv : P a <-> Q a.
  
  Check iffLR PQequiv.                      (* P a -> Q a *)
  Check iffRL PQequiv.                      (* Q a -> P a *)
  Check iffLRn PQequiv.                     (* ~ P a -> ~ Q a *)
  Check iffRLn PQequiv.                     (* ~ Q a -> ~ P a *)

(**
仮定の書き換え：Interpreting assumptions

端折った言い方をすると、move/PQequiv は、
move/(iffLR PQequiv) または move/(iffRL PQequiv) または move/(iffLRn PQequiv) または move/(iffRLn PQequiv)
のどれかが選ばれて使われるので、以下の4種類のゴールがすべて、move/PQequiv をつかって証明できます。
*)
  Goal P a -> Q a. move/PQequiv. by apply. Qed.     (* Q a -> Q a *)
  Goal Q a -> P a. move/PQequiv. by apply. Qed.     (* P a -> P a *)
  Goal ~ P a -> ~ Q a. move/PQequiv. by apply. Qed. (* ~ Q a -> ~ Q a *)
  Goal ~ Q a -> ~ P a. move/PQequiv. by apply. Qed. (* ~ P a -> ~ P a *)

(**
ゴールの書き換え：Interpreting goals

同様に、apply/PQequiv は、
apply/(iffLR PQequiv) または apply/(iffRL PQequiv) または apply/(iffLRn PQequiv) または apply/(iffRLn PQequiv)
のどれかが選ばれて使われるので、以下の4種類のゴールがすべて、apply/PQequiv をつかって証明できます。
*)
  Goal P a -> Q a. move=> H; apply/PQequiv. by apply H. Qed. (* H : P a |- P a *)
  Goal Q a -> P a. move=> H; apply/PQequiv. by apply H. Qed. (* H : Q a |- Q a *)
  Goal ~ P a -> ~ Q a. move=> H; apply/PQequiv. by apply H. Qed. (* H : ~ P a -> ~ P a *)
  Goal ~ Q a -> ~ P a. move=> H; apply/PQequiv. by apply H. Qed. (* H : ~ Q a -> ~ Q a *)
End Sample3.

(**
# reflect述語を使用可能にするView Hint

より重要なView Hintに elimT と intorT があります。
このView Hintのおがけで、andPやorPのような「reclect P b」のかたちのreflect述語をViewに書くことができます。
*)
Check elimT.                              (* forall (P : Prop) (b : bool), reflect P b -> b -> P *)
Check introT.                             (* forall (P : Prop) (b : bool), reflect P b -> P -> b *)

Section Sample4.
  Variable a b : bool.

(**
仮定の書き換え：Interpreting assumptions
*)
  Hypothesis andP : reflect (a /\ b) (a && b).
  Check elimT andP.                         (* a && b -> a /\ b *)

  Goal a && b -> a.
  Proof.
    move/andP.                              (* a /\ b -> a /\ b *)
    Undo 1.
    move/(elimT andP).
    Undo 1.
    move=> Hab; move: {Hab} (elimT andP Hab).
    Undo 1.
    move=> Hab; apply (elimT andP) in Hab; move: Hab.
    case; by [].
  Qed.

(**
ゴールの書き換え：Interpreting goals
*)
  Hypothesis orP  : reflect (a \/ b) (a || b).
  Check introT orP.                         (* a \/ b -> a || b *)  
  
  Goal a -> a || b.
  Proof.
    move=> Ha.
    apply/orP.                              (* Hab : a |- a || b *)
    Undo 1.
    apply/(introT orP).
    Undo 1.
    apply: (introT orP).
    left; by [].
  Qed.
  
(* 次はゴール「a&&b->a/\b」に対して、「a&&b->a/\b」を適用している。
「△->○」全体を対象にしているので一般的な例になっていない。要補足 *)
  Goal a && b -> a /\ b.
  Proof.
    apply/andP.
    Undo 1.
    apply/(elimT andP).
  Qed.
End Sample4.

(**
# まだ説明できていない事項

- ゴールが「=」である場合（Interpreting equivalences）
- move/とapply/のView Hintの区別がある理由。
- 独自にView Hintを定義する方法。
- 上記以外のssrboolにふくまれるView Hint。
*)

(**
# のこりのView Hint

View Hintは、次のように宣言されている。

theories/ssreflect.v では、
``
Hint View for move/ iffLRn|2 iffRLn|2 iffLR|2 iffRL|2.
Hint View for apply/ iffRLn|2 iffLRn|2 iffRL|2 iffLR|2.
``

theories/ssrbool.v では、
``
Hint View for move/ elimTF|3 elimNTF|3 elimTFn|3 introT|2 introTn|2 introN|2.
Hint View for apply/ introTF|3 introNTF|3 introTFn|3 elimT|2 elimTn|2 elimN|2.
Hint View for apply// equivPif|3 xorPif|3 equivPifn|3 xorPifn|3.
``

これをまとめると次のようになります。
``
assumption interpretation (move/)で使用：
elimTF elimNTF elimTFn
introT introTn introN

goal interpretations (apply/)で使用：
elimT elimTn elimN
introTF introNTF introTFn

right hand sides of double views (apply//)で使用：
equivPif equivPifn
xorPif xorPifn
``
*)

(* move/で使用： *)
Check elimTF.                             (* forall (P : Prop) (b c : bool), reflect P b -> b = c -> if c then P else ~ P *)
Check elimNTF.                            (* forall (P : Prop) (b c : bool), reflect P b -> ~~ b = c -> if c then ~ P else P *)
Check elimTFn.                            (* forall (P : Prop) (b c : bool), reflect P (~~ b) -> b = c -> if c then ~ P else P *)
(* apply/で使用： *)
Check elimT.                              (* forall (P : Prop) (b : bool), reflect P b -> b -> P *)
Check elimTn.                             (* forall (P : Prop) (b : bool), forall (P : Prop) (b' : bool), reflect P (~~ b') -> b' -> ~ P *)
Check elimN.                              (* forall (P : Prop) (b : bool), reflect P b -> ~~ b -> ~ P *)
(* apply//で使用： *)
Check equivPif.                           (* forall (P Q : Prop) (b : bool), reflect P b -> (Q -> P) -> (P -> Q) -> if b then Q else ~ Q *)
Check equivPifn.                          (* forall (P Q : Prop) (b : bool), reflect P (~~ b) -> (Q -> P) -> (P -> Q) -> if b then ~ Q else Q *)

(* move/で使用： *)
Check introTF.                            (* forall (P : Prop) (b c : bool), reflect P b -> (if c then P else ~ P) -> b = c *)
Check introNTF.                           (* forall (P : Prop) (b c : bool), reflect P b -> (if c then ~ P else P) -> ~~ b = c *)
Check introTFn.                           (* forall (P : Prop) (b c : bool), reflect P (~~ b) -> (if c then ~ P else P) -> b = c *)
(* apply/で使用： *)
Check introT.                             (* forall (P : Prop) (b : bool), reflect P b -> P -> b *)
Check introTn.                            (* forall (P : Prop) (b' : bool), reflect P (~~ b') -> ~ P -> b' *)
Check introN.                             (* forall (P : Prop) (b : bool), reflect P b -> ~ P -> ~~ b *)
(* apply//で使用： *)
Check xorPif.                             (* forall (P Q : Prop) (b : bool), reflect P b -> Q \/ P -> ~ (Q /\ P) -> if b then ~ Q else Q *)
Check xorPifn.                            (* forall (P Q : Prop) (b : bool), reflect P (~~ b) -> Q \/ P -> ~ (Q /\ P) -> if b then Q else ~ Q *)
  
Section Sample5.
  Variable a b : bool.
  Hypothesis andP : reflect (a /\ b) (a && b).
  Hypothesis nandP : reflect (~~ a \/ ~~ b) (~~ (a && b)).
  Hypothesis idP : reflect b b.

(**
andPまたはnandP を使う例
*)
  (* move/で使用： *)
  Check elimTF andP.                        (* a && b = c -> if c then a /\ b else ~ (a /\ b) *)
  Check elimNTF andP.                       (* ~~ (a && b) = c -> if c then ~ (a /\ b) else a /\ b *)
  Check elimTFn nandP.                      (* a && b = c -> if c then ~ (~~ a \/ ~~ b) else ~~ a \/ ~~ b *)
  (* apply/で使用： *)
  Check elimT andP.                         (* a && b -> a /\ b *)
  Check elimTn nandP.                       (* a && b -> ~ (~~ a \/ ~~ b) *)
  Check elimN andP.                         (* ~~ (a && b) -> ~ (a /\ b) *)
  (* apply//で使用： *)
  Check equivPif andP.                      (* (c -> a /\ b) -> (a /\ b -> c) -> if a && b then c else ~ c*)
  Check equivPifn nandP.                    (* (c -> ~~ a \/ ~~ b) -> (~~ a \/ ~~ b -> c) -> if a && b then ~ c else c *)
 
  (* move/で使用： *)
  Check introTF andP.                       (* (if c then a /\ b else ~ (a /\ b)) -> a && b = c *)
  Check introNTF andP.                      (* (if c then ~ (a /\ b) else a /\ b) -> ~~ (a && b) = c *)
  Check introTFn nandP.                     (* (if c then ~ (~~ a \/ ~~ b) else ~~ a \/ ~~ b) -> a && b = c *)
  (* apply/で使用： *)
  Check introT andP.                        (* a /\ b -> a && b *)
  Check introTn nandP.                      (* (~~ a \/ ~~ b) -> a && b *)
  Check introN andP.                        (* (a /\ b) -> ~~ (a && b) *)
  (* apply//で使用： *)
  Check xorPif andP.                        (* c \/ a /\ b -> ~ (c /\ a /\ b) -> if a && b then ~ c else c *)
  Check xorPifn nandP.                      (* c \/ ~~ a \/ ~~ b -> ~ (c /\ (~~ a \/ ~~ b)) -> if a && b then c else ~ c *)

(**
idPまたはidPn を使う例
*)
  (* move/で使用： *)
  Check elimTF idP.                        (* b = c -> if c then b else ~ b *)
  Check elimNTF idP.                       (* ~~ b = c -> if c then ~ b else b *)
  Check elimTFn idPn.                      (* a = b -> if b then ~ ~~ a else ~~ a *)
  (* apply/で使用： *)
  Check elimT idP.                         (* b -> b *)
  Check elimTn idPn.                       (* b -> ~ ~~ b *)
  Check elimN idP.                         (* ~~ b -> ~ b *)
  (* apply//で使用： *)
  Check equivPif idP.                      (* (c -> b) -> (b -> c) -> if b then c else ~ c*)
  Check equivPifn idPn.                    (* (c -> ~~ b) -> (~~ b -> c) -> if b then ~ c else c *)
 
  (* move/で使用： *)
  Check introTF idP.                       (* (if c then b else ~ b) -> b = c *)
  Check introNTF idP.                      (* (if c then ~ b else b) -> ~~ b = c *)
  Check introTFn idPn.                     (* (if c then ~ ~~ b else ~~ b) -> b = c *)
  (* apply/で使用： *)
  Check introT idP.                        (* b -> b *)
  Check introTn idPn.                      (* ~ ~~ b -> b *)
  Check introN idP.                        (* ~ b -> ~~ b *)
  (* apply//で使用： *)
  Check xorPif idP.                        (* c \/ b -> ~ (c /\ b) -> if a && b then ~ c else c *)
  Check xorPifn idPn.                      (* c \/ ~~ b -> ~ (c /\ ~~ b) -> if b then c else ~ c *)
End Sample5.

(* END *)
