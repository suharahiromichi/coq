(**
問題：全射・単射と左逆・右逆写像

A が空でないと仮定すれば、選択原理を使うことによって、
全射 f : A → B があれば逆方向の単射 g : B → A が構成でき、
逆に単射 f : A → B があれば逆方向の全射 g : B → A を構成することができます

# Lean

- 演習問題
https://lean-ja.github.io/lean-by-example/Tutorial/Exercise/InverseSurjInj.html

- 解答
https://github.com/lean-ja/lean-by-example/blob/main/LeanByExample/Tutorial/Solution/InverseSurjInj.lean

- ビデオ
https://www.youtube.com/watch?v=aWUmWX5Nro4&t=2727s


# MathComp

- 個人メモ
https://gitlab.com/proofcafe/karate/-/blob/main/4.1_Axioms.v

- projT1 について
ssrcoq.pdf
Dependent Pairs

- choice　について
Karate-coq.pdf
4.1.4 Consequences of Classical Axioms
*)

(**
# MathComp による解答
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_classical.

(* 全射 *)
Definition surjective {B A : Type} (f : A -> B) := forall b : B, exists a : A, f a = b.
Check @surjective : forall B A : Type, (A -> B) -> Prop.

(* 単射 mathcomp の定意を使用する。 *)
Print injective.
Check injective : forall B A : Type, (A -> B) -> Prop.
Check fun (B A : Type) (f : A -> B) => forall x1 x2 : A, f x1 = f x2 -> x1 = x2.
  
Section InverseSurjInj.

  Variable A B : Type.

(**
## 問1: 全射から逆方向の単射

全射 `f : A → B` があれば、選択原理を使用することにより
単射 `g : B → A` を作ることができる
*)
(**
考え方：
gをfの逆と考える。fは全射なので、fの値域B全体が、gの定義域Bになる。
しかし、gの定義域Bのひとつの要素が、値域Aの複数の要素に対応してしまう。
当該対応を「消す」すなわち制限すると、gの値域はA全体でなくなるが、これは値域Aとして構わない。
その制限は、論理式 P = (fun b a => f a = b) で行う。
*)
  Lemma surj_to_inj (f : A -> B) :
    surjective f -> exists g : B -> A, injective g.
  Proof.
    move=> hsurj.
    
    (* 命題 existential quant *)    
    Check hsurj : forall b, exists a : A, f a = b.
    
    (* 強い依存型に変換する。 *)
    Check choice
      : forall (X Y : Type) (P : X -> Y -> Prop),
        (forall x : X, exists y : Y, P x y) -> {f : X -> Y & forall x : X, P x (f x)}.

    (* choice はスコーレム関数の存在を言っているが、こういう便利な使い方もある。 *)
    Check @choice B A (fun b a => f a = b) hsurj.
    Check choice hsurj                      (* sum strong dep *)
      : {g : B -> A & forall x : B, f (g x) = x}. (* g はまだ名前は決まっていない。 *)
    
    (* 強い依存型から、値と証明を取り出す。 *)
    Check projT1 (choice hsurj).            (* 値 *)
    pose g := projT1 (choice hsurj).        (* 関数 g *)
    Check g : B -> A.
    
    Check projT2 (choice hsurj).            (* 証明 *)
    pose hg := projT2 (choice hsurj).
    Check hg                                (* 一見複雑な式だが、 *)
      : forall x : B, f (projT1 (choice (P:=fun (b : B) (a : A) => f a = b) hsurj) x) = x.
    Check hg : forall x : B, f (g x) = x.   (* 簡単な式とマッチする。 *)
    (* have gdef : forall x, f (g x) = x by move=> x; apply hg. *)
    have gdef : forall x, f (g x) = x := hg.
    
    exists g.
    rewrite /injective => a b.
    rewrite -{2}(gdef b) -{2}(gdef a).
    by move=> ->.
  Qed.

(**
## 問2: 単射から逆方向の全射

単射 `f : A → B` があれば、選択原理を使用することにより
全射 `g : B → A` を作ることができる。
 *)
  Lemma em_ex (f : A -> B) b : {exists a, f a = b} + {~(exists a, f a = b)}.
  Proof.
    by apply: pselect.
  Defined.                                  (* !!! *)
  
  Definition g' (hnonempty : inhabited A) (f : A -> B) : B -> A.
  Proof.
    move=> b.
    case: (em_ex f b) => H.
    - by apply: (projT1 (cid H)).     (* lean の Classical.choose h *)
    - by apply: inhabited_witness.
  Defined.
  
  Lemma inj_to_surj (f : A -> B) :
    inhabited A -> injective f -> exists g : B -> A, surjective g.
  Proof.
    move=> hnonempty hinj.
    pose g := g' hnonempty f.
    
    have gdef : forall a, g (f a) = a.
    {
      (* rewrite /injective in hinj. *)
      move=> a.
      rewrite /g /g' /em_ex.

      case: pselect => H.
      (* H が成り立つ場合 *)
      - apply: hinj.
        Check projT2 (cid H) : f (projT1 (cid (P:=fun a0 : A => f a0 = f a) H)) = f a.
        by rewrite (projT2 (cid H)). (* lean の Classical.choose_spec h *)
        
      (* H が成り立たない場合。 *)
      - exfalso.
        apply: H.
        by exists a.
    }.
    
    exists g.
    rewrite /surjective => a.
    exists (f a).
    by rewrite gdef.
  Qed.

End InverseSurjInj.

(* END *)
