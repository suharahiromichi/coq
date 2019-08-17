(**
ProofCafe 名古屋 補足資料

萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版

[http://www.morikita.co.jp/books/book/3287]

3.7 View 補足説明

@suharahiromichi

2019_08_17
*)

From mathcomp Require Import all_ssreflect.

(**
# 3.7 View
 *)

Section Test1.

  Variable P Q R : Prop.
  Hypothesis V1 : Q -> R.
  Hypothesis V2 : P -> Q.
  
(**
## apply/V

apply/V は、まず最初は、apply: V と同じと覚えてよいです。

apply/V1/V2 のように複数の命題を書くことができます。
これば、バニラCoqの apply V1, V2 とおなじです。
MathComp では、apply: V1 V2 が、move:V2; apply: V1 の意味になり、
apply: (V1 V2) が、V2にV1を適用した後に…となることに注意してください。
 *)

  Goal P -> R.
  Proof.
    move=> HP.
    apply/V1/V2.
    done.

    Restart.
    intros HP.
    apply V1, V2.
    done.
  Qed.

(**
## move/V

move/V はゴールのスタックトップに適用します。

move/V2/V1 のように複数の命題を書くことができます。
apply/V1/V2 と逆順であることに注意してください。

(バニラCoqでは、前提に適用する場合は apply in)
 *)

  Goal P -> R.
  Proof.
    move/V2/V1.
    done.

    Restart.
    Show.
    move=> HP. move: (V2 HP) => {HP}.
    move=> HQ. move: (V1 HQ) => {HQ}.
    done.
  Qed.

(**
## move/V in H

バニラCoqでは、apply V in H で、文脈にある前提に適用できますが、
MathComp では、move/V in H です。間違い易いので覚えましょう。
*)
  
  Goal P -> R.
  Proof.
    move=> HP.
    move/V2 in HP.
    move/V1 in HP.
    (* まとて move/V2/V1 in HP でもよい。 *)
    done.

    (* 式を直接書く方がよいかもしれない。 *)
    Restart.
    Show.
    move=> HP.
    move: (V1 (V2 HP)).                     (* => {HP} *)
    (*
    move: (V2 HP) => {HP} HQ.
    move: (V1 HQ) => {HQ}
     *)
    done.
    
    (* バニラCoq *)
    Restart.
    Show.
    intro HP.
    apply V2 in HP.
    apply V1 in HP.
    (* まとて apply V2, V1 in HP でもよい。 *)
    done.
  Qed.

(**
## case/V

スタックトップにVを適用して、その後、そのスタックトップで場合分けする意味です。
move/V; case.

なお、elim/T_ind は、帰納法T_indを使う指示(using)なので、まったく異なります。
(see. csm_3_5_elim.v)
*)

End Test1.

(**
# 解釈補題 (P <-> Q)

V : P <-> Q のかたちの補題を使う場合、以下のView Hintが自動適用されます。
 *)

Check iffLR   : forall P Q : Prop, P <-> Q -> P -> Q.
Check iffRL   : forall P Q : Prop, P <-> Q -> Q -> P.
Check iffLRn  : forall P Q : Prop, P <-> Q -> ~ P -> ~ Q.
Check iffRLn  : forall P Q : Prop, P <-> Q -> ~ Q -> ~ P.

Section Test2.

(**
これにより、P <-> Q の補題を P -> Q と Q -> P のほか、
否定を含むかたちで使うことができます。
*)

  Variable P Q : Prop.
  Hypothesis V : P <-> Q.                   (* 解釈補題 *)
  
  Check iffLR V    : P -> Q.
  Check iffRL V    : Q -> P.
  Check iffLRn V   : ~ P -> ~ Q.
  Check iffRLn V   : ~ Q -> ~ P.

End Test2.

(**
# Reflect補題 (reflect P b)

V : reflect P b のかたちの補題を使う場合、以下のView Hintが自動適用されます。

リフレクション補題はMathCompのなかで、xxP の名前で証明されています。
eqP, andP, orP, netP など。
*)

Check elimT
  : forall (P : Prop) (b : bool), reflect P b -> b -> P.
Check elimN
  : forall (P : Prop) (b : bool), reflect P b -> ~~ b -> ~ P.
Check elimTF
  : forall (P : Prop) (b c : bool), reflect P b -> b = c -> if c then P else ~ P.
Check elimNTF
  : forall (P : Prop) (b c : bool), reflect P b -> ~~ b = c -> if c then ~ P else P.
Check elimTF
  : forall (P : Prop) (b c : bool), reflect P b -> b = c -> if c then P else ~ P.
Check elimNTF
  : forall (P : Prop) (b c : bool), reflect P b -> ~~ b = c -> if c then ~ P else P.
  
Check introT
  : forall (P : Prop) (b : bool), reflect P b -> P -> b.
Check introN
    : forall (P : Prop) (b : bool), reflect P b -> ~ P -> ~~ b.
Check introTF
  : forall (P : Prop) (b c : bool), reflect P b -> (if c then P else ~ P) -> b = c.
Check introNTF
  : forall (P : Prop) (b c : bool), reflect P b -> (if c then ~ P else P) -> ~~ b = c.
Check introTF
  : forall (P : Prop) (b c : bool), reflect P b -> (if c then P else ~ P) -> b = c.
Check introNTF
  : forall (P : Prop) (b c : bool), reflect P b -> (if c then ~ P else P) -> ~~ b = c.

Section Test3.

(**
これにより、reflect P b の補題を P -> と や P -> b のほか、
否定を含むかたちで使うことができます。
*)
  Variable P : Prop.
  Variable b : bool.
  Hypothesis V : reflect P b.               (* リフレクション補題 *)

  Check @elimT P b V          : b -> P.
  Check @elimN P b V          : ~~ b -> ~ P.
  Check @elimTF P b true V    : b = true -> P.
  Check @elimNTF P b true V   : ~~ b = true -> ~ P.
  Check @elimTF P b false V   : b = false -> ~ P.
  Check @elimNTF P b false V  : ~~ b = false -> P.
  
  Check @introT P b V         : P -> b.
  Check @introN P b V         : ~ P -> ~~ b.
  Check @introTF P b true V   : P -> b = true.
  Check @introNTF P b true V  : ~ P -> ~~ b = true.
  Check @introTF P b false V  : ~ P -> b = false.
  Check @introNTF P b false V : P -> ~~ b = false.


  Goal b -> P.
  Proof.
    move=> Hb.
    (* Goal: P *)
    apply/V.
    Undo 1. Show.
    apply: (@elimT P b V).
    (* Goal: b *)
    done.

    Restart.
    Show.
    (* Goal: b -> P *)
    move/V.
    Undo 1. Show.
    move/(@elimT P b V).
    (* Goal: P -> P *)
    done.
  Qed.
  
(**
リフレクション補題Vをviewで使うと、
Propの型の命題をboolの型に変換できる、と理解して間違いではありませんが、
以下に2点補足しておきます。
 *)

(**
## 厳密には P と b ではなく、P と b = true の間で変換されている
 *)

  Goal b = true -> P.
  Proof.
    move/V.
    Show Proof.                             (* elimTF が使われている。 *)

    Undo 1. Show.
    move/(@elimTF P b true V).
(*    
    Undo 1. Show.
    move=> Hb.
    apply/V.
    Show Proof.
*)
    done.
  Qed.
  
(**
## ~P と b = false の間の変換も可能である。
 *)

  Goal b = false -> ~ P.
  Proof.
    move/V.
    Show Proof.                          (* elimTF が使われている。 *)
    (* Goal :~ P -> ~ P  *)
    
    Undo 1. Show.
    move/(@elimTF P b false V).
    done.
  Qed.
  
End Test3.

(**
# それ以外の定石

## apply/(iffP idP)

reclect P b のリフレクション補題そのものを証明する場合に使います。

b -> P と P -> b のふたつのゴールを生成します。

 *)

Section Test4.
  
  Variable P : Prop.
  Variable b : bool.

  Goal reflect P b.
  Proof.
    apply/(iffP idP).
    - admit.                                (* goal : b -> P *)
    - admit.                                (* goal : P -> b *)      
  Admitted.                                 (* OK *)
  
End Test4.

(**
## apply/idP/idP

bool値どうしの「=」のゴールを「->」と「<-」のふたつのゴールに分解します。
 *)

Section Test5.

  Variables b1 b2 : bool.

  Goal b1 = b2.
  Proof.
    apply/idP/idP.
    - admit.                                (* goal : b1 -> b2 *)
    - admit.                                (* goal : b2 -> b1 *)

      Show Proof.
    Restart.
    Show.

    Check @introTF b1 b1 b2 idP.
    (* (if b2 then b1 else ~ b1) -> b1 = b2 *)
    Check @equivPif b2 b1 b2 idP.
    (* (b1 -> b2) -> (b2 -> b1) -> if b2 then b1 else ~ b1 *)
    
    apply: (@introTF b1 b1 b2 idP).
    (* goal : if b2 then b1 else ~ b1 *)
    apply: (@equivPif b2 b1 b2 idP).
    - admit.                                (* goal : b1 -> b2 *)
    - admit.                                (* goal : b2 -> b1 *)
  Admitted.                                 (* OK *)
    
(* END *)
