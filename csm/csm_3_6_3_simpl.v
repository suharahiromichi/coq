(**
ProofCafe 名古屋 補足資料

萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版

[http://www.morikita.co.jp/books/book/3287]

3.6.3 rewrite /= または simpl (simplifies タクティク) の説明をします。

本書 p.135 注記2 にも関連する記述があり、それについても言及します。

@suharahiromichi

2019_08_17

参考資料

[1] CRM simpl tactic
https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.simpl

[2] "Simple Simpl"
https://hal.archives-ouvertes.fr/hal-00816918/document

[3] CRM, The SSReflect proof language, locking unlocking
https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html#locking-unlocking
*)

From mathcomp Require Import all_ssreflect.

(** * simpl タクティク

Mathcomp で、rewrite /= または move=> /= を実行したとき、
バニラCoq の simpl タクティクが実行される。
Mathcomp で simpl をコマンドしてもよい。

simpl は、（ゴールに対して）項の簡約をするタクティクで、
simplification または simplify の略である。
多少駄洒落はあるかもしれないが[2]、「簡単な」計算を行うコマンドという説明は適切ではない。
ただし、簡約のことを計算と呼ぶのは支障ないだろう。

計算はできる限り繰り返し行われる。なので、simpl を2回以上繰り返す意味はない。
一方で、Coqなので必ず停止することは保証されている。
 *)
Goal true && (true || false).
Proof.
  rewrite /=.
  (* Goal : true *)
  done.
Qed.

(** 計算の対象をゴールの一部に限定することができる。案外便利である。
    指定の方法は 3.6.6 rewrite [条件] 要素名 を参照のこと。
 *)
Goal true && (true || false).
Proof.
  rewrite [true || false]/=.
  (* Goal : true && true *)
  rewrite /=.
  (* Goal : true *)
  done.
Qed.


(** * simpl タクティクはなにをするのか

まずは、βベータ簡約をする、と覚えて間違いない。
 *)

Definition first {T1 T2} (s : T1 * T2) :=
  match s with
  | (x, y) => x
  end.

Definition pair1 (s : (bool * bool) * (nat * nat)) :=
  match s with
  | (bs, ns) => (first bs, first ns)
  end.
(* 説明の都合から、回りくどい書き方をしています。 *)

Goal pair1 ((false, true), (1, 2)) = (false, 1).
Proof.
  simpl.
  done.
Qed.
(** 左辺は、
    pair1 ((false, true), (1, 2)) ==> (false, 1)
    とβ簡約されている。 *)

(** 実際にはもうすこし複雑である。 *)
Goal forall bs, pair1 (bs, (1, 2)) = (first bs, 1).
Proof.
  move=> bs.
  simpl.
  (* pair1 (bs, (1, 2)) ==>  (first bs, 1) *)
  
  (* 参考 *)
  Eval cbv delta                in pair1 (bs, (1, 2)).
  Eval cbv delta beta           in pair1 (bs, (1, 2)).
  Eval cbv delta beta zeta      in pair1 (bs, (1, 2)).
  Eval cbv delta beta zeta iota in pair1 (bs, (1, 2)).
  
  Restart.
  move=> bs.
  rewrite /pair1.
  rewrite [first (1, 2)]/=.
  done.
Qed.


(** 4段階を踏んでいる [2] ：

(1) pair1 の引数である (bs, (1, 2)) は、pair コンストラクタを逆につかって分解できる。
bs と (1,2) の pair。
    
(2) pair1 を unfold (ηイータ簡約）する。変数を置き換える（δデルタ簡約）とも。

(3) 実引数による仮引数の書換（βベータ簡約）をする。

(4) match の場合分け（ιイオタ簡約）をする。 (bs.1, (1,2).1) を得る。
ι簡約は、inductiveに定義された型の値を使う、という意味から。
（特別な場合として、letへの代入をζゼータ簡約という。）

(1) first の引数である (1, 2) に対して、以下同様にする。

これが、「ポアンカレ原理」を支える「計算」の実際といえるのだろう。
*)

(** fixpoint で定義された関数についても、同様に処理され、再帰的に行われる。
    Coqなので必ず停止する。  *)
Fixpoint bsize (s : seq bool) : nat := if s is _ :: s' then (bsize s').+1 else 0.

Goal bsize [:: true; false; true] = 3.
Proof.
  simpl.
  (* Goal : 3 = 3
     左辺が
     bsize [:: true; false; true] => 3
     とβ簡約された。 *)
  done.
Qed.

Goal forall b s, bsize (b :: s) = bsize s + 1.
Proof.
  move=> b s.
  simpl.
  (* Goal : (bsize s).+1 = bsize s + 1
     ... 左辺が
     bsize (b :: s) => (bsize s).+1
     とβ簡約された。 *)
    by rewrite -addn1.

  Restart.
  move=> b s.
  rewrite [bsize (b :: s)]/bsize.
    by rewrite -addn1.
Qed.

Goal forall b1 b2 s, bsize (b1 :: b2 :: s) = bsize s + 2.
  move=> b1 b2 s.
  simpl.
    by rewrite -addn2.
Qed.


(** * simpl の lock について

Mathcomp の自然数の加・減・乗・累乗・階乗 はlockされている。
そのため、simpl では、自然数の計算は行われない。
*)

Fixpoint fact n :=
  match n with
  | 0 => 1
  | n'.+1 => n * fact n'
  end.

Goal fact 3 = 6.
Proof.
  simpl.
  (* Goal : 3 * (2 * (1 * 1)) = 6 *)
  (* fact は簡約されるが、掛け算はそのまま。 *)
  
  apply: refl_equal.                        (* reflexivity *)
Qed.

(**
バニラCoqと異なり、Mathcomp では、simpl では自然数の計算は行えない。
これは、ゴールが大きくなることを避けるため、とされている。[3]

Mathcomp で、simpl では自然数の計算は行えないことは、
Mathcomp で omega が使えない理由のひとつ。もうひとつは le の定義の違い。
 *)

(* 
参考： ssrnat.v

Definition addn := nosimpl addn_rec.
Definition subn := nosimpl subn_rec.
Definition muln := nosimpl muln_rec.
Definition expn := nosimpl expn_rec.
Definition factorial := nosimpl fact_rec.
Definition double := nosimpl double_rec.

なお、.+1 や .*2 は計算される。
 *)


(**
lock を解除するには、以下のどれかを使う。[3]

unlockをunfold する。 rewrite /unlock
lockをfold する。     rewrite -/lock
unlock タクティクを使う。

（あるいは、simpl の代わりに cbn を使うこともできる [1]）

実際には、ssromegaタクティクの定義の中以外では、unlock する必要はないであろう。
 *)

Goal fact 3 = 6.
Proof.
  simpl.
  (* Goal : 3 * (2 * (1 * 1)) = 6 *)

  rewrite /muln /unlock /=.
  (* Goal : 6 = 6 *)
  
  done.
Qed.

(* END *)
