(**
Coqのmatch式の内部構造を見る
========================

@suharahiromichi

2022/02/25
*)
From elpi Require Import elpi.

(**
# match式の定義

## Coq項 (Gallina項) のmatch式の定義

```
match <term_0> [return <term_t>] with
[ | <ident_1> => <term_1> ]。。。
end.
```

r``return <term_t>`` は、match式の返す型を書きます、ただし、省略できます。
*)

(**
## HOASにおけるElpiの``match``コンストラクタの定義

```
type match term -> term -> list term -> term.
```

Elpiの``match``コンストラクタは、検査される項、
return節、および分岐のリストを引数にとります。
各分岐は、対応するコンストラクタの引数を入力とする Coq 関数です。
順序は帰納型宣言のコンストラクタの順序に従います。

引数は順番に

- 検査される項
- return節
- 分岐のリスト

return節は、match式の型を書きます。Coq項の場合と異なり、match式の入力から書きます。
また、省略できません。

分岐のリストの要素の順序は、検査される項の
帰納型宣言のCoqのコンストラクタの順序に従います。
検査される項のコンストラクタがネストしてる場合は、``match``コンストラクタもネストします。

分岐のリストの要素は、対応するCoqのコンストラクタの引数を入力とする関数であり、
Elpiの``fun``コンストラクタで構成されます。ここで``name``はCoqの表示名で、
Coq項をCoqでPrintする場合に使いますが、Elpi-Coqで処理する場合には情報として使いません。

```
type fun  name -> term -> (term -> term) -> term.
```
*)

(**
# 定義済みの定数に定義されたCoq項 (Gallina項) のHOASを印刷するコマンド
*)
Elpi Command print.
Elpi Accumulate lp:{{
main [str Name] :-
	coq.locate Name (const Const),
	coq.env.const Const (some Bo) Ty,
	coq.say "Bo=" Bo,
	coq.say "Ty=" Ty.
}}.
Elpi Typecheck.

(**
# 単純な例
*)
Definition test_nat (n : nat) : bool :=
	match n return bool with	(* return bool は省略できる。 *)
	| O => true
	| S m => false
	end.

Elpi print test_nat.
(**
```
fun `n`							% test_natの引数の表示名
    (global (indt «nat»)) 		% test_natの引数の型
 	c0 \　match c0												 % 検査される項
	   (fun `n` (global (indt «nat»)) c1 \ global (indt «bool»))  % return節
　　　  [
	　  global (indc «true»), 									 % 分岐のリストの第1要素
   	　　fun `m`													　% 分岐のリストの第2要素
　　　　	(global (indt «nat»)) 
		   c1 \ global (indc «false»)
	   ]
```

test_nat の定義は、Elpiの``fun``コンストラクタで定義され、表示名``n``の自然数型をとる関数です。
ここで、test_natの引数は、内部的に c0 となります。

``match``コンストラクタの検査される項は c0 です。
return節は、このmatch式全体を示す型であり、Coqの型の``nat -> bool``です。
Coq-Elpiでは依存型のforallにあたる``fun``を
省略しないので、``forall (n : nat), bool``のように表現されていますが、同じことです。

nat型のCoqのコンストラクタは、``O : nat``と``S : nat -> nat``
のふたつだったことを思い出してください。分岐のリストの各要素は、Coqのコンストラクタに対応し、
それぞれのCoqのコンストラクタの引数が渡されます。

第1要素は、Coqのコンストラクタ``O``に対応しますが、
これには引数がないので、単にbool型の値を``true``が置かれています。

第2要素は、Coqのコンストラクタ``S``に対応し、その引数であるnatをうけとってboolを返す関数として、
``fun (n : nat) => false`` が置かれます。

このように分岐リストの各要素は、Coqの型としては異なったものになります。
ただし、Elpiの型としては、どれも``term``型です。

以下では、``Elpi print``の結果をコピーすると煩瑣なので、``{{}}``の中に
Coq項を書くことにします。

```
fun `n`											% test_natの引数の表示名
    {{nat}}										% test_natの引数の型
	c0 \ match c0								% matchの検査される型
	 			(fun `n` {{nat}} c1 \ {{bool}})	% matchの型
	  			[{{true}},						% 分岐のリストの第1要素
   			 	 fun `m` {{nat}} c1 \ {{false}}] % 分岐のリストの第2要素
```
*)

(**
# 重複のある自然数の例

## MathComp Book ch1.v の例

ただし Standard Coqに変換した。
*)
Definition three_patterns n :=
	match n return nat with		(* return nat は省略できる。 *)
	| S (S (S (S (S u)))) => u 	(* case 1 *)
	| S v => v           		(* case 2 *)
	| 0 => n              		(* case 3 *)
	end.

(**
実行例
*)
Compute three_patterns 0.   (* 0 *)(* case 3 *)
Compute three_patterns 1.   (* 0 *)(* case 2 *)
Compute three_patterns 2.   (* 1 *)(* case 2 *)
Compute three_patterns 3.   (* 2 *)(* case 2 *)
Compute three_patterns 4.   (* 3 *)(* case 2 *)
Compute three_patterns 5.   (* 0 *)(* case 1 *)
Compute three_patterns 6.   (* 1 *)(* case 1 *)
Compute three_patterns 7.   (* 2 *)(* case 1 *)
Compute three_patterns 8.   (* 3 *)(* case 1 *)
Compute three_patterns 9.   (* 4 *)(* case 1 *)
Compute three_patterns 10.  (* 5 *)(* case 1 *)
Compute three_patterns 11.  (* 6 *)(* case 1 *)

Elpi print three_patterns.
(**
```
fun `n` {{nat}}
        c0 \ match c0 (fun `n` {{nat}} c1 \ {{nat}}) 
                   [c0, 
                    fun `v` {{nat}}
                        c1 \ match c1 (fun `v` {{nat}} c2 \ {{nat}}) 
                                  [c1, 
                                   fun `n0` {{nat}}
                                            c2 \ match c2 (fun `n0` {{nat}} c3 \ {{nat}}) 
                                                       [c1, 
                                                        fun `n1` {{nat}}
                                                            c3 \ match c3 (fun `n1` {{nat}} c4 \ {{nat}}) 
                                                                       [c1, 
                                                                        fun `n2` {{nat}}
                                                                            c4 \ match c4 (fun `n2` {{nat}} c5 \ {{nat}})
                                                                                       [c1,
                                                                                        fun `u` (global (indt «nat»)) c5 \ c5]]]]]
```
*)

(**
## Coqの内部構造に忠実な定義

``return nat`` は省略しています。
*)
Definition three_patterns' c0 :=
  match c0 with
  | 0 => c0                                           	(* case 0 *)
  | S c1 => match c1 with
			| 0 => c1                                 	(* csae 1 *)
			| S c2 => match c2 with
					  | 0 => c1                       	(* case 2 *)
					  | S c3 => match c3 with
								| 0 => c1             	(* csae 3 *)
								| S c4 => match c4 with
										  | 0 => c1   	(* case 4 *)
										  | S c5 => c5  (* case 5 *)
										  end
								end
					   end
			end
	end.
(**
実行例
*)
Compute three_patterns' 0.   (* 0 *)(* case 0 *)
Compute three_patterns' 1.   (* 0 *)(* case 1 *)
Compute three_patterns' 2.   (* 1 *)(* case 2 *)
Compute three_patterns' 3.   (* 2 *)(* case 3 *)
Compute three_patterns' 4.   (* 3 *)(* case 4 *)
Compute three_patterns' 5.   (* 0 *)(* case 5 *)
Compute three_patterns' 6.   (* 1 *)(* case 5 *)
Compute three_patterns' 7.   (* 2 *)(* case 5 *)
Compute three_patterns' 8.   (* 3 *)(* case 5 *)
Compute three_patterns' 9.   (* 4 *)(* case 5 *)
Compute three_patterns' 10.  (* 5 *)(* case 5 *)
Compute three_patterns' 11.  (* 6 *)(* case 5 *)    

(**
ふたつの定義が同じであることの証明
*)
Goal forall n, three_patterns n = three_patterns' n.
Proof. easy. Qed.

(**
# match に　returnを明示する場合

とくに変わったことはありません。
*)

Definition Data (b : bool) : Set :=
	if b then nat else unit.

Definition sample_ret b :=
match b return Data b with
| true => 0
| false => tt
end.

Elpi print sample_ret.
(**
```
fun `b` {{bool}}
		c0 \ match c0 (fun `b` {{bool}} c1 \ app [{{Data}}, c1]) 
  					[{{O}},
					 {{tt}}]
```
*)

(* END *)
