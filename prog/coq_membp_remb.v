(**
The Little Prover (TLP) の第6章にある memb?/remb 定理をCoqで解いてみる。
 *)

Require Import Bool.
Require Import List.
Require Import Program.
Set Implicit Arguments.

(** * はじめに *)

(**
これは、リニアなリストの要素から、文字 '?' を削除する関数 remb と、
これは、リニアなリストの要素に、文字 '?' が含まれるかを判定する関数 memb? が
定義されているとき、
任意のリスト xs に対して、(memb? (remb xs)) が必ず False になるというものです。

オリジナルはLisp系の言語なので、リストの要素は任意のデータでよいのですが、
Coqの場合は、false と true からなる bool型のリストとし、もじ '?' の代わりに true とします。
  *)

(**
まず、membp (memb? に対応する) のリストにtrueが含まれていることを判定する関数を定義ましす。
リストの先頭から見ていき true が含まれていたらそこで True を返します。
*)

Fixpoint membp (xs : list bool) : Prop :=
  match xs with
  | nil => False
  | true :: xs' => True
  | false :: xs' =>  membp xs'
  end.

Compute membp (true :: false :: true :: nil).         (** ==> [True] *)

Compute membp (false :: false :: false :: nil).       (** ==> [False] *)

Compute membp nil.                                    (** ==> [False] *)

(**
ついで、remb のリストからtrueを削除する関数を定義します。
リストの先頭から見ていき true なら、それを含まない結果を返し
false なら、それを含む結果を返します。
*)

Fixpoint remb (xs : list bool) : list bool :=
  match xs with
  | nil => nil
  | true :: xs' => remb xs'
  | false :: xs' => false :: remb xs'
  end.

Compute remb (true :: false :: true :: nil).         (** ==> [[false]] *)

(** * memb?/remb の証明 *)

(**
memb?/remb に対応する membp_remb は、文字通りの定義です。
結果は偽であるため、「~」がついています。

以下に、membp_remb を証明します。線形リスト xs に対する帰納法と、
要素 x に対する場合分けだけで証明されています。
なお、帰納法の仮定IHxsは、ふたつめとみっつめのnowでトリビアルとされています。
 *)

Definition membp_remb (xs : list bool) := ~ membp (remb xs).
  
Goal forall (xs : list bool), membp_remb xs.
Proof.
  unfold membp_remb.
  intros xs.
  induction xs as [|x xs IHxs].
  - now simpl.
  - case x.
    + now simpl.
    + now simpl.

  Restart.
  unfold membp_remb.
  intros xs.
  induction xs as [|x xs IHxs]; try auto.
  now case x.
Qed.

(**
memb?/remb は定理としては自明ですが、trueが含まれないことをチェックする関数membpによって、
trueを削除する関数rembが正しく動作していることを証明する、と考えることができます。

これは、関数の定義とその証明を同時におこなう証明駆動開発の一例となります。
Coqにはそれをサポートする「Program」コマンドがあります。
これを使って remb を再定義してみましょう。

remb' の値は、単なる list bool ではなく、
[{ys : list bool | ~ membp ys}]
すなわち、
[~ membp ys] を満たす [ys] の集合の要素、
となります。

これだと、最初に想定した型と違うので困ると思うかもしれませんが、
「Program」コマンドの中では、そのサブタイプ・コアーションの機能によって、
list boot 型と同一視されます。

remb' の結果が普通にconsされていることに気づいてください。

「Program」コマンドの中では、そのサブタイプ・コアーションは、
再帰呼び出しのみならず、他の（定義済みの）任意な関数に適用されます。
 *)

Program Fixpoint remb' (xs : list bool) : {ys : list bool | ~ membp ys} :=
  match xs with
  | nil => nil
  | true :: xs' => remb' xs'
  | false :: xs' => false :: remb' xs'
  end.

(**
*response* ウインドウに

[[
Solving obligations automatically...
remb'_obligation_1 is defined
remb'_obligation_2 is defined
No more obligations remaining
remb' is defined
remb' is recursively defined (decreasing on 1st argument)
]]

と表示されたはずですが、これは自動的に証明が終わったことを意味します。
 *)

(**
remb' を「Program」コマンドの外から実行するときは、proj1_sig で値を取り出す必要があります。
*)

Compute ` (remb' (true :: false :: true :: nil)). (** ==> [[false]] *)

Extraction remb'.
(**
生成されたコードには、rembp は含まれていない。

[[
val remb' : bool list -> bool list

let rec remb' = function
| Nil -> Nil
| Cons (b, xs') ->
  (match b with
   | True -> remb' xs'
   | False -> Cons (False, (remb' xs')))
]]
*)

(** * 証明駆動開発 *)

(**
これからは、TLP の範囲を越える事項ですが、
remb' の定義を「リストからtrueを除去する関数」の証明付き定義と考えると問題があります。

membp はtrueの有無しかチェックしていませんから、
remb の本体が「つねにnil」を返すような定義であっても問題なくパスします。これではだめです。

remb の厳密な定義は、(1)に加えて(2)も満たさないといけません。

(1) 結果のリストに true が含まれないこと(0個であること)。

(2) もとのリストと結果のリストととで、false の個数が同じであること。
 *)


(**
リストのなかの true ないし false の個数を数える関数を定義します。
 *)

Fixpoint count_occ (l : list bool) (x : bool) : nat :=
  match l with
  | [] => 0
  | y :: tl =>
    match (x, y) with
    | (true, true) => S (count_occ tl x)
    | (false, false) => S (count_occ tl x)
    | _ => count_occ tl x
    end
  end.

Compute count_occ (true :: false :: true :: nil) true. (** ==> [2] *)

Compute count_occ (true :: false :: true :: nil) false. (** ==> [1] *)


(**
定理を直接証明します。
(1) と (2) を連言(/\)でつなぎます。
また let ... in は普通の意味で、ys は構文的な意味しかもちません。
*)


Goal forall (xs : list bool),
    let ys := remb xs in
    count_occ ys true = 0 /\  count_occ xs false = count_occ ys false.
Proof.
  intros xs.
  split.
  - induction xs as [| x' xs' IHxs].
    + now simpl.
    + case x'.
      * now simpl.
      * now simpl.
  - induction xs as [| x' xs'IHxs].
    + reflexivity.
    + case x' as [x' | y']; simpl in *.
      * now rewrite <- IHxs'IHxs.
      * now rewrite IHxs'IHxs.

  Restart.
  intros xs.
  split; induction xs as [|x xs IHxs]; auto; case x; auto.
  now case x; simpl; [rewrite <- IHxs | rewrite IHxs].
Qed.

(**
「Program」コマンドでの定義に条件を追加します。
今回も自動証明できました。
*)

Program Fixpoint remb'' (xs : list bool) :
  {ys : list bool | count_occ ys true = 0 /\
                    count_occ xs false = count_occ ys false} :=
  match xs with
  | nil => nil
  | false :: xs' => false :: remb'' xs'
  | true :: xs' => remb'' xs'
  end.

Compute ` (remb'' (true :: false :: true :: nil)). (** ==> [[false]] *)

Extraction remb''.

(**
生成されたコードには、count_occ は含まれていません。

[[
val remb'' : bool list -> bool list

let rec remb'' = function
| Nil -> Nil
| Cons (b, xs') ->
  (match b with
   | True -> remb'' xs'
   | False -> Cons (False, (remb'' xs')))
]]
 *)

(** * 帰納法の公理 *)

(**
TLPにもどって、帰納法による証明について考えてみましょう。

以下は、証明するべきものではなく、リストの型定義にもとづく「公理」です。
 *)

Check list_ind : forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (a : A) (l : list A), P l -> P (a :: l)) ->
    forall l : list A, P l.

Check list_ind membp_remb :
  membp_remb [] ->
  (forall (a : bool) (l : list bool), membp_remb l -> membp_remb (a :: l)) ->
  forall l : list bool, membp_remb l.

(**
この公理を使うなら、

[forall l : list bool, membp_remb l]

を証明するには、

[membp_remb []]

と

[(forall (a : bool) (l : list bool), membp_remb l -> membp_remb (a :: l))]

とを証明する必要があります。後者は、TLPでは、l は nil でないことを条件に、

[(forall (l : list bool), membp_remb (tl l) -> membp_remb l)]

となっています。おなじですね。
 *)

(**
実際の証明は、以下の通りです。
 *)

Goal forall xs, membp_remb xs.
Proof.
  intros xs.
  apply (list_ind membp_remb).              (* 公理を適用する。 *)
  - now simpl.
  - intros x l.
    case x.
    + now simpl.
    + now simpl.
Qed.

(* END *)
