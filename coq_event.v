(* 
   イベントにより状態を遷移するプログラム
   システムのとりうる必要十分な状態を代数的に定義することで、
   不具合のないプログラムが作成できるという主張。
   
   例題は、以下の前半部分
   http://www.itpl.co.jp/tech/func/event-driven.pdf
   *)
Require Import List.

Inductive button : Type :=
| Bar : button
| Line : button
| Scatter : button.

Inductive event : Type :=
| Nul : event                               (* なにもしない。 *)
| Chk : event                               (* モードの切り替え。 *)
| Btn : button -> event.                    (* ボタンの押下 *)

Inductive state : Type :=           (* とりうる状態はすべて表現できる。 *)
| OverWrite : list button -> state          (* 複数選択モード *)
| Normal : button -> state.                 (* 唯一選択のラジオボタンモード *)

Hypothesis eq_dec : forall {A : Type} (x y : A), {x = y} + {x <> y}.
Hypothesis eq_nat_dec : forall x y : nat, {x = y} + {x <> y}.
Hypothesis eq_btn_dec : forall x y : button, {x = y} + {x <> y}.

Fixpoint ov (b : button) (bs : list button) : list button :=
  match bs with
    | nil => b :: nil                 (* 最後に至ったら、追加する。 *)
    | b' :: bs' =>
      match eq_dec b b' with                (* eq_dec button b b' *)
        | left _ => bs' (* 見つかったら、重複はないので、取り除いて終わり *)
        | right _ => b' :: (ov b bs') (* 違ったら、そのまま、先に進む。 *)
(* このmatchは、if-then-elseと同じ、
   if eq_dec b b' then bs' else b :: (ov b bs') *)
      end
  end.

Definition ts (e : event) (s : state) : state :=
  match (e, s) with
    | (Nul, e') => e'
    | (Chk, Normal _) => OverWrite nil
    | (Chk, OverWrite _) => Normal Bar
    | (Btn b, Normal _) => Normal b
    | (Btn b, OverWrite bs) => OverWrite (ov b bs)
  end.

Eval cbv in ts Nul (Normal Bar).            (* Normal Bar *)
Eval cbv in ts Chk (Normal Bar).            (* Normal Bar *)
Eval cbv in ts Chk (OverWrite (Bar::Line::Scatter::nil)). (* OverWrite nil *)
Eval cbv in ts (Btn Line) (Normal Bar).     (* Normal Line *)
Eval cbv in ts (Btn Line) (OverWrite (Bar::Line::Scatter::nil)).
(* OverWrite [Bar, Scatter] *)
Eval cbv in ts (Btn Line) (OverWrite nil).  (* OverWrite [Line] *)

Definition safe_ts (e : event) (s : state) : {s' | ts e s = s'}.
Proof.
  unfold ts.
  case e.
  case s.
  intros.
  exists (OverWrite l).
  reflexivity.

  intros.
  exists (Normal b).
  reflexivity.

  case s.
  intros.
  exists (Normal Bar).
  reflexivity.

  intros.
  exists (OverWrite nil).
  reflexivity.

  case s.
  intros.
  exists (OverWrite (ov b l)).
  reflexivity.
  
  intros.
  exists (Normal b0).
  reflexivity.
Defined.

Definition op_ts (e : event) (s : state) := proj1_sig (safe_ts e s).

Eval cbv in op_ts Nul (Normal Bar).         (* Normal Bar *)
Eval cbv in op_ts Chk (Normal Bar).         (* Normal Bar *)
Eval cbv in op_ts Chk (OverWrite (Bar::Line::Scatter::nil)). (* OverWrite nil *)
Eval cbv in op_ts (Btn Line) (Normal Bar).  (* Normal Line *)
Eval cbv in op_ts (Btn Line) (OverWrite (Bar::Line::Scatter::nil)).
Eval cbv in op_ts (Btn Line) (OverWrite nil). (* OverWrite [Line] *)

Extraction button.
Extraction event.
Extraction state.
Extraction ov.
Extraction ts.

Extraction op_ts.
Extraction safe_ts.

(* END *)
