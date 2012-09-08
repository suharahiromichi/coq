(* 
   AVTR コントロールパネルの仕様記述
   2012_09_07
   *)

(* MFDS型 *)
Inductive mfd : Set :=
| Left : mfd
| Center : mfd
| Right : mfd.

(* 違うものは異なることを「証明」しておく *)
Lemma notlc : Left <> Center.
Proof.
  discriminate.
Qed.

Lemma notlr : Left <> Right.
Proof.
  discriminate.
Qed.

Lemma notcl : Center <> Left.
Proof.
  discriminate.
Qed.

Lemma notcr : Center <> Right.
Proof.
  discriminate.
Qed.

Lemma notrl : Right <> Left.
Proof.
  discriminate.
Qed.

Lemma notrc : Right <> Center.
Proof.
  discriminate.
Qed.

(* MFDの2個選択状態をしめすレコード。後ろも参照 *)
Record mfds : Set := mkmfds {
  m1 : mfd;
  m2 : mfd;
  mc : m1 <> m2
}.

(* パネルの選択状態 *)
Inductive panel : Set :=
| Hud : panel
| Huds : mfd -> panel
| Mfd : mfd -> panel
| Mfds : mfds -> panel.

(* 制御線からの選択を加えた完全な状態 *)
Inductive state : Set :=
| Nml : panel -> state
| Gun : panel -> state.

(* イベント：スイッチ操作、制御線からの制御 *)
Inductive event : Set :=
| GunOn : event
| GunOff : event
| H : event
| M : mfd -> event.

(* MFDSの2個選択状態を作る。 *)
Definition xs m n : panel :=
  match m with
    | Left => match n with
                | Left => Mfd Left          (* NOTU *)
                | Center => Mfds (mkmfds Left Center notlc)
                | Right => Mfds (mkmfds Left Right notlr)
              end
    | Center => match n with
                  | Left => Mfds (mkmfds Center Left notcl)
                  | Center => Mfd Center    (* NOTU *)
                  | Right => Mfds (mkmfds Center Right notcr)
              end
    | Right =>  match n with
                  | Left => Mfds (mkmfds Right Left notrl)
                  | Center => Mfds (mkmfds Right Center notrc)
                  | Right => Mfd Right      (* NOTU *)
                end
    end.

Hypothesis eq_dec : forall {A : Type} (x y : A), {x = y} + {x <> y}.

(* HUD : HUDだけ選択中のとき *)
Definition hs (x : mfd) : panel :=
  Huds x.                                   (* HUD + MFD *)

(* HUD + MFD : HUDとMFDのラジオボタンモード *)
Definition rs (x m : mfd) : panel :=
  match (eq_dec x m) with
    | left _ => Hud                         (* HUD *) (* MFDは選択解除 *)
    | right _ => Huds x                     (* HUD + MFD *)
  end.

(* MFD : MFDひとつだけ *)
Definition ms (x m : mfd) : panel :=
  match (eq_dec x m) with
    | left _ => Mfd x                       (* MFD 変化なし。*)
    | right _ => xs x m                     (* MFD + MFD *)
  end.

(* MFD + MFD : MFDSがふたつ *)
Definition ds (x m n : mfd) : panel :=
  match (eq_dec x m) with
    | left _ => Mfd n                       (* MFD 選択解除 *)
    | right _  => match (eq_dec x n) with
                   | right _ => Mfd m       (* MFD 選択解除 *)
                   | left _ => xs m n       (* MFD + MFD 変化なし *)
                 end
  end.

(* ひとつの状態遷移 *)
Definition ts (e : event) (s : state) : state :=
match e with
  | GunOn => match s with
               | Nml p => Gun p             (* GUNになる *)
               | _ => s
             end
  | GunOff => match s with
                | Gun p => Nml p            (* NMLにもどる *)
                | _ => s
              end
  | H => match s with
           | Nml Hud => s                   (* HUD 変化なし *)
           | Nml (Huds m) => Nml (Mfd m)    (* MFD *) (* HUDは選択解除 *)
           | Nml (Mfd m) => Nml (Huds m)    (* HUD + MFD *)
           | Nml (Mfds (mkmfds m n _)) => s (* MFD + MFD 変化なし *)
           | _ => s
         end
  | M x => match s with
             | Nml Hud => Nml (hs x)        (* HUD + MFD *)
             | Nml (Huds m) => Nml (rs x m) (* HUD + MFD *)
             | Nml (Mfd m) => Nml (ms x m)  (* MFD + MFD *)
             | Nml (Mfds (mkmfds m n _)) => Nml (ds x m n) (* MFD + MFD *)
             | _ => s
           end
end.

Eval cbv in ts (M Left) (Nml Hud).
Eval cbv in ts (M Left) (Nml (Huds Left)).
Eval cbv in ts (M Center) (Nml (Huds Left)).
Eval cbv in ts (M Center) (Nml (Mfds (mkmfds Center Left notcl))).

(* OCamlコードの生成 *)
Extraction xs.                        (* ここに「証明」は含まない。 *)
Extraction ts.

(* Recordの意味 *)
Inductive mfds' : Set :=
  mkmfds' : forall (m1 : mfd) (m2 : mfd), (m1 <> m2 -> mfds').

Check (mkmfds Left Right notlr).
Check (mkmfds' Left Right notlr).

(* end *)
