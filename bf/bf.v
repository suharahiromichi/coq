(* はとさん作 *)
Require Import List Arith Ascii String.
Import ListNotations.
Open Scope string_scope.

Inductive prim := PtrIncr | PtrDecr | Incr | Decr | Get.

Inductive stmt :=
| SNil : stmt
| Prim : prim -> stmt -> stmt
| Put : stmt -> stmt
| Loop : stmt -> stmt -> stmt.

Fixpoint parse' (str : string) : (stmt * list stmt)%type :=
  match str with
  | "" => (SNil, nil)
  | String x xs =>
    let (body, rest) := parse' xs in
    match x with
    | ">"%char => (Prim PtrIncr body, rest)
    | "<"%char => (Prim PtrDecr body, rest)
    | "+"%char => (Prim Incr body, rest)
    | "-"%char => (Prim Decr body, rest)
    | ","%char => (Prim Get body, rest)
    | "."%char => (Put body, rest)
    | "["%char =>
      match rest with
      | nil => (Loop body SNil, nil)
      | cons s rest' => (Loop body s, rest')
      end
    | "]"%char => (SNil, cons body rest)
    | _ => (SNil, nil)
    end
  end.

Definition parse str := fst (parse' str).


Definition run_prim (env : (nat -> nat) * nat * list nat) p :=
  let '(data, ptr, input) := env in
  match p with
  | PtrIncr => (data, S ptr, input)
  | PtrDecr => (data, pred ptr, input)
  | Incr => (fun i => if Nat.eq_dec i ptr then S (data ptr) else data i,
                      ptr, input)
  | Decr => (fun i => if Nat.eq_dec i ptr then pred (data ptr) else data i,
                      ptr, input)
  | Get =>
    match input with
    | [] => env
    | x::rest => (fun i => if Nat.eq_dec i ptr then x else data i,
                           ptr, rest)
    end
  end.

Fixpoint append (s1 s2 : stmt) :=
  match s1 with
  | SNil => s2
  | Prim p s => Prim p (append s s2)
  | Put s => Put (append s s2)
  | Loop b s => Loop b (append s s2)
  end.

Ltac run env c' :=
  let c := eval compute in c' in
  match env with
  | (?data, ?ptr, ?input) =>
    match c with
    | SNil => idtac
    | Prim ?p ?c' =>
      let env' := eval compute in (run_prim (data,ptr,input) p) in
      run env' c'
    | Put ?c' =>
      let x := eval compute in (data ptr) in
      idtac x;
      run env c'
    | Loop ?c1 ?c2 =>
      let x := eval compute in (Nat.eq_dec (data ptr) 0) in
      match x with
      | left _ => run env c2
      | right _ => run env (append c1 (Loop c1 c2))
      end
    end
  end.

Goal True.
  run ((fun _:nat=>0), 0, [4;3]) (parse ",>,<[-<+>]<.").
Abort.

Goal True.
  run ((fun _:nat=>0), 0, [3;3]) (parse ",>,<[->[->>+<<]>>[-<+<+>>]<<<]>>.").
Abort.

Goal True.
  run ((fun _:nat=>0), 0, @nil nat) (parse "+[>.+<]").
Abort.