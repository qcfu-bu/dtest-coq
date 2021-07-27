
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import ast.

(* one step reduction *)
Inductive value : term -> Prop :=
| value_tt : value TT
| value_pi : forall A B, value (Pi A B)
| value_fun : forall s, value (Fun s).

Inductive step : term -> term -> Prop :=
| step_beta s t u :
  value t -> 
  u = s.[Fun s,t/] -> 
  step (App (Fun s) t) u
| step_appL s1 s2 t :
  step s1 s2 -> 
  step (App s1 t) (App s2 t)
| step_appR s t1 t2 :
  value s ->
  step t1 t2 -> 
  step (App s t1) (App s t2)
| step_castS s1 s2 A :
  step s1 s2 -> 
  step (Cast s1 A) (Cast s2 A)
| step_castR s A :
  value s -> 
  step (Cast s A) s.


(* TODO this can be parameterized to any definition od step and value *)
Definition Stuck e := not (value e) /\ not (exists e', step e e').

(* TODO values don't step *)
(* TODO step is deterministic *)

(*TODO final type soundness, well typed terms don't get stuck *)
