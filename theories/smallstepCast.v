

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import astCast.

(* one step reduction *)

Inductive tysyntax : term -> Prop :=
| tysyntax_tt : tysyntax TT
| tysyntax_Pi : forall A B, tysyntax (Pi A B).

Inductive blame : path -> term -> Prop :=
| blame1 o f A B : blame o (Cast f (Pi A B) TT o)
| blame2 o f A B : blame o (Cast f TT (Pi A B) o)
(* structual *)
| blameCast1 o o' a A B : blame o a -> blame o (Cast a A B o')
| blameCast2 o o' a A B : blame o A -> blame o (Cast a A B o')
| blameCast3 o o' a A B : blame o B -> blame o (Cast a A B o')

| blameappf o f a : blame o f -> blame o (App f a)
| blameappa o f a : blame o a -> blame o (App f a).

Inductive value : term -> Prop :=
| value_tt : value TT
| value_pi : forall A B, value (Pi A B)
| value_fun : forall b, value (Fun b)
| value_c : forall e t u o, 
  not (tysyntax e) -> 
  value e -> 
  value t -> 
  value u -> 
  value (Cast e u t o).

Inductive step : term -> term -> Prop :=
(* beta reductions *)
| step_beta b a :
    value a ->
    step (App (Fun b ) a) (b.[Fun b,  a /])

| step_cast_beta f a A B A' B' o :
  value f -> value a -> (* for deterministic evaluation order *)
  step 
    (App (Cast f (Pi A B) (Pi A' B') o) a)
    (let a' := Cast a A' A (Aty o) in
    Cast (App f a') (B.[a' /]) (B'.[ a/]) (BodTy a o))

(* cast reductions *)
| step_castTT e o :
  value e -> (* for deterministic evaluation order *)
    step (Cast e TT TT o) e

(* unrolled evaluation ctx*)

| step_castTT1 e u t e' o :
  step e e' -> 
    step (Cast e u t o) (Cast e' u t o)

| step_castTT2 e u t u' o :
  value e -> (* for deterministic evaluation order *)
  step u u' ->
    step (Cast e u t o) (Cast e u' t o)

| step_castTT3 e u t t' o :
  value e -> value u -> (* for deterministic evaluation order *)
  step t t' ->
    step (Cast e u t o) (Cast e u t' o)

| step_appL f f' a:
    step f f' -> 
    step (App f a) (App f' a)

| step_appR f a a':
    value f ->
    step a a' -> 
    step (App f a) (App f a').

(* TODO values don't step *)
(* TODO step is deterministic *)

(* TODO this can be parameterized to any definition on step and value *)
Definition Stuck e := not (value e) /\ not (exists e', step e e').
