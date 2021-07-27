
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import ast.
Require Import smallstep.
Require Import typing.
Require Import typing_bi.
Require Import astCast.
Require Import smallstepCast.
Require Import confluenceCast.
Require Import typingCast.

Inductive ElabInf : list astCast.term -> ast.term -> 
  astCast.term -> astCast.term -> Prop :=
  | ElabInfVar ctx x : ElabInf ctx (ast.Var x) (astCast.Var x) (dget ctx x)
  | ElabInfTT ctx : ElabInf ctx ast.TT astCast.TT astCast.TT 
    (* on paper this would require a well formed ctx *)
  | ElabInfPi ctx A A' B B':
    ElabCheck ctx A A' astCast.TT ->
    ElabCheck (A' :: ctx) B B' astCast.TT ->
    ElabInf ctx (ast.Pi A B) (astCast.Pi A' B') astCast.TT
  | ElabInfCast ctx e e' t t' : 
    ElabCheck ctx t t' astCast.TT ->
    ElabCheck ctx e e' t' ->
    ElabInf ctx (ast.Cast e t) e' t' 
    (* insert the cast at a discrepency *)
  | ElabInfapp ctx f f' fty a a' A B : 
    (* ElabInf ctx f f' (astCast.Pi A B) -> (* minimally *) *)
    ElabInf ctx f f' fty -> astCast.Pi A B === fty -> 
    ElabCheck ctx a a' A ->
    ElabInf ctx (ast.App f a) (astCast.App f' a') (B.[a' /])
with ElabCheck : list astCast.term -> ast.term -> 
  astCast.term -> astCast.term -> Prop :=
  | ElabCheckTT ctx : ElabCheck ctx ast.TT astCast.TT astCast.TT 
    (* TODO: this can be removed*)

  | ElabCheckFun ctx A B b b' : 
    ElabCheck ((astCast.Pi A B).[ren (+1)]  :: A :: ctx) b b' B ->
    ElabCheck ctx (ast.Fun b) (astCast.Fun b') (astCast.Pi A B)
  | ElabCheckinf ctx a a' A A' : 
    ElabInf ctx a a' A' ->
    ElabCheck ctx a (astCast.Cast a' A' A astCast.Here) A
.

(* TODO that mutually inductive scheme thing *)

(* CTX elaborations *)
Inductive ElabCtx : list ast.term -> list astCast.term -> Prop :=
| ElabCtx_Emp : ElabCtx nil nil
| ElabCtx_cons ctx ctx' e e' : ElabCtx ctx ctx' -> 
  ElabCheck ctx' e e' astCast.TT -> ElabCtx (e :: ctx) (e' :: ctx')
.


Fixpoint erase (e : ast.term) : astCast.term :=
  match e with
  | ast.Var x    => astCast.Var x
  | ast.TT       => astCast.TT
  | ast.App f a  => astCast.App (erase f) (erase a)
  | ast.Fun b    => astCast.Fun (erase b)
  | ast.Pi a b => astCast.Pi (erase a) (erase b)
  | ast.Cast e t => erase e
  end.

(* TODO: elab (unique enough) *)

(* gragual garentee like conditions, review this with robin *)


Theorem well_typed_terms_elaborate e t :
  [ nil |- e :-> t ] ->
  exists e' t' ,
  ElabInf nil e e' t'.
Proof.
Admitted.

(* TODO a cast varient? *)

(* this is a weak theorem about syntax, it would be nicer to have a stronger theorem about semantics *)
(* can this be strengthend against the TAS? *)
Theorem blameable_terms_were_not_well_typed e e' t :
  (star smallstepCast.step) e e' ->
  smallstepCast.Stuck e' -> 
  not (exists ee tt, 
    typing.has_type nil ee tt /\ 
    ElabCheck nil ee e t)
  .
Admitted.
(* follows directly from type soundenss and the corespondece with elaborated terms *)

Theorem elab_corresponds_TT e e' :
  typingCast.has_type nil e' astCast.TT ->
  ElabCheck nil e e' astCast.TT ->
  (star smallstepCast.step) e' astCast.TT ->
  (star smallstep.step) e ast.TT
  .
Admitted.

Theorem elab_corresponds_Pi e e' a' b' :
  ElabCheck nil e e' astCast.TT ->
  (star smallstepCast.step) e' (astCast.Pi a' b') ->
  exists a b,
  (star smallstep.step) e (ast.Pi a b)
  .
Admitted.











