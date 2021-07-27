
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* presyntax *)

Inductive term : Type :=
| Var (x : var)
| TT
| App (s t : term)
| Fun (s : {bind 2 of term})
| Pi (s : term) (t : {bind term})
| Cast (s t : term).



Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance substLemmas_term : SubstLemmas term. derive. Qed.

