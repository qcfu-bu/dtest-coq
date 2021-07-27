
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import astCast.
Require Import confluenceCast.

Notation "Gamma `_ i" := (dget Gamma i) (at level 2).

Reserved Notation "[ Gamma |- ]".
Reserved Notation "[ Gamma |- s :- A ]".

(* TODO reorder constructors to mach paper *)
Inductive has_type : list term -> term -> term -> Prop :=
| ty_tt Gamma :
  [ Gamma |- TT :- TT ]
| ty_var Gamma x :
  x < size Gamma ->
  [ Gamma |- Var x :- Gamma`_x ]
| ty_pi Gamma A B :
  [ Gamma |- A :- TT ] ->
  [ A :: Gamma |- B :- TT ] ->
  [ Gamma |- Pi A B :- TT ]
| ty_fun Gamma A B s :
  [ Gamma |- Pi A B :- TT ] ->
  [ (Pi A B).[ren (+1)] :: A :: Gamma |- s :- B.[ren (+1)] ] ->
  [ Gamma |- Fun s :- Pi A B ]
| ty_app Gamma A B f a :
  [ Gamma |- f :- Pi A B ] ->
  [ Gamma |- a :- A ] ->
  [ Gamma |- App f a :- B.[a/] ]
| ty_cast Gamma A A' s o :
  [ Gamma |- A' :- TT ] ->
  [ Gamma |- A :- TT ] ->
  [ Gamma |- s :- A' ] -> 
  [ Gamma |- Cast s A' A o :- A ]
| ty_conv Gamma A B s :
  A === B ->
  [ Gamma |- s :- A ] ->
  [ Gamma |- s :- B ]
where "[ Gamma |- s :- A ]" := (has_type Gamma s A).

Inductive context_ok : list term -> Prop :=
| ctx_nil : [ [::] |- ]
| ctx_ncons Gamma A : 
  [ Gamma |- A :- TT ] -> 
  [ Gamma |- ] ->
  [ A :: Gamma |- ]
where "[ Gamma |- ]" := (context_ok Gamma).

Notation "[ Gamma |- t ]" := [ Gamma |- t :- TT ].
Notation "[ Delta |- sigma -| Gamma ]" :=
  (forall x, x < size Gamma -> 
    [ Delta |- sigma x :- (Gamma `_ x).[ sigma : _ -> _ ] ]).

(* TODO would preffer a mutually inductive definition *)
(* TODO when has_ty, ty matches up to === *)
