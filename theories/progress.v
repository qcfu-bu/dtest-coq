


From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import ast.
Require Import smallstep.
Require Import confluence.
Require Import typing.



Theorem progress s t :
[ [::] |- s :- t ] ->
(value s) \/ (exists s', step s s').
Proof with eauto using step.
move=> H. dependent induction H.
- inv H.
- left. econstructor.
- left. econstructor.
- left. econstructor.
- assert (value s \/ (exists s' : term, step s s')) by apply IHhas_type1 => //.
assert (value t \/ (exists s' : term, step t s')) by apply IHhas_type2 => //.
case: H1. case: H2.
+ move=> v1 v2.
  apply (@canonical_form_pi s (Pi A B) A B) in H => //.
  elim: H => x ->. right...
+ move=> [] v => x st. right...
+ move=> [] => x st. right...
- assert (value s \/ (exists s' : term, step s s')) by apply IHhas_type => //.
case: H0.
+ move=> v. right...
+ move=> [] => s' st. right...
- assert (value s \/ (exists s' : term, step s s')) by apply IHhas_type => //.
case: H1.
+ move=> v. left => //.
+ move=> [] => s' st. right...
Qed.



Theorem type_soundnes : forall s t s',
[ [::] |- s :- t ] ->
star step s s' -> not (Stuck s').
Admitted.
