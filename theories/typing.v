

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



(* typing, in the style of type assignemnt *)

Notation "Gamma `_ i" := (dget Gamma i) (at level 2).

Reserved Notation "[ Gamma |- ]".
Reserved Notation "[ Gamma |- s :- A ]".

Inductive has_type : list term -> term -> term -> Prop :=
| ty_var Gamma x :
  x < size Gamma ->
  [ Gamma |- Var x :- Gamma`_x ]
| ty_tt Gamma :
  [ Gamma |- TT :- TT ]
| ty_pi Gamma A B :
  [ Gamma |- A :- TT ] ->
  [ A :: Gamma |- B :- TT ] ->
  [ Gamma |- Pi A B :- TT ]
| ty_fun Gamma A B s :
  [ Gamma |- Pi A B :- TT ] ->
  [ (Pi A B).[ren (+1)] :: A :: Gamma |- s :- B.[ren (+1)] ] -> 
  (* why +1 ? what is the orientation of gamma and the bound 
   * vars inside of it. seems more reasonable to do A+1 *)
  [ Gamma |- Fun s :- Pi A B ]
| ty_app Gamma A B s t :
  [ Gamma |- s :- Pi A B ] ->
  [ Gamma |- t :- A ] ->
  [ Gamma |- App s t :- B.[t/] ]
| ty_cast Gamma A s :
  [ Gamma |- s :- A ] ->
  [ Gamma |- Cast s A :- A ] 
  (* with the reductoin behavour, at the type level some 
   * weirdness is allowed by this rule *)
| ty_conv Gamma A B s :
  A === B ->
  [ Gamma |- s :- A ] ->
  [ Gamma |- s :- B ]
where "[ Gamma |- s :- A ]" := (has_type Gamma s A).

(* for progress *)

Lemma canonical_form_pi s P A B :
  [ [::] |- s :- P ] -> value s -> P === Pi A B ->
  exists s', s = Fun s'.
Proof.
  elim=> [].
  - move=> Gamma x si v eq. inv v.
  - move=> Gamma v eq.
    apply conv_sym in eq.
    apply conv_pi_tt in eq => //.
  - move=> Gamma A0 B0 _ ih1 _ ih2 v eq.
    apply conv_sym in eq.
    apply conv_pi_tt in eq => //.
  - move=> Gamma A0 B0 s0 _ ih1 _ ih2 v eq.
    exists s0 => //.
  - move=> Gamma A0 B0 s0 t _ ih1 _ ih2 v eq. inv v.
  - move=> Gamma A0 s0 _ ih v eq. inv v.
  - move=> Gamma A0 B0 s0 eq1 _ ih v eq2.
    apply: ih => //. eapply conv_trans.
    exact: eq1. exact: eq2.
Qed.

Lemma ty_app' Gamma A B s t u :
  [ Gamma |- s :- Pi A B ] ->
  [ Gamma |- t :- A ] ->
  u = B.[t/] ->
  [ Gamma |- App s t :- u ].
Proof. 
 intros.
 rewrite H1.
 apply: ty_app.
 eauto.
 auto.
Qed.

Inductive context_ok : list term -> Prop :=
| ctx_nil :
[ [::] |- ]
| ctx_ncons Gamma A :
[ Gamma |- A :- TT ] ->
[ Gamma |- ] ->
[ A :: Gamma |- ]
where "[ Gamma |- ]" := (context_ok Gamma).

Lemma ty_evar Gamma (A : term) (x : var) :
A = Gamma`_x -> x < size Gamma -> [ Gamma |- Var x :- A ].
Proof. move->. exact: ty_var. Qed.

Lemma ty_eapp Gamma (A B C s t : term) :
C = B.[t/] ->
[ Gamma |- s :- Pi A B ] -> [ Gamma |- t :- A ] ->
[ Gamma |- App s t :- C ].
Proof. move=>->. exact: ty_app. Qed.


Notation "[ Gamma |- s ]" := [ Gamma |- s :- TT ].

Lemma ty_tt_wf Gamma : [ Gamma |- TT ].
Proof. exact: ty_tt. Qed.
Hint Resolve ty_tt_wf ty_tt.

Lemma ty_pi_wf Gamma A B :
[ Gamma |- A ] -> [ A :: Gamma |- B ] -> [ Gamma |- Pi A B ].
Proof. exact: ty_pi. Qed.




Notation "[ Delta |- sigma -| Gamma ]" :=
(forall x, x < size Gamma -> [ Delta |- sigma x :- (Gamma`_x).[(sigma : _ -> _)] ]).

Lemma ty_renaming xi Gamma Delta s A :
[ Gamma |- s :- A ] ->
(forall x, x < size Gamma -> xi x < size Delta) ->
(forall x, x < size Gamma -> (Gamma`_x).[ren xi] = Delta`_(xi x)) ->
[ Delta |- s.[ren xi] :- A.[ren xi] ].
Proof with eauto using has_type.
move=> tp. elim: tp xi Delta => {Gamma s A} /=.
- move=> Gamma x si xi Delta subctx ->...
- move=> Gamma xi Delta subctx eqn...
- move=> Gamma A B _ ih1 _ ih2 xi Delta subctx eqn.
apply: ty_pi. exact: ih1. asimpl. apply: ih2.
+ by move=> [//|x /subctx].
+ by move=> [_|x /eqn/=<-]; autosubst.
- move=> Gamma A B s _ ih1 _ ih2 xi Delta subctx eqn.
apply ty_fun. by apply ih1. asimpl.
replace (B.[ren (1 .: xi >>> (+2))]) with
    (B.[ren (+1)].[ren (0 .: 1 .: xi >>> (+2))]) by asimpl => //.
apply ih2.
+ move=> [//|]. by move => [//|x /subctx].
+ move=> [|]. autosubst.
  move=> [|n /eqn/=<-]; autosubst.
- move=> Gamma A B s t _ ih1 _ ih2 xi Delta subctx eqn //=.
apply: (@ty_eapp _ A.[ren xi] B.[up (ren xi)]). autosubst.
  exact: ih1. exact: ih2.
- move=> Gamma A s _ ih xi Delta subctx eqn.
apply: ty_cast...
- move=> Gamma A B s eq _ ih xi Delta subctx eqn.
apply: (@ty_conv _ A.[ren xi] B.[ren xi]).
exact: conv_subst. exact: ih.
Qed.

Lemma weakening Gamma s A B :
[ Gamma |- s :- A ] -> [ B :: Gamma |- s.[ren (+1)] :- A.[ren (+1)] ].
Proof. move=> /ty_renaming. exact. Qed.

Lemma eweakening Gamma s s' A A' B :
s' = s.[ren (+1)] -> A' = A.[ren (+1)] ->
[ Gamma |- s :- A ] -> [ B :: Gamma |- s' :- A' ].
Proof. move=>->->. exact: weakening. Qed.

Lemma ty_ok Gamma :
[ Gamma |- ] -> forall x, x < size Gamma -> [ Gamma |- Gamma`_x ].
Proof.
elim=> // {Gamma} Gamma A tp _ ih [_|x /ih {tp} tp];
      exact: weakening tp.
Qed.

Lemma sty_up sigma Gamma Delta A :
[ Delta |- sigma -| Gamma ] ->
[ A.[sigma] :: Delta |- up sigma -| A :: Gamma ].
Proof.
move=> stp [_//|x /stp tp] /=. apply: ty_evar => //=. autosubst.
apply: eweakening tp; autosubst.
Qed.

Lemma ty_subst sigma Gamma Delta s A :
[ Delta |- sigma -| Gamma ] -> [ Gamma |- s :- A ] ->
[ Delta |- s.[sigma] :- A.[sigma] ].
Proof.
move=> stp tp. elim: tp sigma Delta stp => {Gamma s A} /=.
- move=> Gamma x si sigma Delta stp.
exact: stp.
- move=> Gamma sigma Delta stp => //.
- move=> Gamma A B _ ih1 _ ih2 sigma Delta stp.
apply: ty_pi. exact: ih1. apply ih2. exact: sty_up.
- move=> Gamma A B s _ ih1 _ ih2 sigma Delta stp.
apply: ty_fun. by eapply ih1.
replace (B.[up sigma].[ren (+1)]) with
    (B.[ren (+1)].[upn 2 sigma]) by asimpl => //.
apply: ih2 => x si.
rewrite <- fold_up_up.
replace ((Pi A.[sigma] B.[up sigma]).[ren (+1)]) with
    ((Pi A.[ren (+1)] B.[up (ren (+1))]).[up sigma]) by asimpl => //.
apply: sty_up => // => {x si} x si.
exact: sty_up.
- move=> Gamma A B s t _ ih1 _ ih2 sigma Delta stp.
apply: (@ty_eapp _ A.[sigma] B.[up sigma]). autosubst.
exact: ih1. exact: ih2.
- move=> Gamma A s _ ih sigma Delta stp.
apply: ty_cast. exact: ih.
- move=> Gamma A B s eq _ ih sigma Delta stp.
apply: (@ty_conv _ A.[sigma] B.[sigma]).
exact: conv_subst. exact: ih.
Qed.

Lemma ty_cut Gamma s t A B :
[ A :: Gamma |- s :- B ] -> [ Gamma |- t :- A ] ->
[ Gamma |- s.[t/] :- B.[t/] ].
Proof.
move=> /ty_subst h tp. apply: h => -[_|x leq]; asimpl => //.
exact: ty_var.
Qed.

Lemma ty_ctx_conv1 Gamma s A B C :
[ A :: Gamma |- s :- C ] -> B === A -> [ Gamma |- A :- TT ] ->
[ B :: Gamma |- s :- C ].
Proof.
move=> tp1 conv tp2. cut ([ B :: Gamma |- s.[ids] :- C.[ids] ]). autosubst.
apply: ty_subst tp1. move=> [_|x //=]. asimpl. eapply ty_conv.
apply: conv_subst conv.
eapply ty_var => //.
move=> le. asimpl. exact: ty_var.
Qed.

Lemma ty_ctx_conv2 Gamma s A1 A2 B1 B2 C :
[ A1 :: B1 :: Gamma |- s :- C ] -> A2 === A1 -> B2 === B1 ->
[ Gamma |- B1 :- TT ] -> [ B1 :: Gamma |- A1 :- TT ] -> 
[ A2 :: B2 :: Gamma |- s :- C ].
Proof.
move=> tp1 conv1 conv2 tp2 tp3.
cut ([ A2 :: B2 :: Gamma |- s.[ids] :- C.[ids] ]).
autosubst.
apply: ty_subst tp1. move=> [_|[_|x]].
- asimpl. eapply ty_conv. apply: conv_subst conv1. exact: ty_var.
- asimpl. eapply ty_conv. apply: conv_subst conv2.
replace (B2.[ren (+2)]) with
    ([:: A2, B2 & Gamma]`_1) by autosubst.
exact: ty_var.
- move=> le. asimpl.
replace (ids x.+2) with
    ((Var x).[ren (+1)].[ren (+1)]) by autosubst.
replace (Gamma`_ x.[ren (+2)]) with
    ((Gamma`_ x).[ren (+1)].[ren (+1)]) by autosubst.
apply weakening. apply weakening.
exact: ty_var.
Qed.

Lemma ty_pi_inv Gamma A B :
[ Gamma |- Pi A B :- TT ] ->
[ Gamma |- A :- TT ] /\ [ A :: Gamma |- B :- TT ].
Proof.
move e:(Pi A B) => s tp. elim: tp A B e => //{Gamma s}.
- move=> Gamma A B tp1 _ tp2 _ A' B' [->->] => //.
- move=> Gamma A B s eq tp ih A' B' e.
subst. elim: (ih A' B') => // => tp1 tp2.
eauto using has_type.
Qed.

Lemma ty_fun_invX Gamma s A B C :
[ Gamma |- Fun s :- C ] -> (C === Pi A B) ->
[ (Pi A B).[ren (+1)] :: A :: Gamma |- s :- B.[ren (+1)] ].
Proof with eauto using conv_subst, conv_sym, conv_pi.
move e:(Fun s) => t tp eq. elim: tp A B s e eq => // {Gamma C t}.
- move => Gamma A B s tp1 ih1 tp2 ih2 A' B' s' [->].
move=> /inj_pi[e1 e2].
apply: ty_conv. apply: conv_subst e2.
apply: (ty_ctx_conv2 tp2)...
elim: (ty_pi_inv tp1) => //.
replace (TT) with (TT.[ren (+1)]) by autosubst.
by apply: weakening.
- move=> Gamma A B s eq1 tp1 ih A' B' s' e eq2. subst.
+ apply: ih => //.
  exact: conv_trans eq1 eq2.
Qed.

Lemma ty_fun_inv Gamma s A B :
[ Gamma |- Fun s :- Pi A B ] ->
[ (Pi A B).[ren (+1)] :: A :: Gamma |- s :- B.[ren (+1)] ].
Proof. move=> tp. apply: (ty_fun_invX tp). apply: convR. Qed.






(* non bidirectional *)
Lemma nonbi :
  [ nil |- App (Fun (Var 1)) TT :- TT ].
Proof. 
 intros.
 apply: ty_app'.
 Focus 2.
 apply: ty_tt.
 apply: ty_fun.
 apply: ty_pi.
 apply: ty_tt.
 apply: ty_tt.
 simpl.
 apply: ty_var.
 auto.
 auto.
Qed.

Print nonbi.
