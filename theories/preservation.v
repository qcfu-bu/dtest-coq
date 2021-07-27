


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


(* preservation *)

Theorem subject_reduction Gamma s A :
[ Gamma |- ] -> [ Gamma |- s :- A ] ->
forall t, pstep s t -> [ Gamma |- t :- A ].
Proof with eauto using has_type, context_ok.
move=> wf tp. elim: tp wf => {Gamma s A}.
- move=> Gamma x si wf t st. inv st...
- move=> Gamma wf t st. inv st...
- move=> Gamma A B tp1 ih1 tp2 ih2 wf t st. inv st.
apply: ty_pi. exact: ih1. eapply ty_ctx_conv1.
+ apply: ih2...
+ exact: conv1i.
+ exact: tp1.
- move=> Gamma A B s tp1 ih1 tp2 ih2 wf2 t st. inv st.
apply: ty_fun.
+ exact: tp1.
+ eapply ih2 => //.
  econstructor.
  replace (TT) with (TT.[ren (+1)]) by autosubst.
  exact: weakening.
  move: tp1 => /ty_pi_inv[tp _].
  econstructor => //.
- move=> Gamma A B s t tp1 ih1 tp2 ih2 wf t' st. inv st.
+ move: H2 => /pstep_fun.
  move: (wf) => /ih1 h => {tp1 ih1} /h tp1.
  move: (tp1) => /ty_fun_inv.
  move: (wf) (H4) => /ih2 h => {tp2 ih2} /h tp2 tp3.
  move: (tp1) => /weakening h1.
  move: tp3 => /ty_cut h2.
  move: (h2 _ (h1 A)) => {h1 h2} => h.
  move: h => /ty_cut h.
  move: (h _ tp2) => {h}. asimpl.
  apply: ty_conv.
  apply: conv_beta.
  exact: conv1i.
+ pose proof (conv1i H3).
  have: (B.[t2/] === B.[t/]) by apply conv_beta.
  move=> h.
  apply: ty_conv.
  apply: h.
  apply: ty_app.
  apply: ih1 => //.
  apply: ih2 => //.
- move=> Gamma A s tp ih wf t st. inv st.
+ apply ih => //.
+ apply: ty_conv.
  exact: (conv1i H3).
  apply: ty_cast.
  apply: ty_conv.
  exact: (conv_sym (conv1i H3)).
  apply ih => //.
- move=> Gamma A B s eq tp ih wf t st.
apply (ty_conv eq).
apply: ih => //.
Qed.

(* TODO likwise for small steps *)