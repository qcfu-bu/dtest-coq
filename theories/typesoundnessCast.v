From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import astCast.
Require Import smallstepCast.
Require Import confluenceCast.
Require Import typingCast.

Lemma ty_evar Gamma (A : term) (x : var) :
  A = Gamma `_ x -> x < size Gamma -> [ Gamma |- Var x :- A ].
Proof. move=> -> sz. exact: ty_var. Qed.

Lemma ty_eapp Gamma (A B C s t : term) :
  C = B.[t/] ->
  [ Gamma |- s :- Pi A B ] ->
  [ Gamma |- t :- A ] ->
  [ Gamma |- App s t :- C ].
Proof. move=> ->. exact: ty_app. Qed.

Lemma ty_tt_wf Gamma : 
  [ Gamma |- TT ].
Proof. exact: ty_tt. Qed.

Lemma ty_pi_wf Gamma A B :
  [ Gamma |- A ] ->
  [ A :: Gamma |- B ] ->
  [ Gamma |- Pi A B ].
Proof. exact: ty_pi. Qed.

Lemma ty_renaming xi Gamma Delta s A :
  [ Gamma |- s :- A ] ->
  (forall x, x < size Gamma -> xi x < size Delta) ->
  (forall x, x < size Gamma -> (Gamma`_x).[ren xi] = Delta`_(xi x)) ->
  [ Delta |- s.[ren xi] :- A.[ren xi] ].
Proof with eauto using has_type.
  move=> tp. elim: tp xi Delta => { Gamma s A } /=...
  - move=> Gamma x si xi Delta subctx ->...
  - move=> Gamma A B _ ih1 _ ih2 xi Delta subctx eqn.
    apply: ty_pi...
    asimpl.
    apply: ih2.
    + by move=> [//| x /subctx].
    + by move=> [_|x /eqn/=<-]; fold_all; autosubst.
  - move=> Gamma A B s _ ih1 _ ih2 xi Delta subctx eqn.
    apply ty_fun. by apply ih1. fold_all; asimpl.
    replace (B.[ren (1 .: xi >>> (+2))]) with
      (B.[ren (+1)].[ren (0 .: 1 .: xi >>> (+2))]) by asimpl => //.
    apply ih2.
    + move=> [//|]. by move => [//|x /subctx].
    + move=> [|]; fold_all. autosubst.
      move=> [|n /eqn/=<-]; fold_all; autosubst.
  - move=> Gamma A B s t _ ih1 _ ih2 xi Delta subctx eqn //=.
    apply: (@ty_eapp _ A.[ren xi] B.[up (ren xi)]); fold_all. 
    + autosubst.
    + exact: ih1. 
    + exact: ih2.
  - move=> Gamma A B s eq _ ih xi Delta subctx eqn.
    apply: (@ty_conv _ A.[ren xi] B.[ren xi]).
    + exact: conv_subst. 
    + exact: ih.
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
  [ Delta |- sigma -| Gamma ] -> 
  [ Gamma |- s :- A ] ->
  [ Delta |- s.[sigma] :- A.[sigma] ].
Proof with eauto using has_type.
  move=> stp tp. 
  elim: tp sigma Delta stp => {Gamma s A} /=.
  - move=> Gamma sigma Delta stp => //...
  - move=> Gamma x sz sigma Delta stp.
    exact: stp.
  - move=> Gamma A B _ ih1 _ ih2 sigma Delta stp. 
    fold_all.
    apply: ty_pi. 
    + exact: ih1. 
    + apply ih2. 
      exact: sty_up.
  - move=> Gamma A B s _ ih1 _ ih2 sigma Delta stp.
    fold_all.
    apply: ty_fun. 
    + by eapply ih1.
    + replace (B.[up sigma].[ren (+1)]) with
        (B.[ren (+1)].[upn 2 sigma]) by asimpl => //.
      apply: ih2 => x si.
      rewrite <- fold_up_up.
      replace ((Pi A.[sigma] B.[up sigma]).[ren (+1)]) 
        with ((Pi A.[ren (+1)] B.[up (ren (+1))]).[up sigma]) 
          by asimpl => //.
      apply: sty_up => // => {x si} x si.
      exact: sty_up.
  - move=> Gamma A B s t _ ih1 _ ih2 sigma Delta stp.
    apply: (@ty_eapp _ A.[sigma] B.[up sigma]). 
    autosubst.
    + exact: ih1. 
    + exact: ih2.
  - move=> Gamma A A' s o _ ih1 _ ih2 _ ih3 sigma Delta stp.
    apply: ty_cast. 
    exact: ih1.
    exact: ih2.
    exact: ih3.
  - move=> Gamma A B s e _ ih1 sigma Delta stp.
    apply: (@ty_conv _ A.[sigma] B.[sigma]).
    + exact: conv_subst. 
    + exact: ih1.
Qed.

Lemma ty_cut Gamma s t A B :
  [ A :: Gamma |- s :- B ] -> [ Gamma |- t :- A ] ->
  [ Gamma |- s.[t/] :- B.[t/] ].
Proof.
  move=> /ty_subst h tp. 
  apply: h => -[_|x leq]; asimpl => //.
  exact: ty_var.
Qed.

Lemma ty_ctx_conv1 Gamma s A B C :
  [ A :: Gamma |- s :- C ] -> 
  B === A -> 
  [ B :: Gamma |- s :- C ].
Proof.
  move=> tp conv. 
  cut ([ B :: Gamma |- s.[ids] :- C.[ids] ]). autosubst.
  apply: ty_subst tp. move=> [_|x //=]. asimpl. eapply ty_conv.
  apply: conv_subst conv.
  eapply ty_var => //.
  move=> le. asimpl. exact: ty_var.
Qed.

Lemma ty_ctx_conv2 Gamma s A1 A2 B1 B2 C :
  [ A1 :: B1 :: Gamma |- s :- C ] -> 
  A2 === A1 -> 
  B2 === B1 ->
  [ Gamma |- B1 :- TT ] -> 
  [ B1 :: Gamma |- A1 :- TT ] -> 
  [ A2 :: B2 :: Gamma |- s :- C ].
Proof.
  move=> tp1 conv1 conv2 tp2 tp3.
  cut ([ A2 :: B2 :: Gamma |- s.[ids] :- C.[ids] ]).
  autosubst.
  apply: ty_subst tp1. move=> [_|[_|x]].
  - asimpl. eapply ty_conv. apply: conv_subst conv1. exact: ty_var.
  - asimpl. eapply ty_conv. apply: conv_subst conv2.
    replace (B2.[ren (+2)]) 
      with ([:: A2, B2 & Gamma]`_1) by autosubst.
    exact: ty_var.
  - move=> le. asimpl.
    replace (ids x.+2) 
      with ((Var x).[ren (+1)].[ren (+1)]) by autosubst.
    replace (Gamma`_ x.[ren (+2)]) 
      with ((Gamma`_ x).[ren (+1)].[ren (+1)]) by autosubst.
    apply weakening. 
    apply weakening.
    exact: ty_var.
Qed.

Lemma ty_pi_inv Gamma A B :
  [ Gamma |- Pi A B :- TT ] ->
  [ Gamma |- A :- TT ] /\ [ A :: Gamma |- B :- TT ].
Proof.
  move e:(Pi A B) => s tp. elim: tp A B e => //{Gamma s}.
  - move=> Gamma A B tp1 _ tp2 _ A' B' [->->] => //.
  - move=> Gamma A B s eq tp ih A' B' e.
    subst. 
    elim: (ih A' B') => // => tp4 tp5.
    split.
    apply: ty_conv; eauto.
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
    apply: ih => //.
    rewrite <- eq2...
Qed.

Lemma ty_fun_inv Gamma s A B :
  [ Gamma |- Fun s :- Pi A B ] ->
  [ (Pi A B).[ren (+1)] :: A :: Gamma |- s :- B.[ren (+1)] ].
Proof. move=> tp. apply: (ty_fun_invX tp). apply: convR. Qed.

Lemma ty_cast_inv Gamma s A B B' o :
  [ Gamma |- Cast s A B o :- B' ] -> 
  [ Gamma |- A ] /\
  [ Gamma |- B ] /\
  [ Gamma |- s :- A ] /\ B === B'.
Proof. 
  move=> tp.
  dependent induction tp.
  - firstorder.
    assert ([Gamma |- A] /\ 
            [Gamma |- B] /\ 
            [Gamma |- s :- A] /\ B === A0); 
    eauto; firstorder.
    apply: conv_trans; eauto.
Qed.

Theorem ps_subject_reduction Gamma s A :
  [ Gamma |- ] -> 
  [ Gamma |- s :- A ] ->
  forall t, pstep s t -> [ Gamma |- t :- A ].
Proof with eauto using has_type, context_ok, pstep.
  move=> wf tp. elim: tp wf => {Gamma s A}.
  - move=> Gamma wf t st. inv st...
  - move=> Gamma x si wf t st. inv st...
  - move=> Gamma A B tp1 ih1 tp2 ih2 wf t st. inv st.
    apply: ty_pi. exact: ih1. eapply ty_ctx_conv1.
    + apply: ih2...
    + exact: conv1i.
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
      apply: conv_beta; eauto.
      exact: conv1i.
    + have: (pstep 
        (Cast trm (Pi aty1 bodty1) (Pi aty bodty) o)
        (Cast trm' (Pi aty1' bodty1') (Pi aty' bodty') o'))...
      move=> ps.
      specialize (ih1 wf _ ps) => { ps }.
      specialize (ih2 wf _ H3).
      move: ih1 => /ty_cast_inv [tp3 [tp4 [tp5 eq]]].
      move: eq => /inj_pi [eq1 eq2].
      have: ([ Gamma |- ac :- aty1' ]).
      subst ac.
      apply: ty_cast.
      apply ty_pi_inv in tp4; firstorder.
      apply ty_pi_inv in tp3; firstorder. 
      apply: ty_conv.
      apply: conv_sym.
      apply: eq1.
      apply: ih2.
      move=> tp6.
      have: (bodty'.[a'/] === B.[t/]).
      apply: conv_beta...
      apply: (conv1i H3).
      move=> eq3.
      apply: ty_conv...
      apply: ty_cast...
      apply ty_pi_inv in tp3; firstorder.
      replace (TT) with (TT.[ac/]) by autosubst.
      apply: ty_cut...
      apply ty_pi_inv in tp4; firstorder.
      replace (TT) with (TT.[a'/]) by autosubst.
      apply: ty_cut...
      apply: ty_conv.
      apply: conv_sym...
      eauto.
    + pose proof (conv1i H3).
      have: (B.[a'/] === B.[t/]) by apply conv_beta.
      move=> h.
      apply: ty_conv.
      apply: h.
      apply: ty_app.
      apply: ih1 => //.
      apply: ih2 => //.
  - move=> Gamma A s t p tp1 ih1 tp2 ih2 tp3 ih3 wf t0 st. inv st.
    + apply: ih3 => //.
    + apply: ty_conv.
      apply: (conv1i H6).
      apply: ty_cast.
      apply: ih1...
      apply: ih2...
      apply: ty_conv.
      exact: (conv_sym (conv1i H5)).
      apply: ih3... 
  - move=> Gamma A B s eq tp ih wf t st.
    apply (ty_conv eq).
    apply: ih => //.
Qed.

Theorem step_subject_reduction Gamma s A :
  [ Gamma |- ] -> [ Gamma |- s :- A ] ->
  forall t, step s t -> [ Gamma |- t :- A ].
Proof.
  move=> wf tp t /step_pstep ps.
  apply: ps_subject_reduction; eauto.
Qed.

Theorem star_step_subject_reduction s t :
  star step s t -> 
  forall Gamma A,
    [ Gamma |- ] -> 
    [ Gamma |- s :- A ] ->
    [ Gamma |- t :- A ].
Proof.
  move=> ss.
  dependent induction ss; intros; eauto.
  specialize (IHss _ _ H0 H1).
  apply: step_subject_reduction.
  apply: H0.
  apply: IHss.
  apply: H.
Qed.

(* well typed terms don't get stuck without error *)

Lemma ty_fun_tt' Gamma s t :
  [ Gamma |- Fun s :- t ] -> t === TT -> False.
Proof.
  move=> tp.
  dependent induction tp.
  - move=> eq.
    pose proof (@conv_pi_tt A B) => //=.
  - move=> eq.
    assert (A === TT).
    rewrite H; eauto.
    eauto.
Qed.

Lemma ty_fun_tt Gamma s :
  ~ [ Gamma |- Fun s ].
Proof.
  unfold not=> tp.
  apply: ty_fun_tt'; eauto.
Qed.

Lemma tysyntax_tt :
  ~ (~ tysyntax TT).
Proof with eauto using tysyntax.
  unfold not...
Qed.

Lemma tysyntax_pi A B :
  ~ (~ tysyntax (Pi A B)).
Proof with eauto using tysyntax.
  unfold not...
Qed.

Lemma canonical_form_pi s P :
  [ [::] |- Fun s :- P ] -> (exists A B, P === Pi A B).
Proof with eauto using value, tysyntax.
  move=> tp.
  dependent induction tp...
  assert (exists A' B', A === Pi A' B').
  apply: IHtp...
  firstorder.
  exists x.
  exists x0.
  rewrite <- H...
Qed.

Lemma canonical_form_fun s P :
  [ [::] |- s :- P ] -> value s -> 
  forall A B, P === Pi A B -> 
  (exists s', s = Fun s') \/ 
  (exists s' u t o, 
    s = Cast s' u t o /\
    t === (Pi A B) /\
    value u /\
    value s').
Proof with eauto using value, tysyntax.
  move=> tp.
  dependent induction tp...
  - move=> v A B eq.
    apply conv_sym in eq.
    apply conv_pi_tt in eq => //.
  - move=> v A B eq. inv v.
  - move=> v A0 B0 eq.
    apply conv_sym in eq.
    apply conv_pi_tt in eq => //.
  - move=> v A0 B0 eq. inv v.
  - move=> v A0 B eq.
    right.
    inv v.
    exists s.
    exists A'.
    exists A.
    exists o.
    firstorder.
  - move=> v A0 B0 eq2.
    apply: IHtp => //. 
    rewrite <- eq2...
Qed.

Lemma canonical_form_ty t tt :
  value t ->
  [ [::] |- t :- tt ] -> 
  tt === TT ->
  TT = t \/
  (exists A B, Pi A B = t ) \/
  (exists o, blame o t).
Proof with eauto using tysyntax, value, has_type, blame.
  intros.
  dependent induction H...
  assert ([[::] |- Fun b ])...
  apply ty_fun_tt in H => //.
  right. right.
  move: H3 => /ty_cast_inv [ h1 [ h2 [ h3 h4 ] ] ].
  assert ([[::] |- u :- tt ]).
  apply: ty_conv.
  apply: conv_sym.
  apply: H4.
  apply: h1.
  specialize (IHvalue3 H3 H4).
  move: IHvalue3 => [ h5 | [ h6 | h7 ] ]; subst.
  assert ([[::] |- t :- tt]).
  apply: ty_conv.
  apply: conv_sym.
  apply: H4.
  apply: h2.
  specialize (IHvalue2 H5 H4).
  move: IHvalue2 => [ h8 | [ h9 | h10 ] ]; subst.
  assert ([[::] |- e :- tt]).
  apply: ty_conv.
  apply: conv_sym.
  apply H4.
  apply h3.
  specialize (IHvalue1 H6 H4).
  move: IHvalue1 => [ h5 | [ h6 | h7 ] ]; subst.
  apply tysyntax_tt in H => //.
  move: h6 => [ h7 [ h8 h9 ] ]; subst.
  apply tysyntax_pi in H => //.
  move: h7 => [ o' b ].
  exists o'...
  assert ([[::] |- e :- tt]).
  apply: ty_conv.
  apply: conv_sym.
  apply H4.
  apply h3.
  specialize (IHvalue1 H6 H4).
  move: IHvalue1 => [ h5 | [ h6 | h7 ] ]; subst.
  move: h9 => [ A [ B e ] ]; subst.
  apply tysyntax_tt in H => //.
  move: h9 => [ A [ B e' ] ]; subst.
  exists o...
  move: h7 => [ o' b ].
  exists o'...
  move: h10 => [ o' b ].
  exists o'...
  move: h6 => [ A [ B h7 ] ]; subst.
  assert ([[::] |- t :- tt]).
  apply: ty_conv.
  apply: conv_sym.
  apply: H4.
  apply: h2.
  specialize (IHvalue2 H5 H4).
  move: IHvalue2 => [ h5 | [ h6 | h7 ] ]; subst.
  exists o...
  move: h6 => [ A' [ B' e' ]]; subst.
  assert (Pi A' B' === TT).
  apply: conv_trans.
  apply: h4.
  apply: H4.
  apply conv_pi_tt in H6 => //.
  move: h7 => [ o' b ].
  exists o'...
  move: h7 => [ o' b ].
  exists o'...
Qed.

Theorem progress s t :
  [ [::] |- s :- t ] ->
  (value s) \/ (exists s', step s s') \/ (exists o, blame o s).
Proof with eauto using value, step, blame.
  move=> tp.
  dependent induction tp...
  - inv H.
  - firstorder...
    pose proof (canonical_form_fun tp1 H0 (conv_refl _)).
    case: H1 => [h1 | h2].
    + firstorder...
      right. left.
      exists (x.[f, a/]).
      subst...
    + firstorder.
      subst.
      inv H0 => { H11 }.
      apply ty_cast_inv in tp1; firstorder; subst.
      apply canonical_form_ty in H1...
      apply canonical_form_ty in H0...
      move: H1 => [ h1 | [ h2 | h3 ] ]; subst.
      apply conv_sym in H6.
      apply conv_pi_tt in H6 => //.
      move: h2 => [ A' [ B' e ] ]; subst.
      move: H0 => [ h1 | [ h2 | h3 ] ]; subst.
      right. right...
      move: h2 => [ A0 [ B0 e ] ]; subst.
      right. left...
      right. right.
      move: h3 => [ o b ]...
      move: H0 => [ h4 | [ h5 | h6 ] ]; subst.
      right. right.
      move: h3 => [ o b ]...
      right. right.
      move: h3 => [ o b ]...
      right. right.
      move: h3 => [ o b ]...
  - firstorder...
    apply canonical_form_ty in tp1...
    apply canonical_form_ty in tp2...
    firstorder; subst...
    eapply canonical_form_fun in tp3...
    firstorder; subst...
    left. econstructor...
    move=> h. inv h.
    left. econstructor...
    move=> h. inv h.
Qed.

Theorem weak_type_soundnes s s' :
  star step s s' ->
  forall t, [ [::] |- s :- t ] -> Stuck s' -> exists o, blame o s'.
Proof.
  move=> ss.
  dependent induction ss; intros.
  inv H0.
  apply progress in H.
  move: H => [ h1 | [ h2 | h3 ] ]; eauto.
  contradiction.
  contradiction.
  assert ([[::] |- ]).
  constructor.
  pose proof (star_step_subject_reduction ss H2 H0).
  pose proof (step_subject_reduction H2 H3 H).
  apply progress in H4.
  inv H1.
  move: H4 => [ h1 | [ h2 | h3 ] ].
  contradiction.
  contradiction.
  apply: h3.
Qed.
