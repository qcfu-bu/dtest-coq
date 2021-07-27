
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import astCast.
Require Import smallstepCast.

(* parallel reduction *)
(* using equalities to constrain substitution 
 * plays better with eauto tactic *)
(* is it possible to leave the direct substitution then 
 * prove the implication and add them as hints? or would 
 * that make things less clear? *)
Inductive pstep : term -> term -> Prop :=
| pstep_beta bod bod' a a' u:
  u = bod'.[Fun bod', a' /] ->
  pstep bod bod' ->
  pstep a a' ->
  pstep (App (Fun bod) a) u
| betaC a a' 
  trm trm' aty aty' aty1 aty1' bodty bodty' 
    bodty1 bodty1' u1 u2 o o' :
  let ac := Cast a' aty' aty1' (Aty o') in
  u1 = bodty1'.[ ac /] ->
  u2 = bodty'.[ a' /] ->
  pstep a a' ->
  pstep aty aty' ->
  pstep trm trm' ->
  pstep bodty bodty' ->
  pstep aty1 aty1' ->
  pstep bodty1 bodty1' ->
  pstep_path o o' ->
  pstep 
    (App (Cast trm (Pi aty1 bodty1) (Pi aty bodty) o) a) 
    (Cast (App trm' ac) u1 u2 (BodTy a' o')) 
| castTyu e e' o:
  pstep e e' ->
  pstep (Cast e TT TT o) e'
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_tt :
  pstep TT TT
| pstep_pi s1 s2 t1 t2 : 
  pstep s1 s2 ->
  pstep t1 t2 ->
  pstep (Pi s1 t1) (Pi s2 t2)
| pstep_fun bod bod' :
  pstep bod bod' ->
  pstep
    (Fun bod )
    (Fun bod')
| pstep_app f f' a a':
  pstep f f' ->
  pstep a a' ->
  pstep 
    (App f  a )
    (App f' a')
| pstep_castS e e' u u' t t' o o':
  pstep e e' ->
  pstep u u' ->
  pstep t t' ->
  pstep_path o o' ->
  pstep (Cast e u t o) (Cast e' u' t' o')

with pstep_path : path -> path -> Prop :=
| pstep_Here : pstep_path Here Here
| pstep_Aty p p' : 
  pstep_path p p' ->
  pstep_path (Aty p) (Aty p')
| pstep_BodTy s s' p p':
  pstep s s' ->
  pstep_path p p' ->
  pstep_path (BodTy s p) (BodTy s' p').

Scheme pstep_mutual := Induction for pstep Sort Prop
with pstep_path_mutual := Induction for pstep_path Sort Prop.

Notation red := (star pstep).
Notation "s === t" := (conv pstep s t) (at level 50).

Notation "s =o= t" := (conv pstep_path s t) (at level 50).

Definition psstep (sigma tau : var -> term) :=
  forall x, pstep (sigma x) (tau x).

Fixpoint maxpar (s : term) : term :=
  match s with
  | App (Fun bod) a => 
    (maxpar bod).[Fun (maxpar bod) , maxpar a /]
  | App (Cast trm (Pi aty1 bodty1) (Pi aty bodty) o) a =>
    let a' := 
      Cast (maxpar a) (maxpar aty) (maxpar aty1) 
        (Aty (maxpar_path o))  
    in 
    Cast 
      (App (maxpar trm) a') 
      ((maxpar bodty1).[a' /]) 
      ((maxpar bodty).[maxpar a /]) 
      (BodTy (maxpar a) (maxpar_path o))
  | Cast e TT TT _ => maxpar e
  | App f a => App (maxpar f) (maxpar a)
  | Fun bod =>  Fun (maxpar bod)
  | Pi aty bodty => Pi (maxpar aty) (maxpar bodty)
  | Cast e u t o => 
    Cast (maxpar e) (maxpar u) (maxpar t) (maxpar_path o)
  | TT => TT
  | Var x => Var x
  end

with maxpar_path (s : path) : path :=
  match s with
  | Here => Here
  | Aty o => Aty (maxpar_path o)
  | BodTy a o => BodTy (maxpar a) (maxpar_path o)
  end.

Lemma pstep_refl s : pstep s s.
Proof.
  eapply (@term_mutual 
    (fun p : path => 
      pstep_path p p /\
      forall s : term, pstep s s ->
      forall under : term, pstep under under ->
      forall over : term, pstep over over ->
      pstep (Cast s under over p) (Cast s under over p))   
    (fun s : term => pstep s s)); 
    firstorder; eauto using pstep, pstep_path.
Qed.
Hint Resolve pstep_refl.

Lemma psstep_refl s : psstep s s.
Proof. unfold psstep. move=> x; eauto. Qed.
Hint Resolve psstep_refl.

Lemma pstep_path_refl p : pstep_path p p.
Proof. elim p; eauto using pstep_path. Qed.
Hint Resolve pstep_path_refl.

Lemma step_pstep s t : step s t -> pstep s t.
Proof with eauto using pstep, pstep_path.
  elim...
  move=> f a A B A' B' o vf va.
  econstructor; eauto.
Qed.

Lemma pstep_subst sigma s t : 
  pstep s t -> pstep s.[sigma] t.[sigma].
Proof with eauto using pstep, pstep_path.
  move=> st.
  move: st sigma.
  apply: (@pstep_mutual 
    (fun (s t : term) (_ : pstep s t) => 
      forall sigma : var -> term, pstep s.[sigma] t.[sigma])
    (fun (p p' : path) (_ : pstep_path p p') => 
      forall sigma, 
        pstep_path p.[/sigma] p'.[/sigma]))...
  - move=> bod bod' a a' u -> _ h1 _ h2 sigma.
    apply: pstep_beta... 
    by autosubst.
  - move=> a a' trm trm' aty aty' aty1 aty1' 
      bodty bodty' bodty1 bodty1' u1 u2 o o' //=.
    move=> -> ->
      _ h1 _ h2 _ h3 _ h4 _ h5 _ h6 _ h7 sigma. 
    fold_all.
    apply: betaC...
    + autosubst.
    + autosubst.
Qed.

Lemma psstep_up sigma tau :
  psstep sigma tau -> psstep (up sigma) (up tau).
Proof.
  move=> A [|n] //=. asimpl. apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat sigma tau s t :
  psstep sigma tau -> pstep s t -> pstep s.[sigma] t.[tau].
Proof with eauto using pstep, psstep_up.
  move=> A B.
  move: sigma tau A.
  apply: (@pstep_mutual
    (fun (s t : term) (_ : pstep s t) => 
      forall (sigma tau : var -> term), 
        psstep sigma tau -> pstep s.[sigma] t.[tau]) 
    (fun (p q : path) (_ : pstep_path p q) => 
      forall (sigma tau : var -> term),
        psstep sigma tau -> pstep_path p.[/sigma] q.[/tau]))...
  - move=> bod bod' a a' u -> _ ih1 _ ih2 
      sigma tau h.
    apply: (@pstep_beta _ (bod'.[upn 2 tau]) _ (a'.[tau])); asimpl...
  - move=> a a' trm trm' aty aty' aty1 aty1' bodty bodty'
      bodty1 bodty1' u1 u2 o o' //=.
    move=> -> -> _ h1 _ h2 _ h3 _ h4 _ h5 _ h6 _ h7 
      sigma tau h8. 
    fold_all.
    apply: (@betaC 
      _ (a'.[tau]) 
      _ (trm'.[tau]) 
      _ (aty'.[tau]) 
      _ (aty1'.[tau])
      _ (bodty'.[up tau])
      _ (bodty1'.[up tau])); asimpl...
  - move=> e e' u u' t0 t' o o' _ h1 _ h2 _ h3 _ h4 
      sigma tau h8 => //=.
    fold_all.
    econstructor...
  - move=> p p' _ h1 sigma tau h2 => //=.
    econstructor...
  - move=> s0 s' p p' _ h1 _ h2 sigma tau h3 => //=.
    fold_all.
    econstructor...
Qed.

Lemma psstep_compat s1 s2 sigma tau:
  psstep sigma tau -> pstep s1 s2 -> psstep (s1 .: sigma) (s2 .: tau).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_compat_beta s1 s2 t1 t2 u1 u2:
  pstep s1 s2 -> pstep t1 t2 -> pstep u1 u2 ->
  pstep s1.[t1,u1/] s2.[t2,u2/].
Proof.
  move=> A B C.
  apply: pstep_compat A.
  apply: psstep_compat B.
  by apply: psstep_compat C.
Qed.


Lemma rho_triangle : triangle pstep maxpar.
Proof with eauto using pstep, pstep_path.
  move=> s t. 
  apply: (@pstep_mutual
    (fun (s t : term) (_ : pstep s t) => 
      pstep t (maxpar s))
    (fun (p q : path) (_ : pstep_path p q) => 
      pstep_path q (maxpar_path p)))...
  - move=> bod bod' a a' u -> _ A _ B.
    apply: pstep_compat_beta...
  - move=> a a' trm trm' aty aty' aty1 aty1' 
      bodty bodty' bodty1 bodty1' u u' o o' => //=.
    move=> -> -> _ h1 _ h2 _ h3 _ h4 _ h5 _ h6 _ h7.
    repeat constructor...
    apply: pstep_compat h6.
    apply: psstep_compat...
    apply: pstep_compat h4. 
    by apply: psstep_compat h1.
  - move=> f f' a a' h1 ih1 h2 ih2. case: f h1 ih1 => //=...
    move=> s0 h ih. inv h. inv ih...
    move=> s0 under over ih1. case: under ih1 => //=...
    move=> s1 t0 h1 ih1. case: over h1 ih1 => //=...
    move=> s2 t1 h ih1 ih3. inv ih1. inv ih3. 
    + inv H5.
    + inv H5. inv H6. inv H12. inv H13...
  - move=> e e' u u' t0 t' h1 ih1 h2 ih2 h3 ih3 h4 ih4 h5 ih5. 
    case: u h3 ih3 => //=...
    move=> h h'. inv h. case: t0 h4 ih4 => //=...
    move=> h h''. inv h...
Qed.

Theorem church_rosser :
  CR pstep.
Proof.
  apply: (cr_method (e2 := pstep) (rho := maxpar)).
  trivial. exact: star1. exact: rho_triangle.
Qed.
Hint Resolve church_rosser.

(* conversion *)

Definition sconv (sigma tau : var -> term) :=
  forall x, sigma x === tau x.

Lemma conv_app s1 s2 t1 t2 :
  s1 === s2 -> t1 === t2 -> App s1 t1 === App s2 t2.
Proof.
  move=> A B. apply: (conv_trans (App s2 t1)).
  - apply: (conv_hom (App^~ t1)) A => x y H; by apply: pstep_app.
  - apply: (conv_hom) B => x y H; by apply: pstep_app.
Qed.

Lemma conv_fun s1 s2 : s1 === s2 -> Fun s1 === Fun s2.
Proof. apply: conv_hom => x y. exact: pstep_fun. Qed.

Lemma conv_pi s1 s2 t1 t2 :
  s1 === s2 -> t1 === t2 -> Pi s1 t1 === Pi s2 t2.
Proof.
  move=> A B. apply: (conv_trans (Pi s2 t1)).
  - apply: (conv_hom (Pi^~ t1)) A => x y H; by apply : pstep_pi.
  - apply: conv_hom B => x y H; by apply: pstep_pi.
Qed.

Lemma conv_cast e e' u u' t t' o o' :
  e === e' -> 
  u === u' -> 
  t === t' -> 
  o =o= o' -> 
  Cast e u t o === Cast e' u' t' o'.
Proof.
  move=> A B C D. 
  apply: (conv_trans (Cast e' u t o)).
  apply: (conv_hom (fun e => Cast e u t o)) A => x y H; 
    by econstructor.
  apply: (conv_trans (Cast e' u' t o)).
  apply: (conv_hom (fun u => Cast e' u t o)) B => x y H; 
    by econstructor.
  apply: (conv_trans (Cast e' u' t' o)).
  apply: (conv_hom (fun t => Cast e' u' t o)) C => x y H; 
    by econstructor.
  apply: (conv_hom (fun o => Cast e' u' t' o)) D => x y H;
    by econstructor.
Qed.

Lemma conv_aty p p' :
  p =o= p' ->
  Aty p =o= Aty p'.
Proof.
  move=> A.
  apply: (conv_hom (fun p => Aty p)) A => x y H;
    by econstructor.
Qed.

Lemma conv_bodty t t' p p' :
  t === t' ->
  p =o= p' ->
  (BodTy t p) =o= (BodTy t' p').
Proof.
  move=> A B.
  apply: (conv_trans (BodTy t' p)).
  apply: (conv_hom (fun t => BodTy t p)) A => x y H;
    by econstructor.
  apply: (conv_hom (fun p => BodTy t' p)) B => x y H;
    by econstructor.
Qed.

Lemma conv_subst sigma s t : s === t -> s.[sigma] === t.[sigma].
Proof. apply: conv_hom. exact: pstep_subst. Qed.

Lemma sconv_up sigma tau : sconv sigma tau -> sconv (up sigma) (up tau).
Proof. move=> A [|x] //=. asimpl. exact: conv_subst. Qed.

Lemma conv_compat sigma tau s :
  sconv sigma tau -> s.[sigma] === s.[tau].
Proof with eauto 6 using 
  conv_app, conv_fun, conv_pi, conv_cast,
  conv_aty, conv_bodty, sconv_up.
  move: sigma tau.
  apply: (@term_mutual
    (fun (p : path) => 
      forall sigma tau, 
        sconv sigma tau -> p.[/sigma] =o= p.[/tau])
    (fun (s : term) => 
      forall sigma tau,
        sconv sigma tau -> s.[sigma] === s.[tau]))...
Qed.

Lemma conv_beta s1 s2 t1 t2 : s1 === s2 -> t1 === t2 -> s1.[t1/] === s2.[t2/].
Proof. 
  move=> c1 c2. 
  apply: conv_trans. 
  apply: conv_subst.
  apply: c1.
  by apply: conv_compat => -[]. 
Qed.

(* reduction behavior *)

Inductive RedPiSpec A1 B1 : term -> Prop :=
| RedPiSpecI A2 B2 : red A1 A2 -> red B1 B2 -> RedPiSpec A1 B1 (Pi A2 B2).

Lemma red_pi_inv A1 B1 C :
  red (Pi A1 B1) C -> RedPiSpec A1 B1 C.
Proof.
  elim=> {C} [|C D _ [A2 B2]].
  - by constructor.
  - move=> ra12 rb12 st. inv st; constructor; eauto using star.
Qed.

Lemma red_tt_inv A :
  red TT A -> A = TT.
Proof. elim=> [] //. move=> y z _ -> H. by inv H. Qed.

Lemma red_fun_inv A s :
  red (Fun s) A -> exists s', A = Fun s'.
Proof. 
  elim=> [] //. 
  exists s => //.
  move=> y z _ x H. 
  firstorder. 
  subst.
  inv H.
  exists bod' => //.
Qed.

Lemma inj_pi A1 A2 B1 B2 :
  Pi A1 B1 === Pi A2 B2 -> A1 === A2 /\ B1 === B2.
Proof.
  move=>/church_rosser[z /red_pi_inv s1 /red_pi_inv s2].
  inv s1; inv s2; split; eauto using join_conv.
Qed.

Lemma conv_pi_tt A B :
  ~(Pi A B === TT).
Proof.
  move=> /church_rosser[z /red_pi_inv s1 s2].
  inv s1; inv s2; apply red_tt_inv in H1.
  rewrite H1 in H2; inv H2.
Qed.

Lemma conv_pi_fun A B s :
  ~(Pi A B === Fun s).
Proof. 
  move=> /church_rosser[z /red_pi_inv s1 s2].
  inv s1; inv s2. 
  apply red_fun_inv in H1. 
  firstorder. 
  subst.
  inv H2.
Qed.

Lemma conv_refl s : s === s.
Proof. eauto. Qed.

Lemma conv_sym s t : s === t -> t === s.
Proof. apply: conv_sym. Qed.

Lemma conv_trans x y z : x === y -> y === z -> x === z.
Proof. apply: conv_trans. Qed.

Add Relation term (conv pstep)
  reflexivity proved by conv_refl
  symmetry proved by conv_sym
  transitivity proved by conv_trans
  as conv_setoid.