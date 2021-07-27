
(* TODO better named conversion? *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import ast.
Require Import smallstep.


(* parallel reduction *)

Inductive pstep : term -> term -> Prop :=
| pstep_beta s1 s2 t1 t2 u :
  u = s2.[Fun s2,t2/] ->
  pstep s1 s2 ->
  pstep t1 t2 ->
  pstep (App (Fun s1) t1) u
| pstep_castR s1 s2 t :
  pstep s1 s2 ->
  pstep (Cast s1 t) s2
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_tt :
  pstep TT TT
| pstep_pi s1 s2 t1 t2 : 
  pstep s1 s2 ->
  pstep t1 t2 ->
  pstep (Pi s1 t1) (Pi s2 t2)
| pstep_fun s1 s2 :
  pstep s1 s2 ->
  pstep (Fun s1) (Fun s2)
| pstep_app s1 s2 t1 t2 :
  pstep s1 s2 ->
  pstep t1 t2 ->
  pstep (App s1 t1) (App s2 t2)
| pstep_castS s1 s2 t1 t2 :
  pstep s1 s2 ->
  pstep t1 t2 ->
  pstep (Cast s1 t1) (Cast s2 t2).

Notation red := (star pstep).
Notation "s === t" := (conv pstep s t) (at level 50).

(* every ground type should satisfy the lemmas (at least if I could tuple things together) but the prop type destinction pobly handles that already
Instance Ids_pstep : Ids pstep . derive. Defined.
...
*)

(* TODO rename?*)
Definition psstep (sigma tau : var -> term) :=
  forall x, pstep (sigma x) (tau x).

Fixpoint maxpar (s : term) : term :=
  match s with
  | App (Fun s) t => (maxpar s).[Fun (maxpar s),maxpar t/]
  | App s t => App (maxpar s) (maxpar t)
  | Fun s => Fun (maxpar s)
  | Pi A B => Pi (maxpar A) (maxpar B)
  | Cast s t => (maxpar s)
  | x => x
  end.

Lemma pstep_refl s : pstep s s.
Proof. elim: s; eauto using pstep. Qed.
Hint Resolve pstep_refl.

Lemma step_pstep s t : step s t -> pstep s t.
Proof. elim; eauto using pstep. Qed.

Lemma pstep_subst sigma s t : pstep s t -> pstep s.[sigma] t.[sigma].
Proof.
  move=> st. elim: st sigma => /={s t}; eauto using pstep.
  move=> s1 s2 t1 t2 u -> _ A _ B sigma.
  apply: pstep_beta; eauto. by autosubst.
Qed.

Lemma psstep_up sigma tau :
  psstep sigma tau -> psstep (up sigma) (up tau).
Proof.
  move=> A [|n] //=. asimpl. apply: pstep_subst. exact: A.
Qed.

Lemma pstep_compat sigma tau s t :
  psstep sigma tau -> pstep s t -> pstep s.[sigma] t.[tau].
Proof with eauto using pstep, psstep_up.
  move=> A B. elim: B sigma tau A; asimpl...
  move=> s1 s2 t1 t2 u -> _ A _ B sigma tau C.
  apply: (@pstep_beta _ (s2.[upn 2 tau]) _ (t2.[tau])); asimpl...
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

Lemma maxpar_triangle : triangle pstep maxpar.
Proof with eauto using pstep.
  move=> s t. elim=> {s t} //=...
  - move=> s1 s2 t1 t2 u -> {u} _ A _ B.
    apply: pstep_compat_beta; eauto...
  - move=> s1 s2 t1 t2 A ih1 _ ih2. case: s1 A ih1 => //=...
    move=> s A ih1. inv A. inv ih1...
Qed.

Theorem church_rosser :
  CR pstep.
Proof.
  apply: (cr_method (e2 := pstep) (rho := maxpar)).
  trivial. exact: star1. exact: maxpar_triangle.
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

Lemma conv_cast s1 s2 t1 t2 :
  s1 === s2 -> t1 === t2 -> Cast s1 t1 === Cast s2 t2.
Proof.
  move=> A B. apply: (conv_trans (Cast s2 t1)).
  - apply: (conv_hom (Cast^~ t1)) A => x y H; by apply : pstep_castS.
  - apply: conv_hom B => x y H; by apply: pstep_castS.
Qed.

Lemma conv_subst sigma s t : s === t -> s.[sigma] === t.[sigma].
Proof. apply: conv_hom. exact: pstep_subst. Qed.

Lemma sconv_up sigma tau : sconv sigma tau -> sconv (up sigma) (up tau).
Proof. move=> A [|x] //=. asimpl. exact: conv_subst. Qed.

Lemma conv_compat sigma tau s :
  sconv sigma tau -> s.[sigma] === s.[tau].
Proof.
  elim: s sigma tau => *; asimpl; eauto using
    conv_app, conv_fun, conv_pi, conv_cast, sconv_up.
Qed.

Lemma conv_beta s t1 t2 : t1 === t2 -> s.[t1/] === s.[t2/].
Proof. move=> c. by apply: conv_compat => -[]. Qed.

(* reduction behavior *)

Inductive RedPiSpec A1 B1 : term -> Prop :=
| RedPiSpecI A2 B2 : 
  red A1 A2 -> 
  red B1 B2 -> 
  RedPiSpec A1 B1 (Pi A2 B2).

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

