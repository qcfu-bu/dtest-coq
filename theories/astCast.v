
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun.
Require Import AutosubstSsr ARS Context.
Require Import Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive path : Type  := (* mutually inductive? *)
| Here
| Aty : path -> path
| BodTy : term -> path -> path

with term : Type :=
| Var (x : var)
| TT
| App (s t : term)
| Fun (s : {bind 2 of term})
| Pi (s : term) (t : {bind term})
| Cast (s under over : term) (p : path).

Scheme path_mutual := Induction for path Sort Type
with term_mutual := Induction for term Sort Type.

Definition ids_term (v : var) : term := Var v.

Instance Ids_term : Ids term. 
  unfold Ids.
  apply ids_term.
Defined.

Fixpoint rename_term (re : var -> var) (t : term) : term :=
  match t with
  | Var x => Var (re x)
  | TT => TT
  | App s t => App (rename_term re s) (rename_term re t)
  | Fun s => Fun (rename_term (iterate upren 2 re) s)
  | Pi s t => Pi (rename_term re s) (rename_term (upren re) t)
  | Cast s under over p => 
    let s := rename_term re s in
    let under := rename_term re under in
    let over := rename_term re over in
    let p := rename_path re p in
    Cast s under over p
  end

with rename_path (re : var -> var) (p : path) : path :=
  match p with
  | Here => Here
  | Aty p => Aty (rename_path re p)
  | BodTy t p =>
    let t := rename_term re t in
    let p := rename_path re p in
    BodTy t p
  end.

Instance Rename_term : Rename term. 
  unfold Rename.
  apply rename_term.
Defined.

Fixpoint subst_term (sigma : var -> term) (s : term) : term :=
  match s as t return (annot term t) with
  | Var x => sigma x
  | TT => TT
  | App s1 s2 => App (subst_term sigma s1) (subst_term sigma s2)
  | Fun s0 => Fun (subst_term (upn 2 sigma) s0)
  | Pi s0 t => Pi (subst_term sigma s0) (subst_term (up sigma) t)
  | Cast s1 s2 s3 p =>
    let s1 := subst_term sigma s1 in
    let s2 := subst_term sigma s2 in
    let s3 := subst_term sigma s3 in
    let p := subst_path sigma p in
    Cast s1 s2 s3 p
  end

with subst_path (sigma : var -> term) (p : path) : path :=
  match p as t return (annot path p) with
  | Here => Here
  | Aty p => Aty (subst_path sigma p)
  | BodTy t p => 
    let t := subst_term sigma t in
    let p := subst_path sigma p in
    BodTy t p
  end.

Instance Subst_term : Subst term. 
  unfold Subst.
  apply subst_term.
Defined.

Lemma rename_subst : forall xi s, 
  rename xi s = s.[ren xi].
Proof.
  assert (up_upren : forall xi, up (ren xi) = ren (upren xi)) 
    by (apply up_upren_internal; reflexivity).
  assert (up_upren_n : forall xi n, upn n (ren xi) = 
    ren (iterate upren n xi)) by (apply up_upren_n_internal, up_upren).
  move=> xi s. move: s xi.
  apply (@term_mutual 
    (fun p : path => forall (xi : var -> var), 
      rename_path xi p = subst_path (ren xi) p)
    (fun s : term => forall (xi : var -> var), 
      rename xi s = s.[ren xi]));
  asimpl; eauto.
  - move=> p ih xi; apply f_equal; eauto.
  - move=> t ih1 p ih2 xi.
    pose proof (ih1 xi).
    unfold rename in H. unfold Rename_term in H.
    rewrite H ih2; asimpl=> //=.
  - move=> s ih1 t ih2 xi.
    rewrite ih1 ih2=> //=.
  - move=> s ih1 xi; apply f_equal.
    rewrite ?up_upren ?up_upren_n; apply ih1.
  - move=> s ih1 t ih2 xi.
    rewrite ih1 ih2.
    rewrite ?up_upren ?up_upren_n.
    reflexivity.
  - move=> s ih1 under ih2 over ih3 p ihp xi.
    rewrite ih1 ih2 ih3; apply f_equal.
    case: p ihp xi; eauto.
Qed.

Lemma subst_id : forall s, s.[ids] = s.
Proof.
  assert (up_id : up ids = ids) by
    (apply up_id_internal; reflexivity).
  assert (up_id_n : forall n, upn n ids = ids) by
    (apply up_id_n_internal, up_id).
  apply (@term_mutual 
    (fun p : path => subst_path ids p = p)
    (fun s : term => s.[ids] = s)); 
  asimpl; eauto.
  - move=> p -> => //.
  - move=> t ih1 p ih2.
    rewrite ih2.
    unfold subst in ih1. unfold Subst_term in ih1.
    rewrite ih1 => //.
  - move=> s ih1 t ih2.
    rewrite ih1 ih2 => //.
  - move=> s ih.
    rewrite ?up_id ?up_id_n.
    rewrite ih => //.
  - move=> s ih1 t ih2.
    rewrite ?up_id ?up_id_n.
    rewrite ih1 ih2 => //.
  - move=> s ih1 under ih2 over ih3 p ihp.
    rewrite ih1 ih2 ih3; apply f_equal.
    case: p ihp; eauto.
Qed.

Lemma ren_subst_comp : forall xi sigma s, 
  (rename xi s).[sigma] = s.[xi >>> sigma].
Proof.
  move=> xi sigma s; move: s xi sigma.
  apply (@term_mutual 
    (fun p : path => forall xi sigma, 
      subst_path sigma (rename_path xi p) = 
      subst_path (xi >>> sigma) p)
    (fun s : term => forall xi sigma, 
      (rename xi s).[sigma] = s.[xi >>> sigma])); 
  asimpl; eauto.
  - move=> p ih xi sigma; apply f_equal.
    apply ih.
  - move=> t ih1 p ih2 xi sigma.
    pose proof (ih1 xi sigma).
    unfold subst in H. unfold Subst_term in H.
    unfold rename in H. unfold Rename_term in H.
    rewrite H ih2 => //.
  - move=> s ih1 t ih2 xi sigma.
    rewrite ih1 ih2 => //.
  - move=> s ih xi sigma.
    rewrite up_comp_ren_subst_n.
    rewrite ih => //.
  - move=> s ih1 t ih2 xi sigma.
    rewrite up_comp_ren_subst.
    rewrite ih1 ih2 => //.
  - move=> s ih1 under ih2 over ih3 p ihp xi sigma.
    rewrite ih1 ih2 ih3; apply f_equal.
    case: p ihp xi sigma; eauto.
Qed.

Lemma subst_ren_comp : forall sigma xi s,
  rename xi s.[sigma] = s.[sigma >>> rename xi].
Proof.
  move=> sigma xi s; move: s sigma xi.
  assert (up_comp_subst_ren : forall sigma xi, 
    up (sigma >>> rename xi) = up sigma >>>rename (upren xi))
    by (apply up_comp_subst_ren_internal; [reflexivity|
      apply rename_subst| apply ren_subst_comp]).
  assert (up_comp_subst_ren_n : forall sigma xi n, 
    upn n (sigma >>> rename xi) = 
    upn n sigma >>> rename (iterate upren n xi))
    by (apply up_comp_subst_ren_n_internal; 
      apply up_comp_subst_ren).
  apply (@term_mutual 
    (fun p => forall xi sigma,
      rename_path xi (subst_path sigma p) = 
      subst_path (sigma >>> rename xi) p)
    (fun s => forall sigma xi, 
      rename xi s.[sigma] = s.[sigma >>> rename xi]));
  asimpl; eauto.
  - move=> p ih xi sigma; apply f_equal.
    apply ih.
  - move=> t ih1 p ih2 xi sigma.
    pose proof (ih1 sigma xi).
    unfold subst in H. unfold Subst_term in H.
    unfold rename in H. unfold Rename_term in H.
    rewrite H ih2 => //.
  - move=> s ih1 t ih2 sigma xi.
    rewrite ih1 ih2 => //.
  - move=> s ih sigma xi; apply f_equal.
    rewrite up_comp_subst_ren_n.
    apply ih.
  - move=> s ih1 t ih2 sigma xi.
    rewrite up_comp_subst_ren.
    rewrite ih1 ih2 => //.
  - move=> s ih1 under ih2 over ih3 p ihp sigma xi.
    rewrite ih1 ih2 ih3; apply f_equal.
    case: p ihp xi sigma; eauto.
Qed.

Lemma subst_comp : forall (sigma tau : var -> term) (s : term),
  s.[sigma].[tau] = s.[sigma >> tau].
Proof.
  move=> sigma tau s; move: s sigma tau.
  assert (up_comp : forall sigma tau, 
    up (sigma >> tau) = up sigma >> up tau)
    by (apply up_comp_internal; 
      [reflexivity|apply ren_subst_comp|apply subst_ren_comp]).
  assert (up_comp_n : forall sigma tau n, 
    upn n (sigma >> tau) = upn n sigma >> upn n tau)
    by (apply up_comp_n_internal; apply up_comp).
  apply (@term_mutual
    (fun p => forall sigma tau, 
      subst_path tau (subst_path sigma p) = 
      subst_path (sigma >> tau) p)
    (fun s => forall sigma tau,
      s.[sigma].[tau] = s.[sigma >> tau]));
  asimpl; eauto.
  - move=> p ih sigma tau; apply f_equal.
    apply ih.
  - move=> t ih1 p ih2 sigma tau.
    pose proof (ih1 sigma tau).
    unfold subst in H. unfold Subst_term in H.
    rewrite H ih2 => //.
  - move=> s ih1 t ih2 sigma tau.
    rewrite ih1 ih2 => //.
  - move=> s ih sigma tau; apply f_equal.
    rewrite up_comp_n.
    apply ih.
  - move=> s ih1 t ih2 sigma tau.
    rewrite up_comp.
    rewrite ih1 ih2 => //.
  - move=> s ih1 under ih2 over ih3 p ihp sigma tau.
    rewrite ih1 ih2 ih3; apply f_equal.
    case: p ihp sigma tau; eauto.
Qed.

Instance substLemmas_term : SubstLemmas term.
  constructor.
  - apply rename_subst.
  - apply subst_id.
  - reflexivity.
  - apply subst_comp.
Qed.

Notation "p .[/ sigma ]" := (subst_path sigma p)
  (at level 2, sigma at level 200, left associativity,
    format "p .[/ sigma ]") : subst_scope.

(* remove cast information, helpful for some technical lemmas *)
Fixpoint erase (e : term) : term :=
match e with
| Var x        => Var x
| TT           => TT
| App f a      => App (erase f) (erase a)
| Fun b        => Fun (erase b)
| Pi a b       => Pi (erase a) (erase b)
| Cast e _ _ _ => erase e
end.

(* helper tactic *)
Ltac fold_all :=
  fold subst_term;
  fold subst_path;
  fold Subst_term;
  fold subst.