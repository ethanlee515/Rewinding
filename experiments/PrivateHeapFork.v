From Stdlib Require Import Unicode.Utf8.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice ssrnat distr reals.
From extructures Require Import ord fset fmap.
From SSProve Require Import NominalPrelude.
From SSProve.Crypt.nominal Require Import Pr.
From SSProve.Crypt Require Import Axioms SubDistr Casts.
Set SsrOldRewriteGoalsOrder.
Import PackageNotation pkg_heap.
Open Scope package_scope.

(** Run the code's reads and writes against an explicit heap value. *)
Fixpoint privatize {A : choiceType} (c : raw_code A) (h : heap) :
    raw_code (prod_choiceType A heap) :=
  match c with
  | ret x => ret (x,h)
  | opr o x k => opr o x (fun y => privatize (k y) h)
  | getr l k => privatize (k (get_heap h l)) h
  | putr l v k => privatize k (set_heap h l v)
  | sampler op k => sampler op (fun y => privatize (k y) h)
  end.

(** For linked, closed code, the result and private heap agree with the
    ordinary semantics. This uses [Pr_code_call], which gives an unresolved
    call zero mass. Live external calls need a separate linking theorem. *)
Lemma privatize_sound (A : choiceType) (c : raw_code A) h external_heap :
  Pr_code (privatize c h) external_heap =
  \dlet_(z <- Pr_code c h) dunit (z, external_heap).
Proof.
elim: c h => [x|o x k IH|l k IH|l v k IH|op k IH] h /=.
- by rewrite !Pr_code_ret dlet_unit_ext.
- by rewrite !Pr_code_call dlet_null_ext.
- by rewrite Pr_code_get.
- by rewrite Pr_code_put.
- rewrite !Pr_code_sample dlet_dlet_ext.
  apply eq_dlet => y. exact: (IH y h).
Qed.

Lemma privatize_valid (A : choiceType) (c : raw_code A) L I h :
  valid_code L I c -> valid_code emptym I (privatize c h).
Proof.
move=> H.
elim: H h => [x|o x k Ho Hk IH|l k Hl Hk IH|l v k Hl Hk IH|op k Hk IH] h /=.
- by constructor.
- by constructor.
- by apply: IH.
- by apply: IH.
- by constructor.
Qed.

Lemma privatize_bind (A B : choiceType) (c : raw_code A) h external_heap
    (k : prod_choiceType A heap -> raw_code B) :
  Pr_code (v ← privatize c h ;; k v) external_heap =
  \dlet_(z <- Pr_code c h) Pr_code (k z) external_heap.
Proof.
rewrite Pr_code_bind privatize_sound dlet_dlet_ext.
apply eq_dlet => z. by rewrite dlet_unit_ext.
Qed.

(** Run initialization once, then run both branches from its private heap. *)
Definition fork_after {X U V : choiceType} (init : raw_code X)
    (left : X -> raw_code U) (right : X -> raw_code V) initial_heap :
    raw_code (prod_choiceType X (prod_choiceType U V)) :=
  z ← privatize init initial_heap ;;
  u ← privatize (left z.1) z.2 ;;
  v ← privatize (right z.1) z.2 ;;
  ret (z.1,(u.1,v.1)).

Lemma fork_after_sound {X U V : choiceType} (init : raw_code X)
    (left : X -> raw_code U) (right : X -> raw_code V) hi he :
  Pr_code (fork_after init left right hi) he =
  \dlet_(z <- Pr_code init hi)
  \dlet_(u <- Pr_code (left z.1) z.2)
  \dlet_(v <- Pr_code (right z.1) z.2)
    dunit ((z.1,(u.1,v.1)),he).
Proof.
rewrite /fork_after privatize_bind. apply eq_dlet => z.
rewrite privatize_bind. apply eq_dlet => u.
rewrite privatize_bind. apply eq_dlet => v.
by rewrite Pr_code_ret.
Qed.


Lemma fork_after_valid {X U V : choiceType} (init : raw_code X)
    (left : X -> raw_code U) (right : X -> raw_code V) hi L I :
    ValidCode L I init ->
    (forall x, ValidCode L I (left x)) ->
    (forall x, ValidCode L I (right x)) ->
    ValidCode emptym I (fork_after init left right hi).
Proof.
move=> H0 H1 H2. rewrite /fork_after.
apply valid_bind; first exact: privatize_valid H0.
move=> z. apply valid_bind; first exact: privatize_valid (H1 _).
move=> u. apply valid_bind; first exact: privatize_valid (H2 _).
move=> v. by constructor.
Qed.
