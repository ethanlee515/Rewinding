From Stdlib Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop order algebra.
From mathcomp Require Import reals realsum functions numfun distr arithmetic_tactic.

Import GRing.Theory Num.Theory Order.Theory.
Open Scope ring_scope.
Set SsrOldRewriteGoalsOrder.

Section Bounds.
Context {R : realType}.

Lemma expect_add_pos {T : choiceType} (D : {distr T / R}) (f g : T -> R) :
  (forall x, 0 <= f x) -> (forall x, 0 <= g x) ->
  \E?_[D] f -> \E?_[D] g ->
  \E_[D] (fun x => f x + g x) = \E_[D] f + \E_[D] g.
Proof.
move=> f0 g0 sf sg.
have F0 x : 0 <= f x * D x by rewrite mulr_ge0.
have G0 x : 0 <= g x * D x by rewrite mulr_ge0.
rewrite /esp -[in RHS](psum_sum F0) -[in RHS](psum_sum G0).
rewrite -(psumD F0 G0 sf sg) psum_sum; last by move=> x; rewrite /= addr_ge0.
by apply eq_sum => x /=; rewrite mulrDl.
Qed.

Context {T : choiceType} (D : {distr T / R}).

Local Lemma int_interval f (M : R) :
  (forall x : T, 0 <= f x /\ f x <= M) -> \E?_[D] f.
Proof.
move=> H; apply: bounded_has_exp; exists M => x.
by have [Hx HM] := H x; rewrite ger0_norm.
Qed.

(** [a] and [b] are the probabilities of two successful openings
    conditional on the checkpoint. *)
Lemma two_openings (a b : T -> R) :
  (forall x, 0 <= a x /\ a x <= 1) ->
  (forall x, 0 <= b x /\ b x <= 1) ->
  \E_[D] a + \E_[D] b <= 1 + \E_[D] (fun x => a x * b x).
Proof.
move=> Ha Hb.
have ab x : 0 <= a x * b x /\ a x * b x <= 1.
  have [a0 a1] := Ha x; have [b0 b1] := Hb x.
  split; first exact: mulr_ge0.
  rewrite -[leRHS](mulr1 1); exact: ler_pM.
have H : \E_[D] (fun x => a x + b x) <= \E_[D] (fun x => 1 + a x * b x).
  apply: le_exp.
  - apply: (int_interval _ 2) => x; have [? ?] := Ha x; have [? ?] := Hb x; split; lra.
  - apply: (int_interval _ 2) => x; have [? ?] := ab x; split; lra.
  - move=> x; have [_ H1] := Ha x; have [_ H2] := Hb x.
    have Hprod : 0 <= (1-a x)*(1-b x) by rewrite mulr_ge0 // subr_ge0.
    nra.
rewrite (expect_add_pos D a b (fun x => (proj1 (Ha x))) (fun x => (proj1 (Hb x))) (int_interval _ 1 Ha) (int_interval _ 1 Hb)) in H.
rewrite (expect_add_pos D (fun _ => 1) (fun x => a x * b x) (fun _ => ler01) (fun x => (proj1 (ab x))) (has_exp1 D) (int_interval _ 1 ab)) in H.
rewrite exp_cst mulr1 in H.
have Hmass := le1_pr predT D.
lra.
Qed.

(** The mass missing from a subdistribution contributes zero success. *)
Lemma square_checkpoint (f : T -> R) :
  (forall x, 0 <= f x /\ f x <= 1) ->
  (\E_[D] f)^2 <= \E_[D] (fun x => (f x)^2).
Proof.
move=> Hf.
pose p := \E_[D] f.
have p0 : 0 <= p.
  rewrite /p -[leLHS](exp0 D); apply: le_exp; try exact: has_exp0; try exact: (int_interval _ 1 Hf).
  by move=> x; case: (Hf x).
have p1 : p <= 1.
  apply: exp_le_bd => // x; have [f0 f1] := Hf x; by rewrite ger0_norm.
have fsq x : 0 <= (f x)^2 /\ (f x)^2 <= 1.
  have [f0 f1] := Hf x; split; first exact: sqr_ge0.
  nra.
have H : \E_[D] (fun x => (2 * p) * f x) <= \E_[D] (fun x => (f x)^2 + p^2).
  apply: le_exp.
  - apply: (int_interval _ 2) => x; have [? ?] := Hf x; split; nra.
  - apply: (int_interval _ 2) => x; have [? ?] := fsq x; split; nra.
  - move=> x; have := sqr_ge0 (f x - p); nra.
rewrite (expect_add_pos D (fun x => (f x)^2) (fun _ => p^2) (fun x => (proj1 (fsq x))) (fun _ => sqr_ge0 p) (int_interval _ 1 fsq) (has_expC D _)) in H.
rewrite (expZ D f (2 * p)) in H.
rewrite exp_cst -/p in H.
have Hmass := le1_pr predT D.
have Hscale : \P_[D] predT * p^2 <= 1 * p^2 by apply: ler_wpM2r; [exact: sqr_ge0 | exact: Hmass].
change (p^2 <= \E_[D] (fun x => (f x)^2)).
nra.
Qed.
End Bounds.
