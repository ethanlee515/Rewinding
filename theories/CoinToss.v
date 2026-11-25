From mathcomp Require Import ssreflect choice distr.
From SSProve Require Import NominalPrelude.
From Mending.NextMessage Require Import Trace.

Section CoinToss.

Context {Request Result : choice_type}.
Variable challenge_id : ident.
Variable committer : raw_code Result.
Variable oracles : raw_package.

(** Model the committer as code that sends its commitment, then calls
    [challenge_id] to receive the other party's bit. *)
Definition run_to_challenge := run_until_next_call committer challenge_id.

(** The trace identifies the pending challenge call. The heap must come from
    the same execution that produced the trace. This record only checks the
    trace. A later prefix lemma should establish the relationship. *)
Record checkpoint := {
  saved_trace : trace_t;
  saved_heap : heap;
  challenge_request : Request;
  opening_code : chBool -> raw_code Result;
  at_challenge : continue_from_trace committer saved_trace =
    Some (opr (mkopsig challenge_id Request chBool)
      challenge_request opening_code)
}.

Definition run_opening (point : checkpoint) (challenge : chBool) :=
  Pr_code
    (code_link (continue_after_call committer (saved_trace point) challenge) oracles)
    (saved_heap point).

Lemma run_openingE (point : checkpoint) (challenge : chBool) :
  run_opening point challenge =
  Pr_code (code_link (opening_code point challenge) oracles) (saved_heap point).
Proof.
  by rewrite /run_opening (@continue_after_call_at_trace Request chBool Result
    challenge_id committer (saved_trace point) (challenge_request point)
    (opening_code point) challenge (at_challenge point)).
Qed.

(** Each branch starts from [saved_heap point] and samples independently.
    Each result includes the final heap of its own branch. *)
Definition fork_openings (point : checkpoint) :=
  \dlet_(left <- run_opening point false)
  \dlet_(right <- run_opening point true)
  dunit (left, right).

Lemma fork_openingsE (point : checkpoint) :
  fork_openings point =
  \dlet_(left <- Pr_code (code_link (opening_code point false) oracles) (saved_heap point))
  \dlet_(right <- Pr_code (code_link (opening_code point true) oracles) (saved_heap point))
  dunit (left, right).
Proof. by rewrite /fork_openings !run_openingE. Qed.

(** Next, derive the checkpoint from a run of [run_to_challenge] and prove
    that supplying one challenge recovers the original linked game. Then
    construct the binding adversary as a valid package and show that its two
    opening attempts have the joint law [fork_openings]. *)

End CoinToss.
