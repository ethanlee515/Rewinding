# SSProve rewinding experiments

Recovered from the November 24, 2026 Astra session. The two Rocq experiments
are [PrivateHeapFork.v](../experiments/PrivateHeapFork.v) and
[CheckpointBounds.v](../experiments/CheckpointBounds.v).

## Forking at a procedure boundary

For the coin-toss game, the checkpoint is just after `commit` returns. Keep
the commitment and the heap from that run, then call `open` twice from that
heap. Interactive Schnorr extraction has the same shape. SSProve already
exposes the joint subdistribution of a return value and final heap through
`Pr_code`, so `Pr_code_bind` gives the checkpoint distribution directly.
This supplies the probability semantics that Firsov and Unruh obtain by
reflection in EasyCrypt. [Reflection, Rewinding, and Coin-Toss in EasyCrypt, §§1.4 and 3–5](../background-literature/2021-1078.pdf)

`privatize` transforms `raw_code` so its reads and writes use an explicit
heap value. Sampling stays in SSProve code. `fork_after` runs initialization
once and starts each branch from the saved private heap. `fork_after_sound`
proves the resulting joint distribution and shows that the ambient heap is
unchanged. `fork_after_valid` proves that the transformed code has an empty
physical heap footprint and preserves its import interface.

The semantic result covers closed code, including code linked before the
transformation. `Pr_code` gives unresolved calls zero mass. For live imports,
the reduction needs a linking theorem that specifies which oracle state is
shared across runs and which state is restored. That is the gap between the
prototype and a reduction against arbitrary SSProve adversary packages.

## Probability bounds from a shared checkpoint

Let `S` be the checkpoint after initialization. Given `S`, let `a(S)` and
`b(S)` be the success probabilities of the two openings. The branches sample
independently given `S`, so the binding adversary's double-opening success
probability is `q = E[a(S)b(S)]`. Averaging over the shared `S` can correlate
the two runs.

- `two_openings` proves `E[a] + E[b] ≤ 1 + q`, even if `S` has total mass below
  one. It uses the pointwise inequality `(1 − a)(1 − b) ≥ 0`. The coefficient
  of `q` improves on the `1 + 2q` in the paper. With a fair challenge and
  deterministic, side-effect-free verification, the corresponding target-bit
  bound for coin-toss is `(1 + q)/2`. The event counts a valid opening to the
  target bit, so a committer may abort selectively. The experiments prove the
  inequality. Connecting it to the full coin-toss game remains open.
- `square_checkpoint` proves `E[p]² ≤ E[p²]` for checkpoint subdistributions.
  If the two branches run the same test, their joint success is `E[p²]`.
  For an interactive Σ-protocol with uniform challenges in a set `C`, the
  equal-challenge case costs at most `ε/|C|`, where `ε` is one-run acceptance.
  This gives the extraction target `ε² − ε/|C|` before applying special
  soundness. [Zero-Knowledge in EasyCrypt, §4.2](../background-literature/2022-926.pdf)

## When the fork is inside a procedure

[CoinToss.v](../experiments/CoinToss.v) explores a trace-based interface. The
checkpoint is just before the committer receives the other party's bit. The
starter proves the joint law of two continuations from a supplied trace and
heap. A full reduction still needs to obtain both from the same execution and
construct the binding adversary as an SSProve package.

In a random-oracle signature proof, the first result identifies which hash
query to revisit. The reduction needs the continuation just before that
query and the state it had reached, including the oracle table. Mending's
`run_until_next_call` and `continue_after_call_at_trace` already stop at a call
and recover its continuation under a supplied answer. Its compiler
correctness theorem gives the law of a single linked run. The additional
theorem would describe two runs sharing the selected prefix, with an explicit
choice of which later draws are fresh. A proof that freezes the entire
private random tape needs to say how it does so. [Mending's trace compiler](https://github.com/ethanlee515/Mending/blob/0061e41a48d6548401e954e4b90d942adee8e92c/theories/NextMessage/Trace.v)

The discussion identified three milestones.

1. **Coin-toss.** Build a valid binding adversary from `commit` and two calls
   to `open`. Derive its joint law and apply `two_openings`.
2. **Interactive Schnorr.** Produce two accepting transcripts with distinct
   challenges and feed them to SSProve's existing special-soundness extractor.
   An authentication theorem would also specify the impersonation game and
   any prior sessions. [SSProve's Schnorr extractor](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/theories/Crypt/examples/Schnorr.v#L279-L299) · [Bellare–Palacio](https://cseweb.ucsd.edu/~mihir/papers/gq.pdf)
3. **Schnorr signatures.** Prove an output-selected fork for query-bounded
   SSProve packages, then account for signing simulation and random-oracle
   programming. The Bellare–Neven bound to compare against is
   `ε²/Q − ε/|C|` for `Q` candidate query slots. VCVio implements replay and
   CatCrypt runs two continuations from a saved oracle state. Both provide
   reference points for a theorem stated over SSProve's package interface.
   [Forking Lemma in EasyCrypt](https://eprint.iacr.org/2025/573) · [VCVio's replay proof](https://github.com/Verified-zkEVM/VCVio/blob/main/VCVio/CryptoFoundations/ReplayFork.lean) · [CatCrypt's adaptive forking proof](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/OracleForkingLemma.lean)

## Reproduce the experiments

Run the proofs from the repository root with the `rewinding` dependencies
installed.

```sh
opam exec --switch=rewinding -- rocq compile -Q experiments Rewinding.Experiments experiments/PrivateHeapFork.v
opam exec --switch=rewinding -- rocq compile -Q experiments Rewinding.Experiments experiments/CheckpointBounds.v
opam exec --switch=rewinding -- rocq compile -Q experiments Rewinding.Experiments experiments/CoinToss.v
```

The recovered files compiled with Rocq 9.0.1, MathComp 2.6.0, Analysis 1.18.0,
and the SSProve revision in `rewinding.opam`. On this switch `Print Assumptions`
lists MathComp's propositional extensionality, dependent functional
extensionality, and constructive indefinite description. For the fork
theorems it also lists SSProve's abstract real type `Axioms.R`. The old
MathComp 2.5 experiment additionally listed the admitted interchange of
summations. Analysis 1.18.0 supplies a proof of that lemma. [SSProve's assumptions notes](https://github.com/SSProve/ssprove/blob/9a37fe0ab79d041f8d835e6cf18e37614b16a791/README.md)
