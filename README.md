# wakker-debreu-koopmans-lean

A Lean 4 / Mathlib mechanization of **Wakker's additive representation theorem
(Theorem IV.2.7)** for product preferences and the **Debreu–Koopmans hard
direction** (convex preference ⟹ per-coordinate concavity).

This is the formal-methods spin-out of the *Classical Lottery in Action*
(Management Science, 2026) artifact: it isolates and develops the
representation-theoretic layer that the published artifact imports. The
applied Management Science artifact lives separately at
[`classical-lottery-in-action-lean-artifact`](https://github.com/jingyuanli-hk/classical-lottery-in-action-lean-artifact).

**Preprint:** [arXiv:2606.08902](https://arxiv.org/abs/2606.08902)

## What this artifact establishes (verified, `sorry`-free)

- The public theorems `wakker_IV_2_7` and `debreu_koopmans_hard` are **conditional
  wrappers** that consume the additive-representation construction as an explicit,
  clearly-labelled hypothesis; together with the certificate layers (topology
  ladder, global gluing, affine uniqueness) they audit at
  `[propext, Classical.choice, Quot.sound]`.
- The forward construction from the bare structural axioms is **not** claimed —
  and is **machine-checked irreducible** from them. It is reduced to a **single**
  proven-necessary structural input (the cross-pair Thomsen / double-cancellation
  hexagon, equivalently the per-slice grid-additive representation), with **both**
  links of the §IV.5 grid construction assembled end-to-end around it
  (Link A: `doubleCancellation_of_blockIndependence_and_escapeJ2`;
  Link B: `additiveRep_nonempty_of_perSliceRepresentationFamily`).
- That input's irreducibility from {coordinate independence + restricted
  solvability + Archimedean + topology} is pinned by **seven machine-checked
  findings** — including a concrete `n = 3` model satisfying single-coordinate
  independence on every coordinate yet violating the hexagon
  (`constraint1_a1_does_not_imply_hexagon`).
- A sound **cardinal-grid companion** (`additiveRep_of_cardinalGridStructureFamily`)
  discharges the same conclusion once a coordinate scale is supplied, localizing
  the irreducible content to the ordinal construction of that scale.
- There are **no `_from_raw_axioms` axioms** anywhere in the development; the only
  primitive axioms are two clearly-labelled §III.4.2 topology bracket-reach seams.

See `ClassicalLotteryInAction_companion.pdf` for the full paper, and the
documentation files below for the machine-checked status and the irreducibility
analysis.

## Repository layout

| Path | Contents |
| --- | --- |
| `WakkerDebreuKoopmans/Core.lean`, `Certificates.lean`, `M2Frontier.lean`, `ConstructionStack.lean`, `Topology.lean`, `Closure.lean`, `Audit.lean`, `BernsteinDoetsch.lean`, `C1FromStage4.lean` | the split certificate/topology/closure modules |
| `WakkerDebreuKoopmans/RawAxiomDischargers*.lean` | the structural-axiom discharge layer (core, topology IVT, standard sequence, hexagon, Thomsen) |
| `WakkerDebreuKoopmans/OptionB_*.lean` | the Option B reduction: the single-input reduction, both §IV.5 links, the seven irreducibility findings, and the cardinal-grid companion |
| `WakkerDebreuKoopmans/OptionB_AxiomCheck.lean` | the sorry-free audit aggregator (`#print axioms` over the development) |
| `ClassicalLotteryInAction_companion.{tex,pdf}` | the formal-methods companion paper |
| `OptionB_ConsolidationSummary.md` | **ground-truth** machine-checked status |
| `OptionB_AlternativeAxiomScoping.md` | the different-axiom-set analysis (cardinal-grid companion) |
| `STEP4_DISCHARGE_ROADMAP.md` | the §IV.5 Step-4 discharge roadmap and the irreducibility finding |
| `OptionB_AxiomAudit_README.md`, `OptionB_AxiomAudit_baseline.txt` | the committed axiom-audit baseline and how to read it |

## Build

Prerequisites: [elan](https://lean-lang.org/elan/) (toolchain pinned to
`v4.28.0-rc1` in `lean-toolchain`) and Git.

```text
lake exe cache get   # fetch the prebuilt Mathlib cache (recommended)
lake build           # build the spin-out development
```

The default target builds the three roots in `lakefile.lean` and their transitive
imports (the full 93-module development, including the sorry-free
`OptionB_AxiomCheck` audit).

## License

Apache License 2.0 — see [`LICENSE.txt`](LICENSE.txt).

## Citation

> Jingyuan Li, Ilia Tsetlin, and Fan Wang.
> *A Kernel-Clean Lean Mechanization of Classical Lottery in Action
> and the Wakker–Debreu–Koopmans Representation Layer*
> arXiv preprint: [arXiv:2606.08902](https://arxiv.org/abs/2606.08902)

Please also cite the Management Science paper:

> Jingyuan Li, Ilia Tsetlin, and Fan Wang (2026),
> *Classical Lottery in Action: Quantifying Risk and Evaluating Uncertainty*,
> Management Science. DOI: [10.1287/mnsc.2023.04202](https://doi.org/10.1287/mnsc.2023.04202)
