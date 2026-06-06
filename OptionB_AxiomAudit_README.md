# Option B — axiom audit baseline

This directory ships a committed baseline of the full axiom audit for the Option B
construction, so that the claim "the residual frontier is the entire remaining
obligation" is a *checked* fact rather than a prose assertion.

## Files

* `OptionB_AxiomAudit_baseline.txt` — the raw `lake build WakkerDebreuKoopmans.OptionB_AxiomCheck`
  output, capturing every `#print axioms` line emitted by `OptionB_AxiomCheck.lean`
  (which imports the entire Option B development).  Regenerate with:

  ```
  lake build WakkerDebreuKoopmans.OptionB_AxiomCheck
  ```

  (run from the `research/` package root; the `#print axioms` results are emitted
  as `info:` lines during the build).

## How to read it

Every Option B declaration audits at one of:

* `[propext, Quot.sound]` — foundational only (`FND`); or
* `[propext, Classical.choice, Quot.sound]` — foundational + choice (`FND+C`).

There is **no `sorryAx`** anywhere in the audit.

### Two classes of named axioms appear, both expected and documented

1. **The two §III.4.2 topology bracket-reach axioms**
   `coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology`.
   These are the topology-IVT seams.  The Option B **canonical reach-axiom-free
   target** `RawAxiomDischargers.additiveRep_nonempty_from_structural_axioms_reachAxiomFree`
   **eliminates** them: it audits at exactly `[propext, Classical.choice,
   Quot.sound]` (see its line in the baseline), routing the standard-sequence
   construction through the engine-A∘B Archimedean escape instead.

2. **The legacy `*_from_raw_axioms` names** (e.g.
   `sharedPivotStep4TradeoffFamilyOnDataCertificate_from_raw_axioms`,
   `twoPivotSliceTransport{Forward,Backward}Certificate_from_raw_axioms`).
   These are now **theorems**, not axioms — the entire `_from_raw_axioms` family
   has been excised or restated (the last one,
   `sharedPivotStep4TradeoffFamilyOnDataCertificate_from_raw_axioms`, now consumes
   the proven-necessary named input `SharedPivotGridAdditiveRepresentationFamily`).
   **There are no `_from_raw_axioms` axiom declarations anywhere in the tree**
   (`grep "^axiom .*_from_raw_axioms"` → no matches). They still appear in the
   baseline only as the *names of theorems* being audited by `#print axioms`
   lines; none is a kernel axiom dependency. The only remaining `axiom`
   declarations in the whole tree are the two §III.4.2 topology bracket-reach
   seams in item 1.

## The honest scope, restated

The Option B canonical target is **conditional on the explicit residual frontier**
(the open C1/B1/B2/density residuals carried as hypotheses, *not* axioms).  The
audit confirms that frontier is the *entire* remaining obligation: no
`_from_raw_axioms` seam and no `sorryAx` in the canonical chain.

The genuine open mathematical content is the cross-pair trade-off transitivity
`CrossPairTradeoffTransitivity` (= `KzTransfer`), Wakker IV.2.5's hexagon — proved
necessary under any representation, proved **not** derivable from single-coordinate
independence A1 (the machine-checked `Pcm`/`Pstrip`/`Pkz` countermodels), and shown
circular to derive from the permutation-equivalent diagonal residues (§D.2b).  The
forward bricks (`OptionB_C1aHexagonConstruction.lean`,
`OptionB_C1aCrossPairDenseAnchor.lean`) reduce and sharpen it but do not eliminate
it; the full standard-sequence equal-spacing construction remains the genuine
§IV.5/§IV.2.6 frontier.
