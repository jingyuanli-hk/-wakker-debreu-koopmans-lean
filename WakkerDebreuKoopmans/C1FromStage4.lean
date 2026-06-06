/-
This file is part of the split `WakkerDebreuKoopmans` module family.
The public import surface remains `WakkerDebreuKoopmans.lean`.

# C1 closure from Stage-4 pivot-slice data and named cross-coordinate residues

This file packages the Phase-8 C1 closure
(`WakkerConstructionInputCertificate`) as a *single composite theorem*
consuming the active Stage-4 pivot-slice attack surface
(`WakkerStage4PivotSliceRepresentationData`) plus exactly three named
cross-coordinate residues already isolated by the A1/A2/A3 dischargers
in `Closure.lean`:

* `NonPivotPairAdditivityCertificate`  — A1's cross-pair residue,
* `WakkerStep5StrictMonotonicityResidualAtPivot` — A3's cross-profile
  residue,
* `WakkerStep5CoordinateImageCoverageResidualAtPivot` — A2's per-pivot
  coverage residue.

The wrapper inlines the A1 existential `V` once and shares it across
the A2/A3 residue dischargers (the per-cert wrappers in `Closure.lean`
each call A1 separately via `Classical.choose` and therefore pick
different `V`'s; sharing `V` is the actual technical content here),
then feeds the resulting `(V, hpair, hcov, hstrict)` tuple into the
existing chain-construction wrapper
`wakkerConstructionInputCertificate_of_chainConstruction` from
`M2Frontier.lean`.

The output is a non-circular reduction of C1 to exactly the three
named cross-coordinate residues (plus the active Stage-4 pivot-slice
data, which itself has theorem-backed dischargers in `Closure.lean`).
No new sorry / axiom / unproved lemma is introduced; the discharger
chain is theorem-backed in `Closure.lean` and `M2Frontier.lean`.
-/

import WakkerDebreuKoopmans.Closure
import WakkerDebreuKoopmans.M2Frontier

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

open scoped BigOperators
open Function Finset

namespace WakkerRoadmap

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

open WakkerInfra
open WakkerDebreuKoopmans (AdditiveRep)

namespace CertificateChecklist

/-! ##### C1 — unified closure from Stage-4 pivot-slice data and three
named cross-coordinate residues.

The two existing Stage-4-to-Step-5 wrappers
(`wakkerStep5StrictMonotonicityCertificate_of_stage4PivotSliceRepresentationData`
and `wakkerStep5CoordinateImageCoverageCertificate_of_stage4PivotSliceRepresentationData`)
each return their own existential `V`, so they cannot be combined
directly into a single C1 input bundle.  The composite wrapper below
fixes one `V` (via A1 = `allPairsAdditivityCertificate_of_stage4PivotSliceRepresentationData`)
and uses the *primitive* (non-existential)
`wakkerStep5StrictMonotonicityCertificate_of_allPairsAdditivity` and
`wakkerStep5CoordinateImageCoverageCertificate_of_residueAtPivot`
dischargers against that shared `V`.

The result is a single existential triple `(j₀, V, …)` carrying all
three Step-5 inputs simultaneously, which then feeds the existing
chain-construction wrapper. -/

/-- **C1 (Stage-4 attack surface).**  A `WakkerConstructionInputCertificate`
from active Stage-4 pivot-slice data and three named cross-coordinate
residues, packaged through the M1 chain-construction wrapper.

This is the C1 analogue of the C3/C4/C5 composite reductions in
`M2Frontier.lean`: every consumed step is theorem-backed in
`Closure.lean` or `M2Frontier.lean`, and the remaining open content
collapses to the three named residues (`hCross`, `hResStrict`,
`hResCov`) plus the Stage-4 input (`hStage4`).  The Stage-4 input
itself has theorem-backed dischargers in `Closure.lean`
(`wakkerStage4PivotSliceRepresentationData_of_sharedPivot` and
`wakkerStage4PivotSliceRepresentationData_of_stage3FiniteCutCoverage_and_normalization`),
so the genuinely remaining Wakker IV.2 work is reduced to:

* a `SharedPivotAllPairsStep4MachineryCertificate` (Stage-4 normalization,
  Wakker IV.2 Step 4 affine renormalization);
* a `NonPivotPairAdditivityCertificate` (Wakker IV.2 Step 5 cross-pair
  consistency);
* a `WakkerStep5StrictMonotonicityResidualAtPivot` (Step 5 cross-profile
  indifference);
* a `WakkerStep5CoordinateImageCoverageResidualAtPivot` (Step 5
  Archimedean / coverage).

All four are the canonical Wakker IV.2–IV.6 standard-sequence outputs
identified in the Phase-8 roadmap.  No new sorry / axiom introduced. -/
theorem wakkerConstructionInputCertificate_of_stage4PivotSliceRepresentationData
    {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    [_hne   : Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hStage4 : WakkerStage4PivotSliceRepresentationData P)
    (hCross : ∀ j₀ : ι, ∀ (V : (i : ι) → X i → ℝ),
      (∀ k : ι, k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) →
      NonPivotPairAdditivityCertificate P V j₀)
    (hResStrict : ∀ j₀ : ι, ∀ (V : (i : ι) → X i → ℝ),
      WakkerStep5StrictMonotonicityResidualAtPivot P V j₀)
    (hResCov : ∀ (V : (i : ι) → X i → ℝ) (j₀ : ι),
      WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀) :
    WakkerConstructionInputCertificate P essential solvability archimedean := by
  -- Apply A1 once to pin down `(j₀, V, hMatch, hpair)`.
  obtain ⟨j₀, V, hMatch, hpair⟩ :=
    allPairsAdditivityCertificate_of_stage4PivotSliceRepresentationData
      hStage4 hCross
  -- Discharge A3 against the same `V`.
  have hstrict :
      WakkerStep5StrictMonotonicityCertificate P V hpair solvability :=
    wakkerStep5StrictMonotonicityCertificate_of_allPairsAdditivity
      j₀ V hpair solvability (hResStrict j₀ V)
  -- Discharge A2 against the same `V`.
  have hcov :
      WakkerStep5CoordinateImageCoverageCertificate P V hpair solvability :=
    wakkerStep5CoordinateImageCoverageCertificate_of_residueAtPivot
      V hpair solvability (fun j => hResCov V j)
  -- Feed the shared `(V, hpair, hcov, hstrict)` tuple into the existing
  -- chain-construction wrapper.
  exact wakkerConstructionInputCertificate_of_chainConstruction
    P essential solvability archimedean V hpair hcov hstrict

/-- **Public C1 + `wakker_IV_2_7` consumer (Stage-4 form).**

Composes the Stage-4 C1 closure above with
`additiveRep_nonempty_of_wakkerConstructionInputCertificate` to produce
`Nonempty (AdditiveRep P)` directly from the same Stage-4 pivot-slice
data plus the three named cross-coordinate residues. -/
theorem additiveRep_nonempty_of_stage4PivotSliceRepresentationData
    {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    [_hne   : Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hStage4 : WakkerStage4PivotSliceRepresentationData P)
    (hCross : ∀ j₀ : ι, ∀ (V : (i : ι) → X i → ℝ),
      (∀ k : ι, k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) →
      NonPivotPairAdditivityCertificate P V j₀)
    (hResStrict : ∀ j₀ : ι, ∀ (V : (i : ι) → X i → ℝ),
      WakkerStep5StrictMonotonicityResidualAtPivot P V j₀)
    (hResCov : ∀ (V : (i : ι) → X i → ℝ) (j₀ : ι),
      WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀) :
    Nonempty (AdditiveRep P) :=
  additiveRep_nonempty_of_wakkerConstructionInputCertificate
    (_hne := _hne) P essential solvability archimedean
    (wakkerConstructionInputCertificate_of_stage4PivotSliceRepresentationData
      P essential solvability archimedean
      hStage4 hCross hResStrict hResCov)

/-! ##### C1 — unified closure from Stage-3 finite-cut coverage data and
named cross-coordinate residues.

One layer further down: bypass the Stage-4 input by chaining the existing
`wakkerStage4PivotSliceRepresentationData_of_stage3FiniteCutCoverage_and_normalization`
lift in `Closure.lean` with the Stage-4 wrapper above.  This is the
Stage-3 attack surface for C1, mirroring the Stage-3 → Stage-4 lift
already in the tree.

Hypotheses additionally required relative to the Stage-4 form:

* `SharedPivotAllPairsStep4MachineryCertificate P j₀` (Wakker IV.2 Step 4
  affine renormalization at the chosen pivot `j₀`);
* a `PairwiseFiniteCutCoverageCertificate` for one non-pivot coordinate
  `k ≠ j₀` (the witness of Stage-3 finite-cut coverage at `j₀`);
* continuity of all candidate utilities on the pivot coordinate and
  density of every standard-sequence grid on the pivot coordinate
  (both already available on standard topological domains). -/

/-- **C1 (Stage-3 attack surface).**  A `WakkerConstructionInputCertificate`
from active Stage-3 finite-cut coverage data at a fixed pivot, the Step-4
affine renormalization certificate, and the same three named
cross-coordinate residues consumed by the Stage-4 form.

Internally chains
`wakkerStage4PivotSliceRepresentationData_of_stage3FiniteCutCoverage_and_normalization`
(Closure.lean) with the Stage-4 C1 closer above.  No new sorry / axiom. -/
theorem wakkerConstructionInputCertificate_of_stage3FiniteCutCoverage_and_normalization
    {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    [_hne   : Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) [TopologicalSpace (X j₀)] [T2Space (X j₀)]
    (hStage3AtPivot : ∃ k : ι, k ≠ j₀ ∧
      ∃ (σj : ProductPref.StandardSequence P j₀)
        (σk : ProductPref.StandardSequence P k),
        PairwiseFiniteCutCoverageCertificate σj σk)
    (hNorm : SharedPivotAllPairsStep4MachineryCertificate P j₀)
    (hcont : ∀ (V : X j₀ → ℝ), Continuous V)
    (hdense_grid : ∀ σⱼ₀ : ProductPref.StandardSequence P j₀,
      Dense (Set.range σⱼ₀.α))
    (hCross : ∀ j₀' : ι, ∀ (V : (i : ι) → X i → ℝ),
      (∀ k : ι, k ≠ j₀' →
        PairwiseSliceRepresentationCertificate P j₀' k (V j₀') (V k)) →
      NonPivotPairAdditivityCertificate P V j₀')
    (hResStrict : ∀ j₀' : ι, ∀ (V : (i : ι) → X i → ℝ),
      WakkerStep5StrictMonotonicityResidualAtPivot P V j₀')
    (hResCov : ∀ (V : (i : ι) → X i → ℝ) (j₀' : ι),
      WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀') :
    WakkerConstructionInputCertificate P essential solvability archimedean :=
  wakkerConstructionInputCertificate_of_stage4PivotSliceRepresentationData
    P essential solvability archimedean
    (wakkerStage4PivotSliceRepresentationData_of_stage3FiniteCutCoverage_and_normalization
      (j₀ := j₀) solvability hStage3AtPivot hNorm hcont hdense_grid)
    hCross hResStrict hResCov

/-- **Public C1 + `wakker_IV_2_7` consumer (Stage-3 form).** -/
theorem additiveRep_nonempty_of_stage3FiniteCutCoverage_and_normalization
    {X : ι → Type v}
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    [_hne   : Nonempty ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) [TopologicalSpace (X j₀)] [T2Space (X j₀)]
    (hStage3AtPivot : ∃ k : ι, k ≠ j₀ ∧
      ∃ (σj : ProductPref.StandardSequence P j₀)
        (σk : ProductPref.StandardSequence P k),
        PairwiseFiniteCutCoverageCertificate σj σk)
    (hNorm : SharedPivotAllPairsStep4MachineryCertificate P j₀)
    (hcont : ∀ (V : X j₀ → ℝ), Continuous V)
    (hdense_grid : ∀ σⱼ₀ : ProductPref.StandardSequence P j₀,
      Dense (Set.range σⱼ₀.α))
    (hCross : ∀ j₀' : ι, ∀ (V : (i : ι) → X i → ℝ),
      (∀ k : ι, k ≠ j₀' →
        PairwiseSliceRepresentationCertificate P j₀' k (V j₀') (V k)) →
      NonPivotPairAdditivityCertificate P V j₀')
    (hResStrict : ∀ j₀' : ι, ∀ (V : (i : ι) → X i → ℝ),
      WakkerStep5StrictMonotonicityResidualAtPivot P V j₀')
    (hResCov : ∀ (V : (i : ι) → X i → ℝ) (j₀' : ι),
      WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀') :
    Nonempty (AdditiveRep P) :=
  additiveRep_nonempty_of_wakkerConstructionInputCertificate
    (_hne := _hne) P essential solvability archimedean
    (wakkerConstructionInputCertificate_of_stage3FiniteCutCoverage_and_normalization
      P essential solvability archimedean j₀
      hStage3AtPivot hNorm hcont hdense_grid
      hCross hResStrict hResCov)

end CertificateChecklist

end WakkerRoadmap

/-! ##### Axiom audit

Both wrappers above should depend only on the standard Lean axioms
`[propext, Classical.choice, Quot.sound]` (no `sorry`, no new named
axioms).  This mirrors the audit pattern in `Audit.lean`. -/
#print axioms WakkerRoadmap.CertificateChecklist.wakkerConstructionInputCertificate_of_stage4PivotSliceRepresentationData
#print axioms WakkerRoadmap.CertificateChecklist.additiveRep_nonempty_of_stage4PivotSliceRepresentationData
#print axioms WakkerRoadmap.CertificateChecklist.wakkerConstructionInputCertificate_of_stage3FiniteCutCoverage_and_normalization
#print axioms WakkerRoadmap.CertificateChecklist.additiveRep_nonempty_of_stage3FiniteCutCoverage_and_normalization
