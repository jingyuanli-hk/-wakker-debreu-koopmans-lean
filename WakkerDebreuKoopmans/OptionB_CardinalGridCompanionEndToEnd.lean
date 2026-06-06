/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — Candidate D, Step 4: the end-to-end cardinal-grid companion

> **STATUS: `sorry`-free companion theorem.  Completes Candidate D
> (`OptionB_AlternativeAxiomScoping.md` §6 step 4) to an end-to-end
> `Nonempty (AdditiveRep P)` statement.**
> Not in the umbrella import.

`OptionB_CardinalGridCompanion.lean` executed steps 1–3 of Candidate D at the
**single-slice** level: it showed the C1.a grid wall (`ConcreteDiagonalStep` /
the grid Thomsen closure) is **free** given a single-slice cardinal grid datum
(`CardinalGridSliceStructure`, which carries `GridAdditiveSliceRep` — the grid
order).

This file is **step 4**: lift the cardinal datum to the *family* level and run it
through the already-mechanized Link-B family assembly
(`OptionB_EqualSpacingSliceFamily.additiveRep_nonempty_of_perSliceRepresentationFamily`)
to obtain `Nonempty (AdditiveRep P)`.  It is pure packaging — no new §IV.5
mathematics — exactly as the scoping doc anticipated.

## Honest scope (unchanged from Candidate D)

The family-level cardinal datum assumes, per non-pivot slice, a grid-normalized
coordinate-metric pair that represents the **full** `{j₀,k}`-slice
(`PairwiseSliceRepresentationCertificate`).  In the *cardinal* setting the
coordinate metric represents the whole slice by construction (the metric *is* the
scale), so this datum is free; in the *ordinal* setting it is exactly the C1.a
crux (machine-checked irreducible — `OptionB_ConsolidationSummary.md`).  Hence
this is the **cardinal companion**, a different/weaker theorem, **not** ordinal
Wakker IV.2.7.  Its value: it exhibits the entire cardinal route end-to-end
(`Nonempty (AdditiveRep P)`) with the ordinal crux carried as the explicit
cardinal metric, localizing the ordinal difficulty to constructing that metric.

The two standard analytic inputs (pivot-grid density, per-slice pivot continuity)
are carried as hypotheses — the same ones the ordinal Link-B endpoint consumes;
on ℝ-coordinates with continuous unbounded metrics they hold (the project's
`pivotUtilitySurjective_of_continuous_unbounded` / dense-range machinery).

Imports `OptionB_EqualSpacingSliceFamily` (the Link-B endpoint) and
`OptionB_CardinalGridCompanion` (steps 1–3).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_EqualSpacingSliceFamily
import WakkerDebreuKoopmans.OptionB_CardinalGridCompanion

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open WakkerInfra
open WakkerDebreuKoopmans
open WakkerRoadmap.CertificateChecklist
open WakkerRoadmap.CertificateChecklist.RawAxiomDischargers
open Function

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-! ## §A.  The family-level cardinal grid datum -/

/-- **Family-level cardinal grid structure** over a shared pivot `j₀`.

A common pivot metric `V₀` together with, per non-pivot slice `k ≠ j₀`, a
coordinate metric `Vk` such that `(V₀, Vk)` is grid-normalized on the chosen
shared-pivot grids and represents the **full** `{j₀,k}`-slice.  In the cardinal
setting the metrics `V₀, Vk` are the coordinate scales and the full-slice
representation is definitional; in the ordinal setting the full-slice
representation per slice is the C1.a crux. -/
structure CardinalGridStructureFamily (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) where
  /-- The common pivot coordinate metric. -/
  V₀    : X j₀ → ℝ
  /-- The per-slice coordinate metric. -/
  Vk    : ∀ (k : ι), k ≠ j₀ → X k → ℝ
  /-- Grid-normalization on the shared-pivot grids. -/
  hnorm : ∀ (k : ι) (hk : k ≠ j₀),
    PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) V₀ (Vk k hk)
  /-- The cardinal metric represents the full `{j₀,k}`-slice (free in the
  cardinal setting; the C1.a crux in the ordinal setting). -/
  hrep  : ∀ (k : ι) (hk : k ≠ j₀),
    PairwiseSliceRepresentationCertificate P j₀ k V₀ (Vk k hk)

/-- **The family-level cardinal datum yields the per-slice representation family.**

Pure projection: the cardinal family's common `V₀` and per-slice `Vk`, with the
grid-normalization and full-slice representation, are exactly
`PerSliceGridRepresentationFamily`.  (In the cardinal setting this is free; this
lemma is the bridge to the ordinal Link-B assembly.)  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem perSliceRepresentationFamily_of_cardinalGridStructureFamily
    (j₀ : ι) (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (G : CardinalGridStructureFamily P j₀ hdata) :
    PerSliceGridRepresentationFamily P j₀ hdata :=
  fun k hk => ⟨G.V₀, G.Vk k hk, G.hnorm k hk, G.hrep k hk⟩

/-! ## §B.  The end-to-end cardinal companion -/

/-- **Candidate D, Step 4 (PROVED): the additive representation from the
family-level cardinal grid datum.**

Lifts the cardinal per-slice family through the Link-B endpoint
`additiveRep_nonempty_of_perSliceRepresentationFamily`.  The two analytic inputs
(pivot-grid density `hdense`, per-slice pivot continuity `hcont`) are the same
standard inputs the ordinal Link-B endpoint consumes.

**Honest scope.**  This is the **cardinal companion**, not ordinal Wakker IV.2.7:
the per-slice full-slice representations are the cardinal metric (free in the
cardinal setting; the machine-checked-irreducible C1.a crux in the ordinal
setting).  It exhibits the full cardinal route end-to-end, localizing the ordinal
difficulty to constructing the cardinal metric.  Audit `[propext,
Classical.choice, Quot.sound]` **plus** the documented Phase-65 Stage-5
`_from_raw_axioms`-free seams inherited from the Link-B endpoint (non-surjective
`V₀`; the C2/surjective capstones give a seam-free route). -/
theorem additiveRep_of_cardinalGridStructureFamily
    [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) [T2Space (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (G : CardinalGridStructureFamily P j₀ hdata)
    (hdense : Dense (Set.range hdata.σⱼ₀.α))
    (hcont : ∀ (k : ι) (hk : k ≠ j₀) (Vⱼ₀ : X j₀ → ℝ) (Vk : X k → ℝ),
      PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) Vⱼ₀ Vk →
      PairwiseSliceRepresentationCertificate P j₀ k Vⱼ₀ Vk →
      Continuous Vⱼ₀)
    (hcov : ∀ j₀' : ι, TwoPivotSliceTransportCoverageResidual P j₀')
    (hesc : ∀ j₀' : ι, PivotGridEscapesAtTarget P j₀')
    (hcov19 : ∀ hdata' : Stage4MatchedAllPairsAdditivityData P,
      AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate P hdata') :
    Nonempty (AdditiveRep P) :=
  additiveRep_nonempty_of_perSliceRepresentationFamily
    P essential solvability archimedean htop j₀ hdata
    (perSliceRepresentationFamily_of_cardinalGridStructureFamily j₀ hdata G)
    hdense hcont hcov hesc hcov19

/-! ## §C.  Soundness gate (gate 2): the family-level cardinal datum is rep-necessary -/

/-- **Soundness gate (PROVED): a representation supplies the family-level cardinal
grid datum.**

Under an additive representation `R`, taking `V₀ := R.V j₀` and `Vk := R.V k`, the
per-slice full-slice representation is `orderCalibration_of_additiveRep` (G4.b);
grid-normalization is the hypothesis `hnorm` that the shared-pivot grids are
`R`-normalized (the standard-sequence calibration).  So the family-level cardinal
datum is necessary under a rep — it hides nothing false.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
def cardinalGridStructureFamily_of_additiveRep
    (R : AdditiveRep P) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hnorm : ∀ (k : ι) (hk : k ≠ j₀),
      PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) (R.V j₀) (R.V k)) :
    CardinalGridStructureFamily P j₀ hdata where
  V₀    := R.V j₀
  Vk    := fun k _ => R.V k
  hnorm := hnorm
  hrep  := fun k hk => orderCalibration_of_additiveRep R j₀ k (Ne.symm hk)

end ProductPref
end WakkerInfra

/-! ## Candidate D, Step 4 audit

* §A `CardinalGridStructureFamily` / `perSliceRepresentationFamily_of_cardinalGridStructureFamily`
  — the family-level cardinal datum and its bridge to the per-slice family.
* §B `additiveRep_of_cardinalGridStructureFamily` — **the end-to-end cardinal companion**:
  `Nonempty (AdditiveRep P)` from the family-level cardinal datum + the standard
  analytic inputs.
* §C `cardinalGridStructureFamily_of_additiveRep` — the soundness gate (rep-necessary).

**Honest scope.**  Pure packaging completing Candidate D to an end-to-end statement;
the per-slice full-slice representations are the cardinal metric (free in the cardinal
setting; the machine-checked-irreducible ordinal C1.a crux otherwise).  This is the
cardinal companion, NOT ordinal Wakker IV.2.7.  Audit `[propext, Classical.choice,
Quot.sound]` (+ the Link-B endpoint's documented non-surjective-`V₀` seams). -/

#print axioms WakkerInfra.ProductPref.perSliceRepresentationFamily_of_cardinalGridStructureFamily
#print axioms WakkerInfra.ProductPref.additiveRep_of_cardinalGridStructureFamily
#print axioms WakkerInfra.ProductPref.cardinalGridStructureFamily_of_additiveRep
