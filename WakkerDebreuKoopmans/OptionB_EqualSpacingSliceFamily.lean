/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — G4.c: assemble the per-slice reps into the shared-`V₀` family (Link B done)

> **STATUS: `sorry`-free assembly brick closing Link B of the §IV.5 construction (G4.c).**
> Not in the umbrella import.

This file executes **G4.c** of `OptionB_SectionIV5GridConstructionRoadmap.md`, the
final brick of Link B (hexagon → per-slice additive representation → the C1 frontier
field).  It is an **assembly**: it wires the G4.a/G4.b per-slice outputs into the
already-mechanized Phase-74 shared-`V₀` family closer
(`RawAxiomDischargers.sharedPivotGridAdditiveRepresentationFamily_of_step4Family_continuous_dense`)
and thence to the end-to-end `Nonempty (AdditiveRep P)`.

## The assembly chain (each link reused, no new mathematics)

G4.a produced, per slice, a grid-normalized slice rep `(Vⱼ₀, Vk)` with
`PairwiseGridNormalizationWitness` + `GridAdditiveSliceRep`; G4.b reduced the off-grid
extension to `PairwiseSliceRepresentationCertificate` (the §IV.5 order-calibration
residual).  Packaging these per slice as a **per-slice grid-normalized representation
family** `hrep`, the chain is:

1. `sharedPivotStep4TradeoffFamilyOnDataCertificate_of_representationFamily` — the
   per-slice family ⟹ the shared-pivot **Step-4 tradeoff family** `hStep4`.
2. `sharedPivotGridAdditiveRepresentationFamily_of_step4Family_continuous_dense`
   (Phase 74) — `hStep4` + pivot-grid **density** + per-slice pivot **continuity**
   ⟹ the **common-`V₀`** family (the M5 density-extension closes the common-scale
   compatibility: pivot utilities agreeing on the dense grid and continuous are equal).
3. `additiveRep_nonempty_of_gridAdditiveRepresentationFamily` (Phase 65) — the common-
   `V₀` family + raw axioms + topology ⟹ `Nonempty (AdditiveRep P)`.

## What this file delivers (all machine-checked, no `sorry`)

* `step4Family_of_perSliceRepresentationFamily` — G4.c step 1: the Step-4 family from
  the per-slice grid-normalized representation family (the form G4.a/b produce).
* `gridAdditiveRepresentationFamily_of_perSliceRepresentationFamily` — G4.c step 1+2:
  the common-`V₀` family from the per-slice family + density + continuity.
* `additiveRep_nonempty_of_perSliceRepresentationFamily` — **the Link-B endpoint**:
  `Nonempty (AdditiveRep P)` from the per-slice family + the structural axioms + the
  topology bundle + density + continuity.
* `perSliceRepresentationFamily_of_additiveRep` — soundness gate: a representation with
  strictly-increasing continuous pivot grids supplies the per-slice family (so the
  assembly hides nothing false).

## Honest scope

G4.c is pure assembly — no new §IV.5 content.  Its inputs are exactly the per-slice
grid-normalized representations (G4.a normalization + G4.b order-calibration), plus the
**analytic** inputs the Phase-74 closer genuinely needs: pivot-grid **density** (G3,
free for ℝ) and per-slice pivot-utility **continuity** (M4 content).  The §IV.5
representation residual itself — constructing the per-slice reps from bare solvability —
is the G1 crux (the per-slice order-calibration = `PairwiseSliceRepresentationCertificate`,
which G4.b pinned to the standard restricted-solvability assembly).  With Link A
(`HexagonThomsenResidual`) and Link B (this) both reduced to that single crux + the
standard analytic inputs, the §IV.5 grid construction is fully scaffolded end-to-end.

This composition inherits the documented Stage-5 `_from_raw_axioms` seams of the
Phase-65 capstone (the C1-constructed `V₀` is not asserted surjective); the clean
foundational-only deliverable is the family closer (Phase 74).  See the C2/surjective
capstones (Phases 66/68) for a seam-free route.

Imports `RawAxiomDischargers` (the Phase-74/65 closers), `Certificates`
(`PairwiseSliceRepresentationCertificate`), `OptionB_EqualSpacingSliceExtend` (G4.b),
`OptionB_EqualSpacingSliceRep` (G4.a).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.RawAxiomDischargers
import WakkerDebreuKoopmans.Certificates
import WakkerDebreuKoopmans.OptionB_EqualSpacingSliceExtend
import WakkerDebreuKoopmans.OptionB_EqualSpacingSliceRep

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

/-- **The per-slice grid-normalized representation family (the G4.a/G4.b output
shape).**

For each non-pivot slice `k ≠ j₀`, a grid-normalized pivot/coordinate utility pair
`(Vⱼ₀, Vk)` that represents the `{j₀,k}`-slice: this is exactly what G4.a (grid
normalization, `PairwiseGridNormalizationWitness`) and G4.b (off-grid order
calibration, `PairwiseSliceRepresentationCertificate`) jointly produce per slice. -/
def PerSliceGridRepresentationFamily
    (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) : Prop :=
  ∀ (k : ι) (hk : k ≠ j₀),
    ∃ Vⱼ₀ : X j₀ → ℝ, ∃ Vk : X k → ℝ,
      PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) Vⱼ₀ Vk ∧
      PairwiseSliceRepresentationCertificate P j₀ k Vⱼ₀ Vk

/-! ## §A.  Step 1 — the Step-4 family from the per-slice representation family -/

/-- **G4.c step 1 (PROVED): the shared-pivot Step-4 tradeoff family from the per-slice
representation family.**

Pure delegation to `sharedPivotStep4TradeoffFamilyOnDataCertificate_of_representationFamily`:
the per-slice grid-normalized representations (G4.a/b) are exactly the engine-C core, so
they discharge the heaviest §IV.5 Step-4 seam.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem step4Family_of_perSliceRepresentationFamily
    (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hrep : PerSliceGridRepresentationFamily P j₀ hdata) :
    SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata :=
  sharedPivotStep4TradeoffFamilyOnDataCertificate_of_representationFamily P j₀ hdata hrep

/-! ## §B.  Step 1+2 — the common-`V₀` family from the per-slice family -/

/-- **G4.c step 1+2 (PROVED): the common-`V₀` grid-additive representation family.**

Composes §A with the Phase-74 closer
`sharedPivotGridAdditiveRepresentationFamily_of_step4Family_continuous_dense`: the
per-slice family + pivot-grid density + per-slice pivot continuity yields the
**common-`V₀`** family (the M5 density extension forces all per-slice pivot utilities
to coincide).  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridAdditiveRepresentationFamily_of_perSliceRepresentationFamily
    [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (solvability : ProductPref.RestrictedSolvability P)
    (j₀ : ι) [T2Space (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hrep : PerSliceGridRepresentationFamily P j₀ hdata)
    (hdense : Dense (Set.range hdata.σⱼ₀.α))
    (hcont : ∀ (k : ι) (hk : k ≠ j₀) (Vⱼ₀ : X j₀ → ℝ) (Vk : X k → ℝ),
      PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) Vⱼ₀ Vk →
      PairwiseSliceRepresentationCertificate P j₀ k Vⱼ₀ Vk →
      Continuous Vⱼ₀) :
    SharedPivotGridAdditiveRepresentationFamily P j₀ hdata :=
  sharedPivotGridAdditiveRepresentationFamily_of_step4Family_continuous_dense
    P solvability j₀ hdata
    (step4Family_of_perSliceRepresentationFamily P j₀ hdata hrep)
    hdense hcont

/-! ## §C.  The Link-B endpoint — `Nonempty (AdditiveRep P)` -/

/-- **Link-B endpoint (PROVED): the additive representation from the per-slice
representation family.**

Composes §B with the Phase-65 end-to-end capstone
`additiveRep_nonempty_of_gridAdditiveRepresentationFamily`: from the per-slice
grid-normalized representations (G4.a/b) + the structural axioms + the topology bundle
+ pivot-grid density + per-slice pivot continuity, the additive representation exists.

This is the **honest closure of Link B**: every step from the per-slice reps to
`Nonempty (AdditiveRep P)` is theorem-backed; the only §IV.5 content is constructing the
per-slice reps (the G1 crux, = `PairwiseSliceRepresentationCertificate` per slice) plus
the standard analytic inputs (density, continuity).  Audit `[propext, Classical.choice,
Quot.sound]` **plus** the documented Phase-65 Stage-5 `_from_raw_axioms` seams (the
C1-constructed `V₀` is not asserted surjective; see the C2/surjective capstones for a
seam-free route). -/
theorem additiveRep_nonempty_of_perSliceRepresentationFamily
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
    (hrep : PerSliceGridRepresentationFamily P j₀ hdata)
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
  additiveRep_nonempty_of_gridAdditiveRepresentationFamily
    P essential solvability archimedean htop j₀ hdata hcov hesc hcov19
    (gridAdditiveRepresentationFamily_of_perSliceRepresentationFamily
      P solvability j₀ hdata hrep hdense hcont)

/-! ## §D.  Soundness gate -/

/-- **Soundness gate (PROVED): a representation supplies the per-slice family.**

Under an additive representation `R`, every non-pivot slice carries the grid-normalized
representation `(R.V j₀, R.V k)`: the slice rep is `orderCalibration_of_additiveRep`
(G4.b), and the grid normalization `Vⱼ₀ (σ.α n) = n` is supplied by the hypothesis
`hnorm` that the shared-pivot grids are `R`-normalized (the standard-sequence
calibration).  Confirms the per-slice family — hence the whole Link-B assembly — hides
nothing false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem perSliceRepresentationFamily_of_additiveRep
    (R : AdditiveRep P) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hnorm : ∀ (k : ι) (hk : k ≠ j₀),
      PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) (R.V j₀) (R.V k)) :
    PerSliceGridRepresentationFamily P j₀ hdata := by
  intro k hk
  refine ⟨R.V j₀, R.V k, hnorm k hk, ?_⟩
  exact orderCalibration_of_additiveRep R j₀ k (Ne.symm hk)

end ProductPref
end WakkerInfra

/-! ## G4.c audit

* `PerSliceGridRepresentationFamily` — the G4.a/G4.b per-slice output shape.
* §A `step4Family_of_perSliceRepresentationFamily` — the Step-4 family from the
  per-slice reps.
* §B `gridAdditiveRepresentationFamily_of_perSliceRepresentationFamily` — the common-`V₀`
  family (Phase-74 closer: density + continuity ⟹ common scale).
* §C `additiveRep_nonempty_of_perSliceRepresentationFamily` — **the Link-B endpoint**:
  `Nonempty (AdditiveRep P)`.
* §D `perSliceRepresentationFamily_of_additiveRep` — soundness gate.

**Honest scope.**  G4.c is pure assembly (no new §IV.5 content): it wires the G4.a/b
per-slice reps into the already-mechanized Phase-74 common-`V₀` closer + the Phase-65
end-to-end capstone.  Its only inputs are the per-slice reps (G1 crux =
`PairwiseSliceRepresentationCertificate`) and the standard analytic inputs (pivot-grid
density, per-slice pivot continuity).  Link B is now closed end-to-end modulo that
single crux; the endpoint inherits the documented Phase-65 Stage-5 seams (non-surjective
`V₀`). -/

#print axioms WakkerInfra.ProductPref.step4Family_of_perSliceRepresentationFamily
#print axioms WakkerInfra.ProductPref.gridAdditiveRepresentationFamily_of_perSliceRepresentationFamily
#print axioms WakkerInfra.ProductPref.additiveRep_nonempty_of_perSliceRepresentationFamily
#print axioms WakkerInfra.ProductPref.perSliceRepresentationFamily_of_additiveRep
