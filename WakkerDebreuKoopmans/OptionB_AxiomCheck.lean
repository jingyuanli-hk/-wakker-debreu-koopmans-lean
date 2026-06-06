/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — progress axiom audit (WP0)

This is the **Option B** reviewer-facing audit surface, created by WP0 of
`OptionB_UnconditionalConstructionRoadmap.md`.  It is deliberately **separate**
from the paper-cited `Wakker/AxiomCheck.lean`:

* `Wakker/AxiomCheck.lean` audits the *current* public theorem surface, whose
  `wakker_IV_2_7` / `debreu_koopmans_hard` are **wrappers** taking the
  representation as a hypothesis.  It stays untouched until Option B completes.
* This file audits the **Option B canonical target**
  `additiveRep_nonempty_from_structural_axioms_and_coordinateIndependence`, which
  is `Nonempty (AdditiveRep P)` from the structural axioms + topology bundle
  (coordinate independence explicit via `htop.separable`) **conditional on** the
  open residual frontier `OptionBResidualFrontier`.

Per WP-integrate, once `OptionBResidualFrontier` is theorem-backed (WP-C1.a,
WP-C1.b, WP-density, WP-B1, WP-B2), the merge of these prints into
`Wakker/AxiomCheck.lean` makes the public `wakker_IV_2_7` unconditional and the
papers' claim honest.

## Current expected audit

The WP0 target and bridge depend on
`[propext, Classical.choice, Quot.sound]` **plus** the two §III.4.2 topology IVT
seams
`coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology`
(to be discharged by WP-T), and **no** `_from_raw_axioms` seam and **no**
`sorryAx`.  The §5 gate and WP-CI results are foundational-only.

This file is standalone and not in the umbrella import.
-/

import WakkerDebreuKoopmans.RawAxiomDischargers
import WakkerDebreuKoopmans.OptionB_C1aSoundnessGate
import WakkerDebreuKoopmans.OptionB_CoordinateIndependence
import WakkerDebreuKoopmans.OptionB_EscapeGridNecessity
import WakkerDebreuKoopmans.OptionB_C1aHexagonProbe
import WakkerDebreuKoopmans.OptionB_C1aThirdCoordinate
import WakkerDebreuKoopmans.OptionB_C1aStripProbe
import WakkerDebreuKoopmans.OptionB_C1aEndpoint
import WakkerDebreuKoopmans.OptionB_C1aJ2Escape
import WakkerDebreuKoopmans.OptionB_C1aCrossPairFrontier
import WakkerDebreuKoopmans.OptionB_ResidualSharedInfrastructure
import WakkerDebreuKoopmans.OptionB_EscapeGridRefinement
import WakkerDebreuKoopmans.OptionB_EscapeGridSoundnessGate
import WakkerDebreuKoopmans.OptionB_DKConcavityEndpoint
import WakkerDebreuKoopmans.OptionB_DKMidpointProbe
import WakkerDebreuKoopmans.OptionB_DKGlobalQuasiconcavity
import WakkerDebreuKoopmans.OptionB_DKTwoCoordMidpoint
import WakkerDebreuKoopmans.OptionB_DKAffineCompanion
import WakkerDebreuKoopmans.OptionB_DKStandardStickAffine
import WakkerDebreuKoopmans.OptionB_ExtensionDataFromContinuity
import WakkerDebreuKoopmans.OptionB_RationalImageFromTopology
import WakkerDebreuKoopmans.OptionB_C1aStripLevels
import WakkerDebreuKoopmans.OptionB_C1aBlockIndependence
import WakkerDebreuKoopmans.OptionB_C1aKzProbe
import WakkerDebreuKoopmans.OptionB_C1aKzReduction
import WakkerDebreuKoopmans.OptionB_C1aKzAnchor
import WakkerDebreuKoopmans.OptionB_C1aKLSTCapstone
import WakkerDebreuKoopmans.OptionB_BlockFromA1
import WakkerDebreuKoopmans.OptionB_C1aDiagonalResidue
import WakkerDebreuKoopmans.OptionB_C1aDiagonalSymmetry
import WakkerDebreuKoopmans.OptionB_C1aDiagonalBaseIndep
import WakkerDebreuKoopmans.OptionB_C1aDiagonalThomsen
import WakkerDebreuKoopmans.OptionB_C1aDiagonalPermutation
import WakkerDebreuKoopmans.OptionB_C1aDiagonalPermutationJ
import WakkerDebreuKoopmans.OptionB_C1aDiagonalUnifiedCapstone
import WakkerDebreuKoopmans.OptionB_C1aDiagonalStrict
import WakkerDebreuKoopmans.OptionB_C1aDiagonalEquivalence
import WakkerDebreuKoopmans.OptionB_C1aDiagonalAntisym
import WakkerDebreuKoopmans.OptionB_C1aDiagonalTrichotomy
import WakkerDebreuKoopmans.OptionB_C1aDiagonalTransitivity
import WakkerDebreuKoopmans.OptionB_C1aDiagonalSetoid
import WakkerDebreuKoopmans.OptionB_C1aDiagonalExclusive
import WakkerDebreuKoopmans.OptionB_C1aDiagonalSampleStable
import WakkerDebreuKoopmans.OptionB_C1aDiagonalMixedTrans
import WakkerDebreuKoopmans.OptionB_C1aDiagonalSubst
import WakkerDebreuKoopmans.OptionB_C1aDiagonalScore
import WakkerDebreuKoopmans.OptionB_C1aDiagonalHexagon
import WakkerDebreuKoopmans.OptionB_C1aGridThomsen
import WakkerDebreuKoopmans.OptionB_C1aGridTransport
import WakkerDebreuKoopmans.OptionB_C1aHexagonConstruction
import WakkerDebreuKoopmans.OptionB_C1aCrossPairDenseAnchor
import WakkerDebreuKoopmans.OptionB_EqualSpacingProbe
import WakkerDebreuKoopmans.OptionB_EqualSpacingStrictness
import WakkerDebreuKoopmans.OptionB_EqualSpacingSecondSequence
import WakkerDebreuKoopmans.OptionB_EqualSpacingLayerTransport
import WakkerDebreuKoopmans.OptionB_EqualSpacingArchimedeanGrid
import WakkerDebreuKoopmans.OptionB_EqualSpacingPivotSplit
import WakkerDebreuKoopmans.OptionB_HexagonCapstone
import WakkerDebreuKoopmans.OptionB_SectionIV5HardConstraints
import WakkerDebreuKoopmans.OptionB_EqualSpacingThomsenCell
import WakkerDebreuKoopmans.OptionB_EqualSpacingGridPropagate
import WakkerDebreuKoopmans.OptionB_EqualSpacingGridStep
import WakkerDebreuKoopmans.OptionB_EqualSpacingGridTransport
import WakkerDebreuKoopmans.OptionB_EqualSpacingMeshDensity
import WakkerDebreuKoopmans.OptionB_EqualSpacingSliceRep
import WakkerDebreuKoopmans.OptionB_EqualSpacingSliceExtend
import WakkerDebreuKoopmans.OptionB_EqualSpacingSliceFamily
import WakkerDebreuKoopmans.OptionB_EqualSpacingLinkACapstone
import WakkerDebreuKoopmans.OptionB_C1aCompensationExistence
import WakkerDebreuKoopmans.OptionB_C1aThomsenClosure
import WakkerDebreuKoopmans.OptionB_C1aMeasuringStick
import WakkerDebreuKoopmans.OptionB_C1aStickConstruction
import WakkerDebreuKoopmans.OptionB_C1aSimultaneousClosure
import WakkerDebreuKoopmans.OptionB_CardinalGridCompanion
import WakkerDebreuKoopmans.OptionB_C1aHexagon
import WakkerDebreuKoopmans.OptionB_C1aNamedInputClosure
import WakkerDebreuKoopmans.OptionB_C1aThomsenResidueDischarge

set_option linter.unusedVariables false

/-! ## §5 gate — `TradeoffConsistency` is exactly single-coordinate indiff
    base-independence (foundational-only). -/

#print axioms WakkerInfra.ProductPref.tradeoffConsistency_iff_indiffBaseIndependent

/-! ## WP-CI — coordinate independence: necessity + hierarchy (foundational-only). -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep
#print axioms WakkerInfra.ProductPref.coordinateOrderIndependent_of_additiveRep
#print axioms WakkerInfra.ProductPref.indiffBaseIndependent_of_coordinateOrderIndependent

/-! ## WP-density + WP-B1 — escape-grid / density residual is NECESSARY (sound),
    and provably irreducible (single dense sequence impossible).  Soundness
    witnesses only — see `OptionB_EscapeGridNecessity.lean`. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridNecessity.lowerEscape_necessary
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridNecessity.upperEscape_necessary
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridNecessity.twoSidedEscape_necessary
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridNecessity.selectedRefinedDenseGrid_of_betweenPoints

/-! ## WP-C1.a probe — A1 alone does NOT imply the hexagon (concrete n=3 countermodel).

The probe verdict: single-coordinate independence (A1) is satisfied by a
non-additive, Thomsen-violating comonotone model, so WP-C1.a must use restricted
solvability + the third coordinate (the genuine Debreu/KLST construction), not a
one-line A1 projection. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aHexagonProbe.cm_coordinateOrderIndependent
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aHexagonProbe.cm_not_doubleCancellation
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aHexagonProbe.a1_does_not_imply_doubleCancellation

/-! ## WP-C1.a forward construction — the Debreu third-coordinate step.

The hexagon `DoubleCancellation` is soundly reduced to the third-coordinate
transfer residual (by transitivity), and the transfer is proved necessary under a
representation.  The remaining forward steps are the transfer-level existence
(solvability + IVT) and the `t`-block strip (KLST block independence). -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_thirdCoordinateTransfer
#print axioms WakkerInfra.ProductPref.thirdCoordinateTransfer_of_additiveRep

/-! ## WP-C1.a forward step 2 — transfer-level existence.

`ThirdCoordinateTransfer` is decomposed (`thirdCoordinateTransfer_of_components`)
into a J2-witness supplier + `KzTransfer` + `StripTransfer`.  The J2 crossing is
theorem-backed by the WP-T IVT engine (`thirdCoordinateTransfer_J2_of_IVT`);
`KzTransfer` and `StripTransfer` are proved necessary under a representation. -/

#print axioms WakkerInfra.ProductPref.thirdCoordinateTransfer_of_components
#print axioms WakkerInfra.ProductPref.thirdCoordinateTransfer_J2_of_IVT
#print axioms WakkerInfra.ProductPref.kzTransfer_of_additiveRep
#print axioms WakkerInfra.ProductPref.stripTransfer_of_additiveRep

/-! ## WP-C1.a strip probe — `StripTransfer` is NOT an A1 consequence either.

Correcting the earlier "pure A1 consequence" framing: a concrete `n = 3`
A1-satisfying model violates `StripTransfer 0 1 2`.  So both transfer
sub-residuals (`KzTransfer`, `StripTransfer`) are genuine §IV.5 cancellation
content, necessary (proved) but not A1-derivable. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aStripProbe.strip_coordinateOrderIndependent
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aStripProbe.strip_not_stripTransfer
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aStripProbe.a1_does_not_imply_stripTransfer

/-! ## WP-C1.a endpoint — the hexagon as a named, proven-necessary residual.

Both probes (`Pcm`, `Pstrip`) refute A1 ⟹ hexagon and A1 ⟹ `StripTransfer`, so
the cross-pair §IV.5 cancellation content is not free.  The honest endpoint
bundles the three precisely-named, individually-sound pieces (J2 existence,
`KzTransfer`, `StripTransfer`) into one named residual `HexagonResidualData`,
proves the hexagon follows by a clean reduction
(`doubleCancellation_of_hexagonResidualData`), and proves the whole bundle is
necessary under any representation with adequate `t`-coverage
(`hexagonResidualData_of_additiveRep`).  The sanity capstone
`doubleCancellation_of_additiveRep_via_residual` confirms the residual is exactly
the right strength.  All foundational-only. -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_hexagonResidualData
#print axioms WakkerInfra.ProductPref.hexagonResidualData_of_additiveRep
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep_via_residual

/-! ## WP-C1.a forward step 3 — J2 transfer-level existence from the escape grid.

The `HexagonResidualData.j2` field is discharged from the §IV.2.6 Archimedean
escape grid (shared with WP-density/WP-B1), eliminating the explicit `t`-bracket:
`j2Exists_of_archimedeanEscape` (two-sided escape) and
`j2Exists_of_weaklyDescendingSeededAbove` (the leanest form — escape automatic
from a monotone grid + a single seed-above condition).  So J2 is NOT an
independent residual; the hexagon frontier is the two cross-pair residuals
(`KzTransfer`, `StripTransfer`) plus the shared escape grid.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.j2Exists_of_archimedeanEscape
#print axioms WakkerInfra.ProductPref.j2Exists_of_weaklyDescendingSeededAbove
#print axioms WakkerInfra.ProductPref.thirdCoordinateTransfer_of_escapeJ2_and_crossPair

/-! ## WP-C1.a minimal frontier — the hexagon from the escape grid + a single
    named cross-pair cancellation residual.

After J2 is escape-discharged, the entire genuine remaining content of the
hexagon is the single named `CrossPairCancellationData` (= `KzTransfer ∧
StripTransfer`), proved necessary under any representation
(`crossPairCancellationData_of_additiveRep`), with the hexagon following from
{J2 supplier + the bundle} (`doubleCancellation_of_J2_and_crossPair`) and the
sanity capstone confirming the right strength.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_additiveRep
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_J2_and_crossPair
#print axioms WakkerInfra.ProductPref.hexagonResidualData_of_J2_and_crossPair
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep_via_crossPair

/-! ## WP-B2 — equal-score faithfulness from a representation.

The Step-5 coverage residual's leaner content (equal additive scores ⟹ weak
preference) is immediate from any additive representation via `R.represents`, so
it hides nothing false.  Foundational-only. -/

#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.equalAdditiveScoreWeakPreference_of_additiveRep

/-! ## WP-DK — Debreu–Koopmans hard direction as a named midpoint residual.

The DK hard direction (per-coordinate concavity) is reduced to per-coordinate
*midpoint* concavity, with the Sierpiński upgrade fully theorem-backed
(Bernstein–Doetsch).  The genuine remaining DK §3 residual
`SliceMidpointConcavityCertificate` is proved **necessary** under any concave
representation (`sliceMidpointConcavity_of_concaveOn`), the forward step produces
the DK output from it (`dkHardDirection_of_sliceMidpointConcavity`), and the
sanity capstone confirms the residual is exactly the right strength.  All
foundational-only. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKConcavityEndpoint.sliceMidpointConcavity_of_concaveOn
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKConcavityEndpoint.dkHardDirection_of_sliceMidpointConcavity
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKConcavityEndpoint.dkHardDirection_of_concaveRep_via_midpoint

/-! ## WP0 — the unified canonical target and its bridge to public Wakker IV.2.7.

These are *conditional* on `OptionBResidualFrontier` (the open C1/B1/B2/density
residuals).  The audit shows the conditional construction has **no**
`_from_raw_axioms` seam — only foundational axioms and the §III.4.2 topology IVT
seams (WP-T), confirming the residual frontier is the *entire* remaining
obligation. -/

#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_from_structural_axioms_and_coordinateIndependence
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerConstruction_of_structural_axioms_and_coordinateIndependence

/-! ## WP-T — reach-axiom-free canonical target.

The §III.4.2 bracket reach axioms
`coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology` are
**eliminated**: the standard-sequence construction routes through the engine-A∘B
Archimedean escape (the genuine §IV.2.6 residual, carried in the enriched seed
germ).  This target audits at exactly `[propext, Classical.choice, Quot.sound]`
— no topology IVT seam, no `_from_raw_axioms` seam — so the *entire* remaining
obligation is the explicit residual frontier (C1 slices, B1 escape seed germ,
B2 coverage). -/

#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.coordinateOneStepBracketUpperReach_of_archimedeanEscape
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotStrictSeededAboveGridData_of_seedDataWithEscapeFamily
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_from_structural_axioms_reachAxiomFree

/-! ## Maximally-reduced capstone (Phase 76) for reference. -/

#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_of_seedGerm_and_analyticPivot

/-! ## Infrastructure roadmap — shared items X1, X3 (cheap prerequisites).

X1 (`sliceIndiffSelector_*`) re-exports `RestrictedSolvability` in the
`coordPref`-oriented forms the cross-pair (residual 1) and refinement-family
(residual 2) constructions consume; X3 (`exists_third_*`) supplies the
measuring-stick coordinate from `3 ≤ card ι`.  All foundational-only. -/

#print axioms WakkerInfra.ProductPref.sliceIndiffSelector_of_restrictedSolvability
#print axioms WakkerInfra.ProductPref.sliceIndiffSelector_symm_of_restrictedSolvability
#print axioms WakkerInfra.ProductPref.exists_third_coordinate
#print axioms WakkerInfra.ProductPref.exists_third_essential_coordinate

/-! ## Infrastructure roadmap — residual 2 step R2.1 (escape-grid midpoint refinement).

The sound bisection engine underneath the §IV.2.6 refinement family: from a strict
bracket around a target, restricted solvability yields an interior slice value
strictly between the endpoints (`coordStrictMid_of_restrictedSolvability`,
`coordStrictBetween_of_restrictedSolvability`).  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.coordStrictMid_of_restrictedSolvability
#print axioms WakkerInfra.ProductPref.coordStrictBetween_of_restrictedSolvability

/-! ## Infrastructure roadmap — residual 2 soundness gate (R2.2/R2.3 correction).

The gate REFUTES the single-strict-sequence target the infra roadmap first named
(`escapeGrid_singleSequence_target_is_unsound`: false in a model that HAS a
representation), and certifies the corrected refined mesh-family target sound
(`escapeGrid_meshFamily_target_is_sound`), with the whole chain above
rational-image coverage theorem-backed
(`escapeGrid_denseRange_of_rationalImage_and_extensionData`).  So residual 2's
genuine remaining input is `CoordinateRationalImageCertificate`.  Foundational-only. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridSoundnessGate.escapeGrid_singleSequence_target_is_unsound
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridSoundnessGate.escapeGrid_meshFamily_target_is_sound
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridSoundnessGate.escapeGrid_denseRange_of_rationalImage_and_extensionData

/-! ## Infrastructure roadmap — residual 3 (DK §3) midpoint soundness gate.

The gate confirms R3.2 is genuine content: per-slice quasiconcavity (R3.1,
theorem-backed from convex upper-contour) does NOT imply midpoint concavity
(`quasiconcave_does_not_imply_midpointConcave`: `Real.exp` is quasiconcave but
not midpoint-concave).  So `SliceMidpointConcavityCertificate` is a genuine named
residual (proved necessary in `OptionB_DKConcavityEndpoint`), not free from R3.1.
Foundational-only. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKMidpointProbe.exp_quasiconcave
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKMidpointProbe.exp_not_midpointConcave
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKMidpointProbe.quasiconcave_does_not_imply_midpointConcave

/-! ## Infrastructure roadmap — residual 3 (DK §3) step R3.2a: global quasiconcavity.

The sound forward entry point of the DK §3 argument: convex preference is
*equivalent* to global quasiconcavity of the additive sum on the product domain
(`additiveSum_quasiconcaveOn_of_convexPref` and its converse
`convexPref_of_additiveSum_quasiconcaveOn`).  This uses the global convex-
preference structure (not the insufficient per-slice content the probe refuted).
The remaining R3.2b gap is the upgrade from global sum-quasiconcavity to
per-summand midpoint concavity (the additive `n ≥ 3` separation).  Foundational-only. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKGlobalQuasiconcavity.additiveSum_quasiconcaveOn_of_convexPref
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKGlobalQuasiconcavity.convexPref_of_additiveSum_quasiconcaveOn

/-! ## Infrastructure roadmap — residual 3 (DK §3) step R3.2b core:
    cross-coordinate midpoint from global quasiconcavity.

The genuine DK §3 cross-pair midpoint consequence of global quasiconcavity (R3.2a):
at an equal-additive-contribution two-coordinate configuration, the joint midpoint
inequality holds (`twoCoord_midpoint_ge_of_quasiconcave`), equivalently the two
coordinates' midpoint deficits sum to ≥ 0 (`twoCoord_sum_midpointDeficit_nonneg`);
`twoCoord_midpoint_ge_of_convexPref` packages it directly from convex preference.
Isolating a single coordinate's deficit (per-summand midpoint concavity) is the
remaining `n ≥ 3` separation.  Foundational-only. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKTwoCoordMidpoint.twoCoord_midpoint_ge_of_quasiconcave
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKTwoCoordMidpoint.twoCoord_sum_midpointDeficit_nonneg
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKTwoCoordMidpoint.twoCoord_midpoint_ge_of_convexPref

/-! ## Infrastructure roadmap — residual 3 (DK §3) step R3.2b-tail:
    single-coordinate midpoint concavity from an affine companion.

The deficit separation: a midpoint-affine companion coordinate (zero deficit, the
standard-sequence measuring stick) turns the joint `δ_i + δ_j ≥ 0` into `δ_i ≥ 0`
(`midpointConcaveAt_of_affineCompanion`).  Reduces R3.2b-tail to the existence of
an `AffineCompanionCalibration` (`sliceMidpointConcavity_of_affineCompanionCalibration`)
— the standard-sequence measuring-stick existence, the genuine remaining `n ≥ 3`
DK §3 / Wakker §IV.2.6 work.  Foundational-only. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKAffineCompanion.midpointConcaveAt_of_affineCompanion
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKAffineCompanion.midpointConcaveAt_of_affineCompanion_convexPref
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKAffineCompanion.sliceMidpointConcavity_of_affineCompanionCalibration

/-! ## Infrastructure roadmap — residual 3 (DK §3) step R3.2b-tail:
    the standard-sequence measuring stick IS midpoint-affine.

`additiveRep_standardSequence_Vj_arithmetic` makes `R.V j` an arithmetic
progression on a standard-sequence grid, hence midpoint-affine on symmetric/
consecutive grid points (`standardSequence_Vj_midpointAffine`,
`standardSequence_consecutive_midpointAffine`,
`midpointAffineAt_of_standardSequence_indexMidpoint`).  So the affine companion of
R3.2b-tail is not an extra assumption — it is what a standard sequence is under a
representation.  This reduces `AffineCompanionCalibration` to the balanced
standard-sequence pair existence (the shared §IV.2.6 measuring-stick content, also
residual 2's R2.2 input).  Foundational-only. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKStandardStickAffine.standardSequence_Vj_midpointAffine
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKStandardStickAffine.standardSequence_consecutive_midpointAffine
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKStandardStickAffine.midpointAffineAt_of_standardSequence_indexMidpoint

/-! ## Infrastructure roadmap — shared §IV.2.6 measuring stick: extension data
    from continuity + unboundedness.

The one-step extension interface `CoordinateStandardSequenceExtensionData` (shared
by residual 2's R2.2 and residual 3's R3.2b-tail) is discharged from
`∀ i, Continuous (R.V i)` + `∀ i, CoordinateUtilityUnboundedCertificate R i` +
`3 ≤ card ι` (via the additive-representation IVT
`oneStepExtensible_of_continuity_unbounded` + the X3 companion selector).  Feeding
it forward, the residual-2 mesh family follows from {continuity + unboundedness +
rational image} (`coordinateUtilityRefinedMeshFamily_of_continuous_unbounded_rationalImage`).
Foundational-only. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBExtensionDataFromContinuity.coordinateStandardSequenceExtensionData_of_continuous_unbounded
#print axioms WakkerRoadmap.CertificateChecklist.OptionBExtensionDataFromContinuity.coordinateRationalRefinementBisection_of_continuous_unbounded_rationalImage
#print axioms WakkerRoadmap.CertificateChecklist.OptionBExtensionDataFromContinuity.coordinateUtilityRefinedMeshFamily_of_continuous_unbounded_rationalImage

/-! ## Infrastructure roadmap — shared §IV.2.6 measuring stick: rational image
    (hence residual-2 mesh family) from connectedness + continuity + unboundedness.

The last named open input of the residual-2/3 §IV.2.6 frontier,
`CoordinateRationalImageCertificate`, is discharged from the topology bundle:
`ConnectedCoordinates` is free for ℝ (`connectedCoordinates_realProduct`), so
surjectivity — hence rational image — follows from continuity + unboundedness
(`coordinateRationalImage_of_continuous_unbounded`).  Residual 2's mesh family then
follows from {continuity + unboundedness + solvability}
(`coordinateUtilityRefinedMeshFamily_of_continuous_unbounded`), and dense range too
(`coordinateDenseRange_of_continuous_unbounded`).  So the entire residual-2/3
§IV.2.6 frontier reduces to the topology bundle (continuity + unboundedness).
Foundational-only. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBRationalImageFromTopology.coordinateRationalImage_of_continuous_unbounded
#print axioms WakkerRoadmap.CertificateChecklist.OptionBRationalImageFromTopology.coordinateDenseRange_of_continuous_unbounded
#print axioms WakkerRoadmap.CertificateChecklist.OptionBRationalImageFromTopology.coordinateUtilityRefinedMeshFamily_of_continuous_unbounded

/-! ## Infrastructure roadmap — R1.1 groundwork: the strip residual is
    level-independent.

`tri` overwrites coordinate `t`, so the background's `t`-value is irrelevant
(`tri_bg_update_t`); hence `StripTransfer`'s "to background level `a t`" is in fact
"to **every** level `c`" (`stripTransfer_allLevels`) and transports between any two
levels (`stripTransfer_betweenLevels`).  This pins `StripTransfer` as exactly
`t`-block independence at all levels — the genuine KLST block-independence target
for the §IV.5 forward construction.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tri_bg_update_t
#print axioms WakkerInfra.ProductPref.stripTransfer_allLevels
#print axioms WakkerInfra.ProductPref.stripTransfer_betweenLevels

/-! ## Infrastructure roadmap — R1.1 groundwork: `StripTransfer` from the standard
    KLST separability condition `TBlockWeakIndependent`.

`TBlockWeakIndependent` (weakPref `t`-block independence — the standard KLST
separability form) implies the indifference strip
(`stripTransfer_of_tBlockWeakIndependent`), is necessary under a representation
(`tBlockWeakIndependent_of_additiveRep`), and is level-independent
(`tBlockWeakIndependent_allLevels`).  This pins the `StripTransfer` half of
`CrossPairCancellationData` to the standard separability vocabulary — the clean
§IV.5 forward-construction target.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.stripTransfer_of_tBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.tBlockWeakIndependent_of_additiveRep
#print axioms WakkerInfra.ProductPref.tBlockWeakIndependent_allLevels

/-! ## Infrastructure roadmap — R1.1: `KzTransfer` is NOT an A1 consequence (probe).

Completing the soundness characterization of `CrossPairCancellationData =
KzTransfer ∧ StripTransfer`: a concrete `n = 3` A1-satisfying model `Pkz`
(utility `gKz (x 0) (x 1) + x 2`, comonotone but Thomsen-violating) violates
`KzTransfer 0 1 2` (`kz_not_kzTransfer`, audits `[propext]`).  So BOTH halves of
the §IV.5 residual are machine-checked non-A1-derivable (matching the
`StripTransfer` probe `Pstrip`), and both are proved necessary under a
representation.  Foundational-only. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aKzProbe.kz_coordinateOrderIndependent
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aKzProbe.kz_not_kzTransfer
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aKzProbe.a1_does_not_imply_kzTransfer

/-! ## Infrastructure roadmap — R1.1 forward step: `KzTransfer` from an anchor +
    `j`-block independence.

Paralleling the `StripTransfer` reduction: `KzTransfer`'s conclusion is
independent of `x,y,r` and varies only in the common `j`-value, so it follows from
the anchor transfer (`KzAnchorTransfer`, at `z := x`) plus standard `j`-block
independence (`JBlockWeakIndependent`), via
`kzTransfer_of_anchor_and_jBlock`.  The anchor is a specialization of `KzTransfer`
(`kzAnchorTransfer_of_kzTransfer`), and `j`-block independence is necessary
(`jBlockWeakIndependent_of_additiveRep`).  So BOTH halves of
`CrossPairCancellationData` are now reduced to standard KLST block-independence
conditions plus small anchor cores.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.kzTransfer_of_anchor_and_jBlock
#print axioms WakkerInfra.ProductPref.kzAnchorTransfer_of_kzTransfer
#print axioms WakkerInfra.ProductPref.jBlockWeakIndependent_of_additiveRep

/-! ## Infrastructure roadmap — R1.1 anchor core + capstone:
    `CrossPairCancellationData` from the three KLST block-independence conditions.

The anchor core `KzAnchorTransfer` is discharged from `k`-block independence
(`kzAnchorTransfer_of_kBlock`), so `KzTransfer` follows from `k`- + `j`-block
independence (`kzTransfer_of_kBlock_and_jBlock`).  Combined with `StripTransfer`
⟸ `t`-block independence, the **full `CrossPairCancellationData`** follows from the
three standard KLST block conditions (`crossPairCancellationData_of_blockIndependence`),
each proved necessary; the sanity capstone
(`crossPairCancellationData_of_additiveRep_via_blocks`) and the hexagon route
(`doubleCancellation_of_blockIndependence_and_J2`) confirm the strength.  So R1.1's
cross-pair residual is fully reduced to Wakker's coordinate-independence input set.
Foundational-only. -/

#print axioms WakkerInfra.ProductPref.kzAnchorTransfer_of_kBlock
#print axioms WakkerInfra.ProductPref.kBlockWeakIndependent_of_additiveRep
#print axioms WakkerInfra.ProductPref.kzTransfer_of_kBlock_and_jBlock
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_blockIndependence
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_additiveRep_via_blocks
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_blockIndependence_and_J2

/-! ## Infrastructure roadmap — final piece: A1 gives the single-coordinate-
    difference part of the KLST block conditions.

A1 (`CoordinateOrderIndependent`) is exactly background-independence of single-
coordinate `≽`-order.  Each KLST block-independence condition is a *two-coordinate*-
difference statement.  Restricting to its **single-coordinate-difference** sub-form
collapses the comparison to a `coordPref`, and shifting the third coordinate's
common value is a background change A1 absorbs.  So A1 yields the restricted
forms (`tBlockWeakIndependentRestricted_of_a1`, `kBlockWeakIndependentRestricted_of_a1`,
`jBlockWeakIndependentRestricted_of_a1`); the irreducible Thomsen residue is
precisely the two-coordinate-difference part — the genuine §IV.5 `n ≥ 3` content
the probes confirm A1 cannot give.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tri_eq_update_k
#print axioms WakkerInfra.ProductPref.tri_eq_update_j
#print axioms WakkerInfra.ProductPref.tBlockWeakIndependentRestricted_of_a1
#print axioms WakkerInfra.ProductPref.kBlockWeakIndependentRestricted_of_a1
#print axioms WakkerInfra.ProductPref.jBlockWeakIndependentRestricted_of_a1

/-! ## Infrastructure roadmap — final piece: the diagonal Thomsen residue
    (the irreducible two-coordinate-difference content).

Each KLST block-independence condition decomposes into:
* two single-coord-diff restrictions (where the two profiles agree on one of the
  two block coordinates), each A1-derivable
  (`tBlockWeakIndependentRestricted{,J}_of_a1`,
  `kBlockWeakIndependentRestricted{,C}_of_a1`,
  `jBlockWeakIndependentRestricted{,C}_of_a1`);
* the two-coord-diff DIAGONAL RESIDUE (`TBlockDiagonalResidue`,
  `KBlockDiagonalResidue`, `JBlockDiagonalResidue`), each proved necessary
  (`*_of_additiveRep`).

The three decomposition theorems (`tBlockWeakIndependent_of_decomposition`,
`kBlockWeakIndependent_of_decomposition`, `jBlockWeakIndependent_of_decomposition`)
recover the full block conditions from {A1 + diagonal residue}; the final-piece
capstone `crossPairCancellationData_of_a1_and_diagonalResidues` derives the entire
`CrossPairCancellationData` from A1 on every coordinate plus the three diagonal
residues — and `crossPairCancellationData_of_additiveRep_via_diagonalResidues`
confirms strength under a representation.  This is the sharpest possible
characterization of R1.1's open content: the two-coordinate-difference Thomsen
residue, with everything else discharged from A1 by foundational-only proofs.
Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockWeakIndependentRestrictedJ_of_a1
#print axioms WakkerInfra.ProductPref.kBlockWeakIndependentRestrictedC_of_a1
#print axioms WakkerInfra.ProductPref.jBlockWeakIndependentRestrictedC_of_a1
#print axioms WakkerInfra.ProductPref.tBlockWeakIndependent_of_decomposition
#print axioms WakkerInfra.ProductPref.kBlockWeakIndependent_of_decomposition
#print axioms WakkerInfra.ProductPref.jBlockWeakIndependent_of_decomposition
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_additiveRep
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_of_additiveRep
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_of_additiveRep
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_a1_and_diagonalResidues
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_additiveRep_via_diagonalResidues

/-! ## Infrastructure roadmap — final piece: diagonal residue symmetry and
    self-consistency.

Each diagonal residue is bidirectional in its level/coordinate-shift parameter
(`tBlockDiagonalResidue_symm`, `kBlockDiagonalResidue_symm`,
`jBlockDiagonalResidue_symm`); chaining is automatic
(`tBlockDiagonalResidue_chain`); and the indifference form follows directly
(`tBlockDiagonalResidue_indiff`).  These confirm the diagonal residues are stated
exactly right — no gratuitous asymmetry, the sharpest form of Wakker §IV.5
Thomsen content.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_symm
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_symm
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_symm
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_chain
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff

/-! ## Infrastructure roadmap — final piece: diagonal residues are
    background-independent off `{j,k,t}`.

`tri_eq_of_agreeOff`: backgrounds that agree off `{j,k,t}` produce identical
`tri` profiles (the `j`,`k`,`t`-values are overwritten).  Hence each diagonal
residue's truth is genuinely a property of the off-`{j,k,t}` background only
(`tBlockDiagonalResidue_apply_of_agreeOff`,
`kBlockDiagonalResidue_apply_of_agreeOff`,
`jBlockDiagonalResidue_apply_of_agreeOff`): an application at one background
transports directly to any agreeing background.  This isolates exactly which
background data the residues consume — useful structural information for the
§IV.5 forward construction.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tri_eq_of_agreeOff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_apply_of_agreeOff
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_apply_of_agreeOff
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_apply_of_agreeOff

/-! ## Infrastructure roadmap — final piece: Thomsen-style chaining of the
    diagonal residues.

Under `IsWeakOrder`, each diagonal residue chains as an indifference and is
level-invariant: an indifference at one shift parameter forces it at every other.
The iff forms (`tBlockDiagonalResidue_indiff_iff`, `kBlockDiagonalResidue_indiff_iff`,
`jBlockDiagonalResidue_indiff_iff`) and level-invariance forms
(`tBlockDiagonalResidue_levelInvariant`, etc.) confirm the diagonal residues encode
the genuine equal-trade-off content the §IV.5 measuring-stick argument exploits —
not merely one-way preservation.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_iff
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_indiff
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_indiff_iff
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_indiff
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_indiff_iff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_levelInvariant
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_levelInvariant
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_levelInvariant

/-! ## Infrastructure roadmap — final piece: diagonal residues are equivalent
    under coordinate-role permutation.

`tri_perm_jk` and `tri_perm_kt` give pure `Function.update_comm` reassociations of
the `tri` profile under coordinate-role swaps.  Hence
`kBlockDiagonalResidue_iff_tBlock_perm` shows `KBlockDiagonalResidue P j k t` is
literally `TBlockDiagonalResidue P j t k` — the same Thomsen statement applied to
the permuted coordinate triple `(j, t, k)`.  So the three diagonal residues are
not three independent statements; K-diag is a permutation-instance of T-diag.
Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tri_perm_jk
#print axioms WakkerInfra.ProductPref.tri_perm_kt
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_iff_tBlock_perm

/-! ## Infrastructure roadmap — final piece: (j,t) coordinate-role swap on tri.

`tri_perm_jt` proves `tri a j k t u v c = tri a t k j c v u` pointwise via
`funext` — the `(j,t)` role swap.  Together with `tri_perm_jk` and `tri_perm_kt`
(`OptionB_C1aDiagonalPermutation.lean`), this gives every transposition on the
three coordinate roles, the foundation for showing the diagonal residues are
permutation-instances of one another.  And `jBlockDiagonalResidue_iff_tBlock_perm`
proves `JBlockDiagonalResidue P j k t ↔ TBlockDiagonalResidue P t k j` — the
J-diagonal is also a permutation-instance of T-diag.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tri_perm_jt
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_iff_tBlock_perm

/-! ## Infrastructure roadmap — final piece: R1.1 unified capstone
    `CrossPairCancellationData` from A1 + a single Thomsen residue at three
    coordinate triples.

The full R1.1 reduction in its sharpest form: A1 on every coordinate, plus the
**single** `TBlockDiagonalResidue` instantiated at the three permuted coordinate
triples `(j,k,t)`, `(j,t,k)`, `(t,k,j)`, suffices for `CrossPairCancellationData`
(`crossPairCancellationData_of_a1_and_oneThomsenResidue`).  Sanity capstone under
a representation: `crossPairCancellationData_of_additiveRep_via_oneThomsen`.
Foundational-only. -/

#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_a1_and_oneThomsenResidue
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_additiveRep_via_oneThomsen

/-! ## Infrastructure roadmap — final piece: the diagonal residue preserves
    strict preference (full trade-off relation transfer).

The single Thomsen residue `TBlockDiagonalResidue` (and its K- and J-permutation
instances) preserves not just `≽` but also strict preference `≻`
(`tBlockDiagonalResidue_strict`, `kBlockDiagonalResidue_strict`,
`jBlockDiagonalResidue_strict`); the iff form
(`tBlockDiagonalResidue_strict_iff`) makes this level-equivalent.  Combined with
the prior level-invariance for `≽` and `∼`, this confirms the diagonal residue
transfers the **full trade-off relation** — exactly the Wakker IV.2.5 trade-off-
consistency content for the cross-pair on the third coordinate.  Foundational-
only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_iff
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_strict
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_strict

/-! ## Infrastructure roadmap — final piece: complete pairwise equivalence of
    the three diagonal residues.

`tBlockDiagonalResidue_iff_kBlock_perm` (T-diag ↔ K-diag with k↔t swapped) and
`tBlockDiagonalResidue_iff_jBlock_perm` (T-diag ↔ J-diag with t↔j swapped) give
the inverse permutation directions; `kBlockDiagonalResidue_iff_jBlock_perm`
chains them to give K-diag ↔ J-diag.  So the three diagonals form a complete
`S_3`-equivariant family under coordinate-role permutation — a single Thomsen
statement applied at the six role-assignments of `(j,k,t)` (modulo trivial
relabelings).  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_iff_kBlock_perm
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_iff_jBlock_perm
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_iff_jBlock_perm

/-! ## Infrastructure roadmap — final piece: antisymmetry / rigidity of the
    diagonal Thomsen residue across levels.

The diagonal residue forces the trade-off relation between two two-coordinate-
different profiles to be a single rigid relation, level-invariant: a `≽` at one
shift parameter combined with a reverse `≽` at any other forces both to be
indifferences (`tBlockDiagonalResidue_antisym`, `kBlockDiagonalResidue_antisym`,
`jBlockDiagonalResidue_antisym`).  Consequently a strict preference at one level
rules out the reverse at every other (`tBlockDiagonalResidue_strict_one_direction`).
This is the rigidity content classical Wakker §IV.2.5 trade-off consistency
encodes.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_antisym
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_one_direction
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_antisym
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_antisym

/-! ## Infrastructure roadmap — final piece: trichotomy classification of the
    diagonal Thomsen residue.

Under the diagonal residue + `IsWeakOrder`, the trade-off relation between two
two-coordinate-different profiles falls into exactly one of three uniform
classes across all levels — uniform `≻`, uniform `∼`, or uniform `≺`
(`tBlockDiagonalResidue_trichotomy`, `kBlockDiagonalResidue_trichotomy`,
`jBlockDiagonalResidue_trichotomy`).  This formalizes the Wakker IV.2.5
trichotomy: trade-off comparisons are level-independent and totally classified.
Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trichotomy
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_trichotomy
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_trichotomy

/-! ## Infrastructure roadmap — final piece: transitivity of the diagonal
    trichotomy classes.

The trichotomy classes (`OptionB_C1aDiagonalTrichotomy.lean`) compose by
transitivity: chaining two uniform `≽` (or `∼`, or `≻`) gives a uniform `≽` (or
`∼`, or `≻`) on the chained pair (`tBlockDiagonalResidue_trans_weakPref`,
`tBlockDiagonalResidue_trans_indiff`, `tBlockDiagonalResidue_trans_strict`).
This formalizes Wakker §IV.2.5's claim that the trade-off relation forms a
genuine total preorder on the trade-off space.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_weakPref
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_indiff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_strict

/-! ## Infrastructure roadmap — final piece: equivalence-relation structure of
    the diagonal indifference class.

The level-uniform indifference relation on two-coord-different profile pairs is
reflexive, symmetric, and transitive — a full equivalence relation
(`tBlockDiagonalResidue_indiff_uniform_refl`,
`tBlockDiagonalResidue_indiff_uniform_symm`,
`tBlockDiagonalResidue_indiff_uniform_trans`); the strict relation is
irreflexive (`tBlockDiagonalResidue_strict_uniform_irrefl`).  Together with the
prior trichotomy + transitivity, this gives a full preorder-with-equivalence
structure on the trade-off space — the genuine Wakker §IV.2.5 trade-off-
consistency content.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_uniform_symm
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_uniform_trans
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_uniform_refl
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_uniform_irrefl

/-! ## Infrastructure roadmap — final piece: pairwise mutual exclusivity of the
    trichotomy classes.

The three trichotomy classes (uniform `≻`, uniform `∼`, uniform reversed `≻`)
are **pairwise mutually exclusive**: any two are jointly inconsistent
(`tBlockDiagonalResidue_strict_indiff_exclusive`,
`tBlockDiagonalResidue_strict_dual_exclusive`,
`tBlockDiagonalResidue_indiff_strict_dual_exclusive`); the packaged form
`tBlockDiagonalResidue_trichotomy_unique` makes "exactly one class" precise.
Combined with the prior exhaustive trichotomy, this gives the sharpest possible
total-classification statement.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_indiff_exclusive
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_dual_exclusive
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_strict_dual_exclusive
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trichotomy_unique

/-! ## Infrastructure roadmap — final piece: single-level → uniform-class
    determination.

Under the diagonal residue, a single-level observation determines the entire
trichotomy class: a strict preference at one level forces uniform strict at all
levels (`tBlockDiagonalResidue_uniformStrict_of_pointStrict`), and similarly for
indifference (`…_uniformIndiff_of_pointIndiff`) and reversed strict
(`…_uniformStrictBwd_of_pointStrictBwd`).  This makes the trichotomy class a
well-defined function of just the profile pair — independent of the sampling
level.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_uniformStrict_of_pointStrict
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_uniformIndiff_of_pointIndiff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_uniformStrictBwd_of_pointStrictBwd

/-! ## Infrastructure roadmap — final piece: mixed-class transitivity of the
    diagonal trichotomy.

`OptionB_C1aDiagonalTransitivity.lean` proved same-class transitivity (`≻∘≻`,
`∼∘∼`, `≽∘≽`) and `OptionB_C1aDiagonalSetoid.lean` proved indifference is
reflexive/symmetric/transitive.  This piece fills the **cross-class** corner of
the preorder-with-equivalence calculus: chaining a uniform strict relation with
a uniform indifference (in either order) forces uniform strict
(`tBlockDiagonalResidue_trans_strict_indiff`,
`tBlockDiagonalResidue_trans_indiff_strict`); chaining a uniform `≽` with a
uniform indifference (in either order) forces uniform `≽`
(`tBlockDiagonalResidue_trans_weakPref_indiff`,
`tBlockDiagonalResidue_trans_indiff_weakPref`).  Together with the prior
same-class transitivity, this completes the total-preorder-modulo-equivalence
calculus on the trichotomy classes — the standard preorder structure of the
Wakker §IV.2.5 trade-off space.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_strict_indiff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_indiff_strict
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_weakPref_indiff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_indiff_weakPref

/-! ## Infrastructure roadmap — final piece: indifference-substitution rules
    for the diagonal trichotomy.

The mixed-class transitivity from `OptionB_C1aDiagonalMixedTrans.lean` is
packaged in the standard "preorder respects equivalence" substitution shape:
substituting either endpoint by an indifferent profile pair preserves the
trichotomy class.  Left/right/both substitution forms cover all three
relations:
* uniform `≻`: `tBlockDiagonalResidue_strict_subst_{left,right,both}`,
* uniform `≽`: `tBlockDiagonalResidue_weakPref_subst_{left,right,both}`,
* uniform `∼`: `tBlockDiagonalResidue_indiff_subst_{left,right,both}`.

This is exactly the "preorder on the indifference quotient" content — the
trichotomy class is well-defined on the trade-off space modulo indifference,
in the operationally usable substitution-rule shape.  Foundational-only. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_subst_left
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_subst_right
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_weakPref_subst_left
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_weakPref_subst_right
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_subst_left
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_subst_right
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_subst_both
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_weakPref_subst_both
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_subst_both

/-! ## Infrastructure roadmap — final piece: additive-arithmetic characterization
    of the diagonal trichotomy.

Under an additive representation, the diagonal residue's abstract trichotomy
*coincides* with the sign of the cross-coordinate utility difference
`(V_j x + V_k r) − (V_j z + V_k p)` — the `t`-level utility and the off-`{j,k,t}`
background cancel as an arithmetic identity.  Point and uniform forms for strict
(`tBlockDiagonalResidue_pointStrict_iff_score`,
`tBlockDiagonalResidue_uniformStrict_iff_score`) and indifference
(`tBlockDiagonalResidue_pointIndiff_iff_score`,
`tBlockDiagonalResidue_uniformIndiff_iff_score`); the capstone
`tBlockDiagonalResidue_trichotomy_matches_score` packages all three classes as
`lt_trichotomy` on the cross-sums.  This is a genuine soundness/consistency
result: it confirms the structurally-derived abstract trichotomy IS the additive-
order trichotomy under any representation, and exhibits the level-invariance as a
cancellation.  Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_pointStrict_iff_score
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_pointIndiff_iff_score
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_uniformStrict_iff_score
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_uniformIndiff_iff_score
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trichotomy_matches_score

/-! ## Infrastructure roadmap — final piece: the classical hexagon from A1 + one
    Thomsen residue + a J2 supplier.

The classical-vocabulary endpoint of R1.1: the standard additive-conjoint hexagon
`DoubleCancellation P j k` follows from A1 on `{j,k,t}`, the single Thomsen residue
`TBlockDiagonalResidue` at the three permuted triples `(j,k,t)`, `(j,t,k)`,
`(t,k,j)`, and a J2 transfer-level supplier (escape-grid-dischargeable).  Composes
`crossPairCancellationData_of_a1_and_oneThomsenResidue` with
`doubleCancellation_of_J2_and_crossPair`
(`doubleCancellation_of_a1_and_oneThomsenResidue`).  The sanity capstone
`doubleCancellation_of_additiveRep_via_oneThomsen` confirms the strength: under a
representation with adequate `t`-coverage, the one-Thomsen route recovers the
hexagon.  So the genuinely-open content of the entire classical hexagon is now
exactly the single Thomsen residue.  Audit `[propext, Classical.choice,
Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_a1_and_oneThomsenResidue
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep_via_oneThomsen

/-! ## Grid-Thomsen route — the R1.1 closure as a `sorry`-free reduction.

The grid-Thomsen attack on R1.1 (`OptionB_C1aGridThomsen.lean`; full per-
declaration table: `OptionB_C1aGridThomsenStatusTable.md`) reduces the
`GridThomsenClosure` to a minimal cross-pair frontier with **all** order theory,
free calibration cases, grid assembly, and continuum/IVT existence content
theorem-backed at `[propext, Classical.choice, Quot.sound]`.  The module is now
**`sorry`-free**; the genuinely-open content is isolated as named §IV.5/§IV.2.6
inputs (the equal-spacing *matching* residuals + the Archimedean *reach*
brackets), each soundness-gated and machine-checked non-A1-derivable (the strip
and Kz probes).

### Headline closure (theorem-backed mod the named inputs).
The closure follows from the calibrated grid + the topology bundle + the named
cross-pair inputs.  No `sorryAx`. -/

#print axioms WakkerInfra.ProductPref.gridThomsenClosure_of_calibratedGrid
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_of_calibratedGrid
#print axioms WakkerInfra.ProductPref.gridDiagonalLevelMoveResidual_of_calibratedGrid
#print axioms WakkerInfra.ProductPref.calibrationOffAxisOneStep_of_calibratedGrid
#print axioms WakkerInfra.ProductPref.calibrationAllBackgrounds_of_calibratedGrid

/-! ### Order-theory backbone (theorem-backed; no §IV.5 content). -/

#print axioms WakkerInfra.ProductPref.gridThomsenClosure_of_additiveRep
#print axioms WakkerInfra.ProductPref.gridThomsenClosure_of_gridDiagonalStep
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_of_additiveRep
#print axioms WakkerInfra.ProductPref.gridTBlockDiagonalResidue_of_closure

/-! ### Calibration layer — free axis cases + free calibration-level cases.

Axis cases free by definitional unfolding (`spaced_j`/`spaced_k` already supply
them).  Calibration-level cases at `st`/`rt` free from full/interior calibration
by pure weak order (no A1, no solvability).  Off-axis induction free
(`spaced_j`/`spaced_k` as base case + the atomic one-step shift). -/

#print axioms WakkerInfra.ProductPref.calibrationAllBackgrounds_of_axisCases_and_interior
#print axioms WakkerInfra.ProductPref.calibrationAllBackgrounds_of_additiveRep
#print axioms WakkerInfra.ProductPref.calibrationInteriorBackgrounds_of_offAxisOneStep
#print axioms WakkerInfra.ProductPref.calibrationInteriorBackgrounds_of_additiveRep
#print axioms WakkerInfra.ProductPref.calibrationOffAxisOneStep_of_additiveRep
#print axioms WakkerInfra.ProductPref.interiorDiagonalStep_st_of_allBackgrounds
#print axioms WakkerInfra.ProductPref.interiorDiagonalStep_rt_of_interiorBackgrounds
#print axioms WakkerInfra.ProductPref.interiorDiagonalStep_at_calibrationLevels

/-! ### Off-axis one-step shift (§D.3a-fwd) — genuine forward construction.

The atomic one-step off-axis calibration shift is theorem-backed via the IVT
crossing `tCompensationExists_of_topology` plus the named forward data
`CalibrationOffAxisForwardData` (the §IV.2.6 reach brackets + the two cross-pair
matching residuals, each soundness-gated). -/

#print axioms WakkerInfra.ProductPref.tCompensationExists_of_topology
#print axioms WakkerInfra.ProductPref.calibrationOffAxisForwardData_of_additiveRep
#print axioms WakkerInfra.ProductPref.calibrationOffAxisOneStep_of_topology_and_forwardData

/-! ### Off-cal level move (§D.3f–h) — genuine forward construction.

The off-calibration diagonal step is theorem-backed via the same factoring: the
`j`-half existence by IVT (`offCalJHalf_of_IVT`,
`offCalJHalf_of_topology_and_bracket`) + the matching residual
`OffCalCompensationMatch` (necessary under a rep, characterized as the canonical
KLST `t`-block separability via `offCalCompensationMatch_of_calibration_and_tBlock`). -/

#print axioms WakkerInfra.ProductPref.offCalJHalf_of_IVT
#print axioms WakkerInfra.ProductPref.offCalJHalf_of_topology_and_bracket
#print axioms WakkerInfra.ProductPref.offCalKHalf_of_IVT
#print axioms WakkerInfra.ProductPref.offCalJBracket_of_additiveRep
#print axioms WakkerInfra.ProductPref.offCalCompensationMatch_of_additiveRep
#print axioms WakkerInfra.ProductPref.offCalCompensationMatch_of_calibration_and_tBlock
#print axioms WakkerInfra.ProductPref.matchedOffCalCompensation_of_additiveRep
#print axioms WakkerInfra.ProductPref.matchedOffCalCompensation_of_jHalfExists_and_match
#print axioms WakkerInfra.ProductPref.gridDiagonalStepOffCal_of_matchedCompensation
#print axioms WakkerInfra.ProductPref.gridDiagonalStepOffCal_of_jHalfExists_and_match
#print axioms WakkerInfra.ProductPref.gridDiagonalStepOffCal_of_topology_bracket_and_match
#print axioms WakkerInfra.ProductPref.gridDiagonalStepOffCal_of_calibratedGrid
#print axioms WakkerInfra.ProductPref.gridDiagonalStepOffCal_of_additiveRep

/-! ### R1.1a — calibrated grid construction from structural axioms + topology bundle. -/

#print axioms WakkerInfra.ProductPref.calibratedJKGrid_of_seedData
#print axioms WakkerInfra.ProductPref.calibratedGridSeedData_extenders_of_additiveRep
#print axioms WakkerInfra.ProductPref.gridJ_injective_of_strictSteps
#print axioms WakkerInfra.ProductPref.gridK_injective_of_strictSteps
#print axioms WakkerInfra.ProductPref.calibratedJKGrid_with_injectivity_of_seedData
#print axioms WakkerInfra.ProductPref.calibratedOneStepSeam_of_topology
#print axioms WakkerInfra.ProductPref.calibratedJKGrid_of_structuralAxioms_and_topology
#print axioms WakkerInfra.ProductPref.calibratedJKGrid_of_structuralAxioms

/-! ### Grid-Thomsen frontier capstone (§F.1) — bundled named inputs ⇒ closure ⇒
    grid-restricted `TBlockDiagonalResidue`.

`GridThomsenForwardFrontier` bundles the genuine §IV.5/§IV.2.6 named inputs (the
off-axis forward data + the level-move reach bracket + the equal-spacing matching
residual) into one object, proved necessary under a rep
(`gridThomsenForwardFrontier_of_additiveRep`).  The capstones produce the
`GridThomsenClosure` (`gridThomsenClosure_of_frontier`) and then the grid-restricted
`TBlockDiagonalResidue` (`gridTBlockDiagonalResidue_of_frontier`) — the R1.1
endpoint in the project's downstream vocabulary, `sorry`-free at
`[propext, Classical.choice, Quot.sound]` modulo the bundled frontier. -/

#print axioms WakkerInfra.ProductPref.gridThomsenForwardFrontier_of_additiveRep
#print axioms WakkerInfra.ProductPref.gridThomsenClosure_of_frontier
#print axioms WakkerInfra.ProductPref.gridTBlockDiagonalResidue_of_frontier

/-! ### R1.2 transport (§ `OptionB_C1aGridTransport.lean`) — grid-restricted ⟹
    full `TBlockDiagonalResidue`.

The grid-restricted residue (from the grid-Thomsen frontier capstone) is lifted
to the **full** `TBlockDiagonalResidue P j k t` — by pure weak order — modulo the
single named level-stable grid-coverage residual `StableGridIndifferentCover`
(proved necessary under a rep modulo grid-utility reach, the §IV.2.6 density
content).  `tBlockDiagonalResidue_of_frontier_and_stableCover` composes the whole
R1.1+R1.2 grid route to the residue the R1.1 unified capstone consumes (at the
three permuted triples), `sorry`-free at `[propext, Classical.choice, Quot.sound]`
modulo the bundled frontier + stable cover. -/

#print axioms WakkerInfra.ProductPref.stableGridIndifferentCover_of_additiveRep
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_gridRestricted_and_stableCover
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_frontier_and_stableCover

/-! ### Grid route ⟹ classical hexagon (§E of `OptionB_C1aGridTransport.lean`).

The full `TBlockDiagonalResidue P j k t` over **all** backgrounds is produced from
a background-indexed grid-route family (`tBlockDiagonalResidue_of_gridRouteData`),
and feeding it at the three coordinate role-assignments `(j,k,t)`, `(j,t,k)`,
`(t,k,j)` into the unified one-Thomsen hexagon capstone yields the classical
additive-conjoint hexagon `DoubleCancellation P j k` (`doubleCancellation_of_gridRoute`).
So the entire grid-Thomsen + transport route reaches the classical hexagon,
`sorry`-free at `[propext, Classical.choice, Quot.sound]`, modulo the named
§IV.5/§IV.2.6 inputs (forward frontiers + stable covers bundled per-background +
the J2 supplier), all soundness-gated and A1-non-derivable. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_gridRouteData
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_gridRoute

/-! ### Grid route ⟹ hexagon with J2 escape-discharged (§F of `OptionB_C1aGridTransport.lean`).

The J2 transfer-level supplier is no longer a bare hypothesis: it is discharged
from the §IV.2.6 Archimedean escape grid in coordinate `t` (`J2EscapeData` ⟹
`j2Supplier_of_escapeData`, via `j2Exists_of_archimedeanEscape`).  The capstone
`doubleCancellation_of_gridRoute_escapeJ2` produces the classical hexagon
`DoubleCancellation P j k` from exactly the named §IV.5/§IV.2.6 inputs — the three
grid-route families (forward frontiers + stable covers) and the J2 escape grid —
all soundness-gated and A1-non-derivable.  `sorry`-free at
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.j2Supplier_of_escapeData
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_gridRoute_escapeJ2

/-! ### Unified single-bundle grid-route interface (§G of `OptionB_C1aGridTransport.lean`).

The grid route's entire frontier is packaged into one object `UnifiedGridRouteData`
(the three per-triple grid-route families + the J2 escape grid), and
`doubleCancellation_of_unifiedGridRoute` produces the classical hexagon
`DoubleCancellation P j k` from that single bundle.  This is an *interface*
reduction (four inputs → one), not a mathematical merge: the three Thomsen facts at
`(j,k,t)`, `(j,t,k)`, `(t,k,j)` are genuinely distinct cross-pair cancellation
conditions and do not collapse.  `sorry`-free at `[propext, Classical.choice,
Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_unifiedGridRoute

/-! ### `OffCalJBracket` discharged from the §IV.2.6 escape grid (§H of
    `OptionB_C1aGridTransport.lean`).

The level-move `j`-half reach bracket is **not** a separate residual: it is
discharged from a strict Archimedean `t`-standard-sequence escaping the reference
(`OffCalJEscapeGrid` ⟹ `offCalJBracket_of_escapeGrid`), via the project's
`archimedean_reach_above`/`below` — **pure order theory** (no topology, no IVT, no
A1; audit `[propext, Quot.sound]`).  `gridThomsenForwardFrontier_of_escapeGrid`
then builds the forward frontier with the bracket field derived from the escape
grid rather than assumed.  So the bracket joins J2 as escape-grid-discharged: the
grid route's reach content is pinned to the canonical §IV.2.6 escape grid, leaving
the genuine open frontier as the cross-pair *matching* residuals + the stable
cover + the escape grids. -/

#print axioms WakkerInfra.ProductPref.offCalJBracket_of_escapeGrid
#print axioms WakkerInfra.ProductPref.gridThomsenForwardFrontier_of_escapeGrid

/-! ### End-to-end route data with reach bracket escape-discharged (§I of
    `OptionB_C1aGridTransport.lean`).

`TBlockGridRouteDataEsc` carries the §IV.2.6 escape grid per background (deriving
the reach bracket) instead of an assumed bracket; `tBlockDiagonalResidue_of_gridRouteDataEsc`
produces the full residue from it, and `doubleCancellation_of_unifiedGridRouteEsc`
reaches the classical hexagon `DoubleCancellation P j k` with **every**
Archimedean-reach obligation (the level-move brackets and J2) discharged from
escape grids by pure order theory.  So the hexagon rests on exactly the genuine
cross-pair + exact-match content (forward data + matching residuals + stable
covers) plus the canonical §IV.2.6 escape grids.  `sorry`-free at
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_gridRouteDataEsc
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_unifiedGridRouteEsc

/-! ### Scoping the exact-match cover (§J of `OptionB_C1aGridTransport.lean`).

**Verdict: solvability + escape grid does NOT close `StableGridIndifferentCover`.**
Restricted solvability + a `j`-axis escape bracket reaches only the strictly
weaker `DenseSliceInterpolantCover` (`denseSliceInterpolantCover_of_solvability_and_bracket`):
a collapse to an *interpolated* `X j` value (not a grid point) at a *single* level.
Two independent walls block the upgrade to the exact-match, level-stable,
grid-point cover: (1) the interpolant ranges over a continuum, the grid points are
countable; (2) lifting the single-level collapse to all levels transports a
two-coordinate `{j,k}` indifference across `t` — which `stableCover_gives_levelTransport`
exhibits as exactly `TBlockDiagonalResidue`-shaped content (circular).  So the
exact-match cover genuinely needs the continuity+density §IV.2.6 closure, not a
pure-solvability reach.  Foundational/`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.denseSliceInterpolantCover_of_solvability_and_bracket
#print axioms WakkerInfra.ProductPref.stableCover_gives_levelTransport

/-! ### The continuity+density closure engine (§K of `OptionB_C1aGridTransport.lean`).

§J identified the genuine path for the exact-match cover: a continuity+density
closure (residue on the dense grid + continuous contours ⟹ residue on the
continuum).  §K mechanizes the **engine**: the two-coordinate `{j,k}`-slice map is
continuous (`continuous_jkSliceMap`), and an indifference extends from the dense
grid image to all of `X j × X k` (`indiff_extends_of_denseGridImage`) via
`IsClosed.preimage` + `DenseRange.closure_eq` — Mathlib's `Continuous.ext_on`-style
closure, the same pattern as `Certificates.sharedPivotGrid_global_agreement`.  This
reduces the closure to the named §IV.2.6 input `GridImageDense` (dense grid image)
+ a closed indifference set (preference continuity).  `sorry`-free at
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.continuous_jkSliceMap
#print axioms WakkerInfra.ProductPref.indiff_extends_of_denseGridImage

/-! ### Scoping `GridImageDense` vs the dense-range infrastructure (§L of
    `OptionB_C1aGridTransport.lean`).

**Verdict: the dense-range infrastructure does NOT discharge `GridImageDense`.**
`CoordinateDenseRangeCertificate := ∀ i, DenseRange (R.V i)` is about the full
*utility image* being dense (a refinement-family / mesh property), whereas
`GridImageDense G` requires the **single** calibrated grid `{(αⱼ m, αₖ n)}` to be
dense.  `gridImageDense_imp_axisDenseRange` proves `GridImageDense` forces
`DenseRange G.αj` — but a calibrated grid's axis is a *standard sequence*, an
arithmetic progression under any representation, hence **not dense** (the
machine-checked no-go `M2Frontier.additiveRealBool_strictStandardSequence_not_dense`).
So `GridImageDense` is unsatisfiable for the single grid; the §K closure engine is
sound but must run over a §IV.2.6 refinement *mesh family*, not the measuring-stick
grid.  Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.gridImageDense_imp_axisDenseRange

/-! ### Generalized closure engine over an abstract dense mesh (§M of
    `OptionB_C1aGridTransport.lean`).

§L showed the §K engine's single-grid `GridImageDense` is unsatisfiable (the grid
axes are arithmetic progressions, not dense).  The fix: generalize the engine to
consume *any* dense `{j,k}`-mesh `(meshJ, meshK) : I → X j × X k` — in particular a
§IV.2.6 refinement mesh (`DenseJKMesh`).  `indiff_extends_of_denseJKMesh` extends an
indifference from such a mesh to the continuum (pure topology); the single-grid §K
engine is recovered as the `I := ℕ × ℕ` instance
(`indiff_extends_of_denseGridImage_via_mesh`).  So the analytic closure is now in
its reusable, satisfiable form — the genuine remaining input is the refinement
mesh's density (the §IV.2.6 construction), not the impossible single-grid density.
Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.indiff_extends_of_denseJKMesh
#print axioms WakkerInfra.ProductPref.indiff_extends_of_denseGridImage_via_mesh

/-! ### Scoping utility-side density for the mesh (§N of `OptionB_C1aGridTransport.lean`).

Does the per-coordinate dense-range infrastructure build a usable `DenseJKMesh`?
**Two machine-checked findings.** (N.1, positive) `denseJKMesh_of_coordinateDenseRanges`:
the product of two per-coordinate dense families is a dense `{j,k}`-mesh
(`DenseRange.prodMap`) — so the §M *density input* is reachable from per-coordinate
density (what the surjectivity/rational-image chain supplies for ℝ).  (N.2, the
catch) `fixedB_meshHypothesis_forces_constant_score`: the §M closure engine requires
`[mesh i|c] ∼ b` for a *fixed* `b` across the whole mesh, which under a rep forces
the slice-score constant on a dense set — impossible.  So the §M engine extends a
*fixed* indifference class, not the cover's *moving-target* relation `[x|v|c] ∼ [grid
rep of (x,v)|c]`; closing the cover needs a comparison-map continuity argument, not
`indiff_extends`.  Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.denseJKMesh_of_coordinateDenseRanges
#print axioms WakkerInfra.ProductPref.fixedB_meshHypothesis_forces_constant_score

/-! ### The comparison-map closure engine (§O of `OptionB_C1aGridTransport.lean`).

§N.2 identified the cover as a *moving-target* relation needing a comparison-map
closure (not the fixed-`b` §M engine).  §O builds it: `JointWeakPrefClosed` (the
joint `≽`-graph `{(y,z) | y ≽ z}` is closed — a named topological input, strictly
stronger than `PreferenceContinuous`), soundness-gated by
`jointWeakPrefClosed_of_additiveRep` (it holds under a rep with continuous
utilities, as the preimage of `{(p,q) | q ≤ p}` under the continuous score-pair
map).  `weakPref_extends_of_dense` then extends a comparison between two
**continuously-varying** profiles `F y ≽ G y` from a dense parameter set to all `y`;
`indiff_extends_of_dense` is the two-directional indifference form.  This is the
engine the cover needs — both sides vary with the parameter — which §M could not
express.  Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.jointWeakPrefClosed_of_additiveRep
#print axioms WakkerInfra.ProductPref.weakPref_extends_of_dense
#print axioms WakkerInfra.ProductPref.indiff_extends_of_dense

/-! ### The mesh is free for ℝ-coordinates (§P of `OptionB_C1aGridTransport.lean`).

For the Debreu–Koopmans setting `X i = ℝ`, the `{j,k}`-mesh's **density** is not a
residual: `realDenseJKMesh` builds a dense mesh from `Rat.denseRange_cast` (rationals
dense in ℝ) with no axiom beyond the ambient topology.  So "build the mesh" is
settled outright for the DK setting; the genuine remaining §IV.5 frontier is only
the **matching** — the residue holding *on* the mesh (the Thomsen cross-pair
cancellation `OffCalCompensationMatch`, the full standard-sequence
double-cancellation construction, A1-non-derivable per the strip/Kz probes).
Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.realDenseJKMesh

/-! ### Attacking the matching: its irreducible core (§Q of `OptionB_C1aGridTransport.lean`).

Attacking the matching from bare axioms pins its true content.  The matching's
`KzTransfer` half **is** cross-pair trade-off transitivity
(`kzTransfer_iff_crossPairTradeoffTransitivity`, definitional): from
`(j:x→y)≡(k:q→p)` and `(j:x→y)≡(t:w→c)`, conclude `(k:q→p)≡(t:w→c)` — Wakker IV.2.5's
hexagon.  `crossPairTradeoffTransitivity_of_additiveRep` proves it necessary under a
rep (the additive scale composes trade-offs across pairs).  **The determination:**
the matching needs this *equality-transfer across coordinate pairs* — which
restricted solvability (existence of compensations) does NOT supply, and which the
formalized `TradeoffConsistency` (single-coordinate, per the §5 gate) does NOT
contain.  So the matching's irreducible axiom is cross-pair trade-off consistency,
exactly Wakker's hexagon input — neither solvability nor A1.  Audit foundational /
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.kzTransfer_iff_crossPairTradeoffTransitivity
#print axioms WakkerInfra.ProductPref.crossPairTradeoffTransitivity_of_additiveRep

/-! ### Attempting the hexagon construction (§ `OptionB_C1aHexagonConstruction.lean`).

Genuine progress on the Debreu/KLST measuring-stick derivation of the hexagon.
The atomic hexagon `KzAnchorTransfer` is decomposed (by pure weak order,
`kzAnchorTransfer_of_kStepMatch_and_bridge`) into:
* `KStepMatch` — within-slice `{k,t}` compensation EXISTENCE, which is
  **genuinely discharged from restricted solvability + a t-bracket**
  (`kStepMatch_of_solvability_and_bracket`, audit `[propext, Quot.sound]` — no
  cancellation axiom); and
* `J2AtP` — the `{j,t}`-difference's `k`-value shift, shown to be exactly the
  project's `k`-block separability (`j2AtP_of_kBlockWeakIndependent`).
The assembled `kzAnchorTransfer_of_solvability_bracket_and_kBlock` derives the
atomic hexagon from {restricted solvability + a t-bracket + `k`-block independence}.
Both new residuals are soundness-gated (`kStepMatch_of_additiveRep`,
`j2AtP_of_additiveRep`).  **Net:** the hexagon's *existence* content is now
discharged from solvability; the irreducible remainder is exactly `k`-block
independence (a single KLST separability condition), not the full cross-pair
transitivity.  Audit `[propext, Quot.sound]` / `[propext, Classical.choice,
Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.kzAnchorTransfer_of_kStepMatch_and_bridge
#print axioms WakkerInfra.ProductPref.kStepMatch_of_solvability_and_bracket
#print axioms WakkerInfra.ProductPref.j2AtP_of_kBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.kzAnchorTransfer_of_solvability_bracket_and_kBlock
#print axioms WakkerInfra.ProductPref.kStepMatch_of_additiveRep
#print axioms WakkerInfra.ProductPref.j2AtP_of_additiveRep

/-! ### Hexagon construction §F — existence half fully structural.

The `KStepMatch` bracket is discharged from a per-datum Archimedean escape grid by
pure order theory (`kStepMatchBracket_of_escapeGrid`, via `archimedean_reach_above`/
`below`), so `KStepMatch` rests on `{RestrictedSolvability + Archimedean escape}`
alone (`kStepMatch_of_solvability_and_escapeGrid`).  The assembled
`kzAnchorTransfer_of_escapeGrid_and_kBlock` derives the atomic hexagon from
{solvability + Archimedean escape + `k`-block independence}: the existence content
fully structural (no topology IVT, no A1, no cancellation), the sole remaining
residue being `k`-block separability.  Audit `[propext, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.kStepMatchBracket_of_escapeGrid
#print axioms WakkerInfra.ProductPref.kStepMatch_of_solvability_and_escapeGrid
#print axioms WakkerInfra.ProductPref.kzAnchorTransfer_of_escapeGrid_and_kBlock

/-! ### Cross-pair hexagon over the anchor continuum from a dense set
    (§ `OptionB_C1aCrossPairDenseAnchor.lean`).

The cross-pair trade-off transitivity `CrossPairTradeoffTransitivity` (= `KzTransfer`,
the genuine §IV.5 hexagon input) asserts the conclusion `[z|q|c] ∼ [z|p|w]` at
**every** anchor `j`-value `z`, while its premises `P1`, `J2` do not mention `z`.
So the conclusion is an indifference between two continuous single-anchor slice
maps, and by preference continuity (`JointWeakPrefClosed`, the §O comparison-map
closure) it extends from a **dense** set of anchors to all anchors
(`crossPairTradeoffTransitivity_of_denseAnchors`, `kzTransfer_of_denseAnchors`).
For ℝ-coordinates the rational anchors are dense, so rational anchors suffice
(`crossPairTradeoffTransitivity_of_rationalAnchors`).

This is a genuine, **non-circular** forward step: the only structural input is
continuity (not the permutation-equivalent diagonal residues, so §D.2b circularity
is avoided).  It discharges the residue's *anchor* universal quantifier; the
cross-pair *magnitude-matching* content (the residue on the dense anchor set,
`CrossPairTradeoffTransitivityOnAnchors`, proved necessary under a rep) remains the
genuine §IV.5 frontier.  Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.crossPairTradeoffTransitivity_iff_onAnchors_univ
#print axioms WakkerInfra.ProductPref.continuous_anchorSliceMap
#print axioms WakkerInfra.ProductPref.crossPairTradeoffTransitivity_of_denseAnchors
#print axioms WakkerInfra.ProductPref.kzTransfer_of_denseAnchors
#print axioms WakkerInfra.ProductPref.crossPairTradeoffTransitivityOnAnchors_of_additiveRep
#print axioms WakkerInfra.ProductPref.crossPairTradeoffTransitivity_of_rationalAnchors

/-! ### §F — the `t`-level continuum quantifier (the equal-spacing level move).

The grid diagonal step `[u₁|v₁|c] ∼ [u₂|v₂|c]` is, for fixed `{j,k}`-data,
continuous in the level `c` (only the outermost `t`-update varies), so it extends
from a dense set of `t`-levels to all levels by the §O comparison-map closure
(`indiff_allLevels_of_denseLevels`, `weakPref_allLevels_of_denseLevels`).  For
ℝ-coordinates the level move thus reduces to rational levels
(`indiff_allLevels_of_rationalLevels`).  This is a forward-construction tool for
the equal-spacing diagonal step — non-circular (continuity only).  Audit
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.continuous_tSliceMap
#print axioms WakkerInfra.ProductPref.indiff_allLevels_of_denseLevels
#print axioms WakkerInfra.ProductPref.weakPref_allLevels_of_denseLevels
#print axioms WakkerInfra.ProductPref.indiff_allLevels_of_rationalLevels

/-! ### WP-EQ0 — equal-spacing derivability probe
    (§ `OptionB_EqualSpacingProbe.lean`).

Before the multi-week equal-spacing forward construction (WP-EQ1 of
`OptionB_EqualSpacingConstructionPlan.md`), the mandated derivability probe pins
the matching kernel `CompensationMatch` (the `k`-background independence of a
`j`-step's `t`-compensation — equal spacing, stripped to its atomic logical form):

* **Probe B (sound):** `compensationMatch_of_additiveRep` — the matching is
  necessary under any additive representation (equal spacing is forced; the `V_k`
  term cancels, so the compensation equation is `k`-background-free).
* **Probe A (not free):** `a1_does_not_imply_compensationMatch` — A1 on every
  coordinate does NOT imply it (the comonotone, Thomsen-violating `Pkz`
  countermodel, reused from the `KzTransfer` probe).
* **Scoping confirmation:** `compensationMatch_of_kBlockWeakIndependent` — the
  kernel is the indifference shadow of KLST `k`-block separability
  `KBlockWeakIndependent`, so WP-EQ1a's forward target is exactly the existing
  downstream-capstone input (no glue needed).

Verdict: the WP-EQ1a target is sound and A1-non-derivable — a GREEN light to attack
it with restricted solvability + the third coordinate (the genuine Wakker §IV.5
measuring-stick lever), not a one-line A1 or residue projection.  Audit
`[propext, Classical.choice, Quot.sound]` (Probe A's computation: `[propext]`;
scoping: `[propext, Quot.sound]`). -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBEqualSpacingProbe.compensationMatch_of_additiveRep
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEqualSpacingProbe.kz_not_compensationMatch
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEqualSpacingProbe.a1_does_not_imply_compensationMatch
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEqualSpacingProbe.compensationMatch_of_kBlockWeakIndependent

/-! ### WP-EQ1a.0 — compensation uniqueness (the strictness prerequisite)
    (§ `OptionB_EqualSpacingStrictness.lean`).

Resolves the `standard_sequence_unique` prerequisite of the equal-spacing crux, with
an honest scoping correction:

* **§A (free):** `compensationLevel_unique_of_indiff` — two `t`-levels that both
  compensate the same `j`-step against the same background are indifferent (pure
  weak order).  This is the *indifference-level* uniqueness the crux (WP-EQ1a.2)
  actually needs.
* **§B (gate):** `compensationLevel_Vt_eq_of_additiveRep` — necessary under a rep
  (the two levels have equal `V_t`).
* **§C (no-go):** `hStrict_fails_for_plateau` — the *value-level* `hStrict`
  (`indiff (update a j v)(update a j w) → v = w`) required by
  `Core.standard_sequence_unique` is NOT a structural-axiom consequence (a
  representation with a non-injective `V_j` plateau violates it).

Net (de-risks the plan): the crux routes through free indifference-level uniqueness;
value-level standard-sequence uniqueness is off the critical path.  Audit
`[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.compensationLevel_unique_of_indiff
#print axioms WakkerInfra.ProductPref.compensationLevel_Vt_eq_of_additiveRep
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEqualSpacingStrictness.hStrict_fails_for_plateau

/-! ### WP-EQ1a.2-construct (session 1 + build finding) — the second measuring-stick sequence
    (§ `OptionB_EqualSpacingSecondSequence.lean`).

The committed equal-spacing construction's foundation, **and** the machine-checked
finding that the second-sequence reformulation is circular:

* `shiftedCalibration_of_secondSequence` — **forward (free):** the second-sequence
  data discharges `ShiftedCalibration` by pure weak order (the measuring-stick
  relocation).
* `secondSequenceData_of_additiveRep` — **soundness gate:** a representation supplies
  the interface.
* `secondSequenceData_iff_shiftedCalibration` — **the WP-EQ1a.2-build finding:** the
  interface is **logically equivalent** to the shifted calibration it was meant to
  reduce (`Nonempty (SecondSequenceData G n) ↔ ∀ m, ShiftedCalibration G m n`).  So a
  1-D second sequence does NOT reduce the residual; the genuine escape is the 2-D
  Thomsen/hexagon solvability construction (Debreu/KLST).

Net: honest negative result — the second-sequence route is circular, sharpening the
real WP-EQ1a.2-build target (the hexagon construction) and leaving the §6 fallback
(carry `KBlockWeakIndependent` as a named input) standing.  Audit
`[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.shiftedCalibration_of_secondSequence
#print axioms WakkerInfra.ProductPref.secondSequenceData_of_additiveRep
#print axioms WakkerInfra.ProductPref.shiftedCalibration_forall_of_secondSequenceFamily
#print axioms WakkerInfra.ProductPref.secondSequenceData_of_shiftedCalibration
#print axioms WakkerInfra.ProductPref.secondSequenceData_iff_shiftedCalibration

/-! ### WP-EQ1a.2-build — the third-coordinate layer transport (the hexagon construction)
    (§ `OptionB_EqualSpacingLayerTransport.lean`).

The genuine forward target precisely isolated: `DiagonalLayerPropagation` (the §IV.5
hexagon-combination residual) via the third coordinate `t` as a measuring stick.

* `layerStep_of_alignedRuler` — **forward (free):** the layer-`(m+1)` diagonal step
  from an `AlignedRulerTransport` bundle, by pure weak order (the `t`-stick shuttles
  the comparison up one `k`-layer).
* `alignedRulerTransport_of_additiveRep` — **soundness gate:** a rep supplies the
  bundle exactly when the `k`-grid is equally spaced — so the bundle is *equivalent*
  to the equal-spacing content.

**Honest finding:** the `t`-stick does NOT break the circularity — the bundle's
`diagAtC'` field (the diagonal at the fresh `t`-level `c'`) already *is* a diagonal
step at a new level, the off-cal level move the construction was producing.  The
third coordinate *relocates* the residual onto the stick; it does not discharge it.
The genuine §IV.5 content (equal `k`-grid spacing on the stick + the level-`c'`
diagonal) is sharply isolated and soundness-gated; the §6 fallback (carry
`KBlockWeakIndependent` as a proven-necessary named input) stands.  Audit
`[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.concreteGrid_eq_tri
#print axioms WakkerInfra.ProductPref.layerStep_of_alignedRuler
#print axioms WakkerInfra.ProductPref.alignedRulerTransport_of_additiveRep

/-! ### WP-EQ1a.2-build (ab-initio) — the Archimedean grid induction for the level move
    (§ `OptionB_EqualSpacingArchimedeanGrid.lean`).

The first genuinely-non-circular forward content in the equal-spacing construction:
the Archimedean axiom's standard-sequence grid gives a free induction that reduces
the all-grid-levels `t`-level move to a single step.

* `gridLevelMove_of_step` — **free (the non-circular Archimedean content):** the
  one-step `t`-level move at every grid index ⟹ the move to every grid level, by
  induction.  No cancellation content.
* `gridLevelMoveStep_of_tBlockDiagonalResidue` — the one-step move is
  `TBlockDiagonalResidue` localized to a grid step (no new object; connects to the
  established frontier).
* `gridLevelMove_of_tBlockDiagonalResidue` — the grid-restricted level move from
  {free induction + the standard residual}.

**Honest scope.**  The induction (§B) is genuinely free — it discharges the
*all-grid-levels* quantifier of the level move from a *single* step.  The one-step
residual remains the irreducible §IV.5 content (= `TBlockDiagonalResidue`); reaching
*off-grid* `t`-levels needs the §IV.2.6 density residual (residual 2), which the
repo's no-go (`additiveRealBool_archimedean_..._insufficient_for_selectedRefinedDenseGrid`)
shows Archimedean alone cannot supply.  Audit `[propext, Quot.sound]` /
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.gridLevelMove_of_step
#print axioms WakkerInfra.ProductPref.gridLevelMoveStep_of_tBlockDiagonalResidue
#print axioms WakkerInfra.ProductPref.gridLevelMoveStep_of_additiveRep
#print axioms WakkerInfra.ProductPref.gridLevelMove_of_tBlockDiagonalResidue

/-! ### WP-EQ1a.2-build — the 3-coordinate solvability pivot split
    (§ `OptionB_EqualSpacingPivotSplit.lean`).

Attacking the one-step residual (`TBlockDiagonalResidue` at a grid step) directly by
the Debreu pivot split: route the diagonal comparison `[x|r|·] ≽ [z|p|·]` through the
intermediate `[z|r|·]`, so each leg is single-coordinate and A1-transportable.

* `tBlockDiagonalStep_of_pivotJ_and_a1` — the one-step diagonal move from the
  `{j}`-pivot at level `c` + A1 on `k` (the `{k}`-leg transports by A1).
* `tBlockDiagonalStep_of_pivotFamily_and_a1` — the same from the `{j}`-pivot family
  (at levels `w`, `c`) + A1 on `k`.
* `diagonalPivotJ_transport_of_a1` — **the decisive reduction:** the `{j}`-pivot is
  *free given A1 on `j`* (the `j`-difference direction at one `t`-level gives it at
  all levels).
* `diagonalPivotJ_levelIndep_of_additiveRep` — soundness gate.

**Decisive finding.**  The one-step residual's *level transport* (`w → c`) is fully
**A1-reducible**: both legs transport across `t`-levels by A1 (on `j`, `k`), the
diagonal chaining through `[z|r|·]`.  Combined with the Archimedean grid induction
(all-grid-levels from one step) and the prior continuum reductions, this discharges
*every quantifier* of the level move from A1 + induction.  The sole irreducible
remainder is the **source-level `{j}`-pivot direction** (separating the `j`-direction
from the `k`-direction at the source level) — the genuine cross-pair content the
strip/Kz probes refute from A1, now localized to its sharpest single-step form.
Audit `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalStep_of_pivotJ_and_a1
#print axioms WakkerInfra.ProductPref.tBlockDiagonalStep_of_pivotFamily_and_a1
#print axioms WakkerInfra.ProductPref.diagonalPivotJ_transport_of_a1
#print axioms WakkerInfra.ProductPref.diagonalPivotJ_levelIndep_of_additiveRep

/-! ### CONSOLIDATION CAPSTONE — the hexagon from A1 + one named residual
    (§ `OptionB_HexagonCapstone.lean`).

The consolidation headline: the classical additive-conjoint hexagon
`DoubleCancellation` from A1 (the structural coordinate-independence input) + a
**single** named cross-pair residual `HexagonThomsenResidual` (the Thomsen diagonal
residue at the three coordinate-role assignments) + a J2 supplier.

* `doubleCancellation_of_a1_and_thomsenResidual` — the headline reduction.
* `hexagonThomsenResidual_of_additiveRep` — the residual is necessary (sound).
* `doubleCancellation_of_additiveRep_via_thomsenResidual` — the residual recovers the
  hexagon (the strength is exactly right).

The named residual is the sharpest-isolated genuine §IV.5 content: its anchor,
all-grid-levels, and level-transport quantifiers are all separately mechanized
(`OptionB_C1aCrossPairDenseAnchor`, `OptionB_EqualSpacingArchimedeanGrid`,
`OptionB_EqualSpacingPivotSplit`), it is the KLST `t`-block separability, and it is
proved necessary + non-A1-derivable (five machine-checked circularity findings show no
shortcut).  See `OptionB_ConsolidationSummary.md`.  Audit
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_a1_and_thomsenResidual
#print axioms WakkerInfra.ProductPref.hexagonThomsenResidual_of_additiveRep
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep_via_thomsenResidual

/-! ### §IV.5 roadmap §0 — the five hard constraints, machine-checked
    (§ `OptionB_SectionIV5HardConstraints.lean`).

Executes §0 of `OptionB_SectionIV5GridConstructionRoadmap.md`: the five machine-checked
findings the §IV.5 construction must respect, gathered as named theorems so a single
build re-verifies the design constraints.

1. `constraint1_a1_does_not_imply_hexagon` — A1 ⇏ the hexagon.
2. `constraint2_matchingKernel_of_kBlockSeparability` — the matching kernel ⟸ KLST
   `t`-block separability (no weaker target).
3. `constraint3_secondSequence_is_circular` — the 1-D second-sequence reformulation is
   equivalent to its target.
4. `constraint4_layerTransport_relocates` — the 3-coordinate layer transport relocates
   the residual, not discharges it.
5. `constraint5_archimedean_insufficient_for_denseGrid` — Archimedean + solvability +
   tradeoff ⇏ a dense grid (density needs a refinement-mesh family).

All foundational-only (`[propext, (Classical.choice,) Quot.sound]`); no `sorryAx`. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBSectionIV5HardConstraints.constraint1_a1_does_not_imply_hexagon
#print axioms WakkerRoadmap.CertificateChecklist.OptionBSectionIV5HardConstraints.constraint2_matchingKernel_of_kBlockSeparability
#print axioms WakkerRoadmap.CertificateChecklist.OptionBSectionIV5HardConstraints.constraint3_secondSequence_is_circular
#print axioms WakkerRoadmap.CertificateChecklist.OptionBSectionIV5HardConstraints.constraint4_layerTransport_relocates
#print axioms WakkerRoadmap.CertificateChecklist.OptionBSectionIV5HardConstraints.constraint5_archimedean_insufficient_for_denseGrid

/-! ### G1.a — the Thomsen cell: calibration from KLST block separability
    (§ `OptionB_EqualSpacingThomsenCell.lean`).

The first sound, non-circular brick of the §IV.5 grid construction (G1.a of
`OptionB_SectionIV5GridConstructionRoadmap.md`): the off-axis grid calibration
`CalibrationAllBackgrounds` from the standard KLST block separability conditions
(`KBlockWeakIndependent`, `JBlockWeakIndependent`) — **not** the §D.2b-circular
diagonal residues.

* `calJ_of_kBlockWeakIndependent` / `calK_of_jBlockWeakIndependent` — the off-axis
  calibration cells from block separability (shift the common third-coordinate value
  on the on-axis `spaced_j`/`spaced_k` data).
* `calibrationAllBackgrounds_of_blockIndependence` — the G1.a calibration content.
* `kBlockWeakIndependent_necessary` / `jBlockWeakIndependent_necessary` — soundness
  gates (the block conditions necessary under a rep).

**Honest scope:** discharges the calibration half of the Thomsen cell from KLST block
separability (sound, non-circular).  The block conditions remain the genuine §IV.5
input (proved necessary, A1-non-derivable); discharging *them* from bare solvability is
the remaining G1 content.  Audit `[propext, Quot.sound]` /
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.calJ_of_kBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.calK_of_jBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.calibrationAllBackgrounds_of_blockIndependence
#print axioms WakkerInfra.ProductPref.kBlockWeakIndependent_necessary
#print axioms WakkerInfra.ProductPref.jBlockWeakIndependent_necessary

/-! ### G1.b — propagate the calibrated cell to the full grid Thomsen closure
    (§ `OptionB_EqualSpacingGridPropagate.lean`).

The second §IV.5 grid brick (G1.b of `OptionB_SectionIV5GridConstructionRoadmap.md`):
*propagate* the single-cell calibration (G1.a) to the **full** `GridThomsenClosure`
through the standard KLST block separability vocabulary — the non-circular route.

* `gridDiagonalStepLevelMove_of_tBlockWeakIndependent` — the `st → c` level
  propagation of the interior diagonal step from `TBlockWeakIndependent` (the
  non-circular analog of `diagonalStepLevelMove_of_tBlockDiagonalResidue`).
* `gridDiagonalStep_of_calibration_and_tBlock` /
  `gridDiagonalStep_of_blockIndependence` — the full diagonal step (all `(m,n)`, all
  `t`-levels) from calibration + `t`-block, then straight from the three block
  conditions.
* `gridThomsenClosure_of_blockIndependence` — **the G1.b target**: the full grid
  Thomsen closure from the three KLST block conditions.
* `gridDiagonalStep_necessary` / `gridThomsenClosure_necessary` /
  `tBlockWeakIndependent_necessary` — soundness gates.

**Honest scope:** the calibration propagates to the entire grid closure through the
*same* standard block vocabulary (level move = `TBlockWeakIndependent`, closure = free
order theory).  So the §IV.5 grid Thomsen closure is fully reduced to Wakker's three
KLST block-independence conditions — each proved necessary, A1-non-derivable.
Discharging those three from bare restricted solvability is the remaining G1 content.
Audit `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.gridDiagonalStepLevelMove_of_tBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_of_calibration_and_tBlock
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_of_blockIndependence
#print axioms WakkerInfra.ProductPref.gridThomsenClosure_of_blockIndependence
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_necessary
#print axioms WakkerInfra.ProductPref.gridThomsenClosure_necessary
#print axioms WakkerInfra.ProductPref.tBlockWeakIndependent_necessary

/-! ### G1.c — the end-to-end grid step: existence + closure
    (§ `OptionB_EqualSpacingGridStep.lean`).

The third §IV.5 grid brick (G1.c of `OptionB_SectionIV5GridConstructionRoadmap.md`):
the **end-to-end grid step** — bundle grid *existence* (from the structural axioms +
topology) with the G1.b closure, so the full Thomsen grid holds on a grid that
actually exists from the axioms.

* `gridStep_of_structuralAxioms_and_blockIndependence` — **the G1.c endpoint**: there
  exists an injective calibrated `{j,k,t}` grid on which `GridThomsenClosure` holds,
  from `RestrictedSolvability` + A1-`t` + `WakkerCoordinateTopology` + strict seed +
  the three KLST block conditions.
* `gridDiagonalStepExists_of_structuralAxioms_and_blockIndependence` — the
  diagonal-step form.
* `gridStep_of_structuralAxioms_via_additiveRep` — soundness gate (the grid step is
  necessary under any representation, since the block conditions are).

**Axiom note.**  Unlike G1.a/G1.b (foundational-only), G1.c routes through grid
existence and therefore inherits the two **documented** §III.4.2 bracket-reach IVT
seams `coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology` (the
standard Option B topology interface — not a `_from_raw_axioms` bypass, not a `sorry`,
the same seams carried by `calibratedJKGrid_of_structuralAxioms_and_topology` above).

**Honest scope:** G1.c closes work package G1 *modulo the block conditions* — the
§IV.5 grid step is a one-line composition of {grid existence} + {G1.b closure}.  The
single remaining G1 obligation is discharging the three KLST block conditions from
bare restricted solvability (the genuine `n ≥ 3` crux). -/

#print axioms WakkerInfra.ProductPref.gridStep_of_structuralAxioms_and_blockIndependence
#print axioms WakkerInfra.ProductPref.gridDiagonalStepExists_of_structuralAxioms_and_blockIndependence
#print axioms WakkerInfra.ProductPref.gridStep_of_structuralAxioms_via_additiveRep

/-! ### G2 — transport the grid step to all profiles (the full `TBlockDiagonalResidue`)
    (§ `OptionB_EqualSpacingGridTransport.lean`).

Work package G2 of `OptionB_SectionIV5GridConstructionRoadmap.md`: lift the G1 grid
step (grid points) to the full `TBlockDiagonalResidue P j k t` (all `{j,k}`-values,
all backgrounds), through the **non-circular block route** — feeding the G1.b closure
`gridThomsenClosure_of_blockIndependence` (not the bespoke `GridThomsenForwardFrontier`)
through the existing transport machinery.

* `gridRestrictedTBlock_of_blockIndependence` — closure + A1-`j` ⟹ the grid-restricted
  residue (via `gridTBlockDiagonalResidue_of_closure`).
* `tBlockDiagonalResidue_fixedGrid_of_blockIndependence_and_cover` — full residue over
  a fixed background (grid-restricted + stable cover + the `tri_eq_of_agreeOff`
  background bridge).
* `tBlockDiagonalResidue_of_blockIndependence_and_coverData` — **the G2 target**: the
  full residue over all backgrounds from {three block conditions + A1-`j` + a
  background-indexed stable-cover family `TBlockGridCoverData`}.
* `tBlockDiagonalResidue_necessary` — soundness gate.

**Honest scope:** the block route is strictly leaner than the frontier route (no
topology, no solvability, no A1-`k`).  `TBlockDiagonalResidue` is reduced to {three
KLST block conditions (G1) + A1-`j` (theorem-backed) + the level-stable grid cover
(`StableGridIndifferentCover`, the §IV.2.6 / G3 density content)}.  Discharging the
block conditions (G1 crux) and the cover (G3) are the remaining obligations.  Audit
`[propext, Classical.choice, Quot.sound]` (foundational-only — the grid and cover are
inputs, so no topology seams enter here). -/

#print axioms WakkerInfra.ProductPref.gridRestrictedTBlock_of_blockIndependence
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_fixedGrid_of_blockIndependence_and_cover
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_blockIndependence_and_coverData
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_necessary

/-! ### G3 — §IV.2.6 mesh density + the redundancy finding
    (§ `OptionB_EqualSpacingMeshDensity.lean`).

Work package G3 of `OptionB_SectionIV5GridConstructionRoadmap.md`, but it first
**corrects the route**.

* `tBlockDiagonalResidue_of_tBlockWeakIndependent` — **the finding**:
  `TBlockDiagonalResidue` is definitionally `TBlockWeakIndependent` plus two
  disequality guards, so the residue is **free** (guard-drop) from the standard KLST
  block separability — no grid, no cover, no density.
* `tBlockDiagonalResidue_blockRoute_is_redundant` — consequence: G2's transport and
  the naive G3 cover are **redundant** in the block route (the residue follows from
  one block condition alone). The grid construction does genuine work only from bare
  restricted solvability.
* `weakPrefComparison_extends_of_denseJKMesh` / `indiffComparison_extends_of_denseJKMesh`
  / `weakPrefComparison_extends_real` — the genuine §IV.2.6 density closure **for the
  solvability route**: a fixed-level `≽`/`∼` comparison extends from a dense
  `{j,k}`-mesh to all values (via the §O moving-target engine + `JointWeakPrefClosed`);
  free for ℝ (rational mesh).
* `jointWeakPrefClosed_necessary` — soundness gate.

**Honest scope:** the block route does not need G2/G3; the density closure is
non-redundant only in the solvability route, where it *extends* a supplied
mesh-comparison — and that mesh-comparison is, by `OptionB_C1aGridTransport` §Q,
exactly `KzTransfer` = the cross-pair crux. So the single genuine open obligation
across G1/G2/G3 is the cross-pair / block-separability content from bare solvability.
Audit `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_tBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_blockRoute_is_redundant
#print axioms WakkerInfra.ProductPref.weakPrefComparison_extends_of_denseJKMesh
#print axioms WakkerInfra.ProductPref.indiffComparison_extends_of_denseJKMesh
#print axioms WakkerInfra.ProductPref.weakPrefComparison_extends_real
#print axioms WakkerInfra.ProductPref.jointWeakPrefClosed_necessary

/-! ### G4.a — construct the grid index-sum slice representation `S`
    (§ `OptionB_EqualSpacingSliceRep.lean`).

Work package G4.a of `OptionB_SectionIV5GridConstructionRoadmap.md` (Link B, hexagon →
per-slice additive representation): **construct** `S` and prove `GridAdditiveSliceRep`
(`RawAxiomDischargersHexagon`) — the §IV.5 Step-4 calibration output on the grid.

* `gridIndexSumScore_eq_indexSum` — `S = Vⱼ + Vₖ` evaluates to `n + m` on grid profiles
  (property ii, from the normalization witness).
* `score_concreteGrid` — the additive score of a grid profile under a rep.
* `gridStepStrictMono_of_additiveRep` / `concreteDiagonalStep_of_additiveRep_grid` —
  soundness gates for the two order ingredients (strict monotone step; the G1 diagonal
  step). **Strict** monotonicity is required — the weak form is a documented no-go
  (total indifference satisfies it but falsifies order-tracking).
* `gridAdditiveSliceRep_of_data` / `gridAdditiveSliceRep_of_normalization_diagonal_monotone`
  — **the G4.a construction**: `GridAdditiveSliceRep` from {index-sum score + concrete
  diagonal step (G1) + strict monotonicity}.
* `gridAdditiveSliceRep_of_additiveRep` — soundness capstone (a rep with a
  strictly-increasing, equal-spaced grid supplies all ingredients).

**Honest scope:** Link-B's first brick is complete modulo the same G1 crux (the
concrete diagonal step is G1; the normalization witness is theorem-backed; strict
monotonicity is necessary under a rep). G4.b (continuous extension off the grid via the
G3 mesh density) and G4.c (assemble the C1 frontier field, already mechanized) follow.
Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.gridIndexSumScore_eq_indexSum
#print axioms WakkerInfra.ProductPref.score_concreteGrid
#print axioms WakkerInfra.ProductPref.gridStepStrictMono_of_additiveRep
#print axioms WakkerInfra.ProductPref.concreteDiagonalStep_of_additiveRep_grid
#print axioms WakkerInfra.ProductPref.gridAdditiveSliceRep_of_data
#print axioms WakkerInfra.ProductPref.gridAdditiveSliceRep_of_normalization_diagonal_monotone
#print axioms WakkerInfra.ProductPref.gridAdditiveSliceRep_of_additiveRep

/-! ### G4.b — extend `S` to a continuous slice utility off the grid
    (§ `OptionB_EqualSpacingSliceExtend.lean`).

Work package G4.b of `OptionB_SectionIV5GridConstructionRoadmap.md` (Link B): extend
the grid representation `S` (G4.a) to all of `X j × X k`.  **The construction reshapes
the route** (a §N.2-style no-go, like G3):

* `continuous_sliceMap` / `sliceMap_apply` — the two-coordinate slice map and its
  continuity (the genuine reusable topological brick).
* `sliceWeakPref_fixedTarget_extends_of_dense` /
  `sliceWeakPref_fixedSource_extends_of_dense` — the §O engine **correctly scoped**: it
  extends a *fixed*-target/source slice preference from a dense mesh.  The off-grid
  *representation*, by contrast, is a moving-target relation whose density closure would
  need mesh density within each closed sublevel set (false for ambient density) — so the
  roadmap's "extend the representation via §O density" is a no-go.
* `pairwiseSliceRep_iff_orderCalibration` /
  `pairwiseSliceRepresentation_of_orderCalibration` — the honest reduction: the off-grid
  representation **is** the named §IV.5 order-calibration residual
  `PairwiseOrderCalibrationCertificate`, produced by the existing
  restricted-solvability assembly (not 2-D density).
* `orderCalibration_of_additiveRep` — soundness gate.

**Honest scope:** G4.b's genuine topological content is `continuous_sliceMap`; the
off-grid representation reduces to the standard §IV.5 Step-4 order-calibration the
project already discharges from solvability.  The §O density engine is correctly scoped
to *fixed*-comparison extension only.  Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.continuous_sliceMap
#print axioms WakkerInfra.ProductPref.sliceWeakPref_fixedTarget_extends_of_dense
#print axioms WakkerInfra.ProductPref.sliceWeakPref_fixedSource_extends_of_dense
#print axioms WakkerInfra.ProductPref.pairwiseSliceRep_iff_orderCalibration
#print axioms WakkerInfra.ProductPref.pairwiseSliceRepresentation_of_orderCalibration
#print axioms WakkerInfra.ProductPref.orderCalibration_of_additiveRep

/-! ### G4.c — assemble the per-slice reps into the shared-`V₀` family (Link B done)
    (§ `OptionB_EqualSpacingSliceFamily.lean`).

Work package G4.c of `OptionB_SectionIV5GridConstructionRoadmap.md` — the final brick
of Link B, an **assembly** wiring the G4.a/G4.b per-slice outputs into the
already-mechanized Phase-74 shared-`V₀` closer and the Phase-65 end-to-end capstone.

* `step4Family_of_perSliceRepresentationFamily` — the per-slice grid-normalized
  representation family (G4.a normalization + G4.b order-calibration) ⟹ the shared-pivot
  Step-4 tradeoff family.
* `gridAdditiveRepresentationFamily_of_perSliceRepresentationFamily` — + pivot-grid
  density + per-slice pivot continuity ⟹ the common-`V₀` family (Phase-74 M5 closer).
* `additiveRep_nonempty_of_perSliceRepresentationFamily` — **the Link-B endpoint**:
  `Nonempty (AdditiveRep P)` from the per-slice reps + structural axioms + topology +
  density + continuity.
* `perSliceRepresentationFamily_of_additiveRep` — soundness gate.

**Honest scope:** G4.c is pure assembly (no new §IV.5 content) — its only inputs are the
per-slice reps (the G1 crux = `PairwiseSliceRepresentationCertificate`) and the standard
analytic inputs (density, continuity).  §A/§B/§D audit clean at `[propext,
Classical.choice, Quot.sound]`; the **endpoint §C inherits the documented Phase-65
Stage-5 `_from_raw_axioms` seams** (`twoPivotSliceTransport{Forward,Backward}`,
`pivotCoordinateRetargetingBracket{Upper,Lower}Reach`,
`allPairsAdditivityDrivenCoordinateImageCoverageResidual` — the same seams
`additiveRep_nonempty_from_raw_axioms` already exposes, since the C1-constructed `V₀` is
not asserted surjective; a seam-free route uses the C2/surjective capstones). -/

#print axioms WakkerInfra.ProductPref.step4Family_of_perSliceRepresentationFamily
#print axioms WakkerInfra.ProductPref.gridAdditiveRepresentationFamily_of_perSliceRepresentationFamily
#print axioms WakkerInfra.ProductPref.additiveRep_nonempty_of_perSliceRepresentationFamily
#print axioms WakkerInfra.ProductPref.perSliceRepresentationFamily_of_additiveRep

/-! ### Link-A capstone — the hexagon from the KLST block conditions (Link A done)
    (§ `OptionB_EqualSpacingLinkACapstone.lean`).

Realizes the "Link A done" node of the §IV.5 roadmap dependency graph (§6), parallel to
G4.c's Link-B endpoint: assemble `DoubleCancellation P j k` from the standard KLST
block-separability conditions + A1 + the §IV.2.6 J2 escape grid.

* `hexagonThomsenResidual_of_blockIndependence` — the named residual from the three KLST
  `t`-block conditions at the three coordinate-role assignments (the G3 guard-drop
  applied at three triples).
* `doubleCancellation_of_blockIndependence_and_J2supplier` (bare J2) /
  `doubleCancellation_of_blockIndependence_and_escapeJ2` (J2 escape-discharged) — **the
  Link-A endpoint**: the classical hexagon from {three block conditions + A1 + J2}.
* `blockIndependence_necessary` / `doubleCancellation_of_additiveRep_via_blockIndependence`
  — soundness gates.

**Honest scope:** pure assembly (no new §IV.5 content); the genuine open input is the
three KLST block conditions from bare solvability (the G1 crux, proved necessary /
A1-non-derivable); J2 is the standard §IV.2.6 escape-grid content; A1 is structural.
Foundational-only — audit `[propext, Quot.sound]` / `[propext, Classical.choice,
Quot.sound]` (no topology seams). -/

#print axioms WakkerInfra.ProductPref.hexagonThomsenResidual_of_blockIndependence
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_blockIndependence_and_J2supplier
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_blockIndependence_and_escapeJ2
#print axioms WakkerInfra.ProductPref.blockIndependence_necessary
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep_via_blockIndependence

/-! ### C1.a-1 — compensating-level existence at one off-cal cell
    (§ `OptionB_C1aCompensationExistence.lean`).

First genuinely-new sound brick of the C1.a crux attack
(`OptionB_C1aConstructionPlan.md`): the compensating-`t`-level **existence** at one
off-calibration cell, from the structural axioms (IVT crossing + Archimedean escape).
NOT the wall — existence only; the cross-pair matching (C1.a-3) is the open crux.

* `compensatingLevelExists_of_additiveRep` — soundness gate (proved FIRST): the level
  exists under a rep given `V_t`-reach.
* `compensatingLevelExists_of_topology_and_escapeGrid` — the forward brick: existence
  from {`WakkerCoordinateTopology` bundle + `OffCalJEscapeGrid`}, composing
  `offCalJBracket_of_escapeGrid` (bracket from Archimedean escape) +
  `offCalJHalf_of_topology_and_bracket` (IVT crossing).

**Honest scope:** existence half of the off-cal cell, theorem-backed from the
structural axioms; feeds C1.a-3/C1.a-4 but does not discharge the crux.  Audit
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.compensatingLevelExists_of_additiveRep
#print axioms WakkerInfra.ProductPref.compensatingLevelExists_of_topology_and_escapeGrid

/-! ### C1.a-3 — the Thomsen closure crux (off-cal compensation match)
    (§ `OptionB_C1aThomsenClosure.lean`).

The genuine crux of the C1.a construction (`OptionB_C1aConstructionPlan.md`), attacked
with the gate green first and the circularity guard active.  The result is the honest
machine-checked determination of the wall at single-cell granularity:

* `matchCell_of_diagonalOffCal` / `diagonalOffCal_of_matchCell` (non-circular, weak
  order) — the off-cal match at a cell IS the off-cal diagonal step (via the C1.a-1
  compensator).
* `matchCell_at_st_free` (non-circular) — the match holds FREE at the calibration
  level `st` (from `CalibrationAllBackgrounds`; the cell closes at the calibration
  level with no block input).
* `diagonalOffCal_of_levelTransport` (the wall) — the off-cal step is exactly the
  `st → c` transport of the free `st`-level diagonal step;
* `diagonalOffCal_of_tBlockDiagonalResidue` — that transport IS `TBlockDiagonalResidue`
  at the cell (the §D.2b circularity made explicit at single-cell, single-level
  granularity).
* `offCalMatch_of_additiveRep` — soundness gate.

**Honest determination:** §A/§B reduce the off-cal match, by pure weak order, to the
bare `st → c` transport of a `{j,k}`-two-coordinate-difference indifference (the free
calibration-level step discharged); §C proves that transport IS the target.  So there
is NO non-circular cell-level lemma closing the crux — the remaining content is the
minimum irreducible bit (one two-coordinate indifference, one `t`-level), needing the
global Debreu/KLST construction or the §6 fallback (carry `TBlockWeakIndependent`).
Audit `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.matchCell_of_diagonalOffCal
#print axioms WakkerInfra.ProductPref.diagonalOffCal_of_matchCell
#print axioms WakkerInfra.ProductPref.matchCell_at_st_free
#print axioms WakkerInfra.ProductPref.diagonalOffCal_of_levelTransport
#print axioms WakkerInfra.ProductPref.diagonalOffCal_of_tBlockDiagonalResidue
#print axioms WakkerInfra.ProductPref.offCalMatch_of_additiveRep

/-! ### C1.a-3 global construction — the t-measuring-stick diagonal transport
    (§ `OptionB_C1aMeasuringStick.lean`).

The global standard-sequence forward content for the C1.a crux: the explicit Debreu
measuring-stick reduction of the off-cal diagonal transport.

* `diagAllCells_succ_of_stickCalibration` — **the genuine forward brick** (pure weak
  order): one-stick-level diagonal transport via the measuring-stick chain (stick at two
  consecutive `k`-backgrounds + the free `st`-diagonal at the shifted cell).
* `diagAllCells_of_stick_induction` / `diagAllCells_stickLevels_of_calibration_and_stick`
  — the off-cal diagonal at every stick level from {free `st`-diagonal +
  `StickCalibration` at all `k`-backgrounds}, by free induction.
* `stickCalibration_of_additiveRep` — soundness gate.

**Honest scope:** genuine non-circular reduction — it discharges the all-stick-levels +
all-cells quantifiers of the off-cal transport for free, relocating the residual to
`StickCalibration` (a `{j,t}`-pair object, inter-derivable with the target by the
permutation equivalence — so it sharpens, but does not alone break, the wall). Reaching
off-stick `t`-levels is the §IV.2.6 density residual. Audit `[propext, Quot.sound]` /
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.diagAllCells_succ_of_stickCalibration
#print axioms WakkerInfra.ProductPref.diagAllCells_of_stick_induction
#print axioms WakkerInfra.ProductPref.diagAllCells_stickLevels_of_calibration_and_stick
#print axioms WakkerInfra.ProductPref.stickCalibration_of_additiveRep

/-! ### C1.a-3 global construction (session 2) — building the t-measuring stick
    (§ `OptionB_C1aStickConstruction.lean`).

Session 2 of the global construction: build the measuring stick from solvability and
pin the relocated residual.

* `stickCalibration_of_stickFromExchange` — the per-step datum = the calibration.
* `stickFromExchange_zero_of_constantStepStick` / `constantStepStick_of_additiveRep` —
  the stick built at one `k`-background `0` from the calibration data (genuine, free, no
  block input).
* `stickFromExchange_of_kBlock` / `stickFromExchange_acrossK_of_additiveRep` — **the wall,
  machine-checked**: the across-`k` stick uniformity from `KBlockWeakIndependent` (the
  target).
* `diagAllCells_of_stickAt0_and_kBlock` — the off-cal diagonal from {calibration +
  buildable stick-at-`0` + `k`-block}, exhibiting `KBlockWeakIndependent` as the precise
  relocated residual of the entire measuring-stick route.

**Honest determination:** the stick is constructible at one `k`-background (free); the
across-`k` uniformity IS `KBlockWeakIndependent` (the target). Sixth machine-checked
confirmation that the crux is irreducible by the measuring-stick route. The genuine
remaining content is the §6 fallback's named input. Audit `[propext, Quot.sound]` /
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.stickCalibration_of_stickFromExchange
#print axioms WakkerInfra.ProductPref.stickFromExchange_zero_of_constantStepStick
#print axioms WakkerInfra.ProductPref.constantStepStick_of_additiveRep
#print axioms WakkerInfra.ProductPref.stickFromExchange_of_kBlock
#print axioms WakkerInfra.ProductPref.stickFromExchange_acrossK_of_additiveRep
#print axioms WakkerInfra.ProductPref.diagAllCells_of_stickAt0_and_kBlock

/-! ### C1.a-3 global construction (session 3) — the simultaneous closure
    (§ `OptionB_C1aSimultaneousClosure.lean`).

Session 3: the simultaneous two-compensator closure (distinct from the single stick) —
measure both the `j`-step and `k`-step against `t` at the same common interior
background, no cross-background relocation.

* `diagonalOffCal_iff_compensatorsCoincide` (pure weak order) — the off-cal diagonal
  step ⟺ the `j`- and `k`-compensators coincide at the common background. The sharpest
  single-background form of the crux.
* `compensatorsCoincide_iff_equalStepSize_of_additiveRep` — **the blockage, machine-
  checked**: coincidence IS the interior `j`-step = `k`-step utility equality (the
  cross-pair content; axis calibration gives it only on the axes).
* `compensatorsCoincide_of_additiveRep` — soundness gate.

**Honest determination:** the simultaneous closure reduces the crux to a single-background
compensator coincidence (sharpest form, no relocation), but §B proves that coincidence IS
the interior step-size equality = the cross-pair target. Seventh machine-checked
confirmation the crux is irreducible; the classical lever (`standard_sequence_unique` via
value-level `hStrict`) is blocked (`hStrict` not free). The §6 fallback stands. Audit
`[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.diagonalOffCal_iff_compensatorsCoincide
#print axioms WakkerInfra.ProductPref.compensatorsCoincide_iff_equalStepSize_of_additiveRep
#print axioms WakkerInfra.ProductPref.compensatorsCoincide_of_additiveRep

/-! ### Candidate D — the cardinal-grid companion (the wall is ordinal-specific)
    (§ `OptionB_CardinalGridCompanion.lean`).

The one alternative axiom set (`OptionB_AlternativeAxiomScoping.md`) worth building:
demonstrates the C1.a cross-pair wall is FREE given a *cardinal* grid datum — i.e. the
irreducibility is specific to the ordinal axiom set. A **companion**, NOT Wakker IV.2.7
(it assumes the cardinal scale the ordinal theorem constructs).

* `concreteDiagonalStep_free_of_cardinalGrid` / `gridThomsenClosure_free_of_cardinalGrid`
  — gate 3 (the probe, PASSES): the diagonal step / grid Thomsen closure (the ordinal
  C1.a wall) is free from `CardinalGridSliceStructure` (the grid order = the metric
  index-sum order).
* `cardinalGridSliceStructure_of_additiveRep` — gate 2: the cardinal datum is necessary
  under a rep with a strict, equal-spaced, normalized grid.

**Honest scope:** sound (gate 2 ✓), wall free given the datum (gate 3 ✓), but assumes the
cardinal scale (gate 4 — a different, weaker theorem). Localizes the ordinal difficulty:
everything downstream of the scale is free; constructing the scale from ordinal data is
the §IV.5 work. Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.concreteDiagonalStep_free_of_cardinalGrid
#print axioms WakkerInfra.ProductPref.gridThomsenClosure_free_of_cardinalGrid
#print axioms WakkerInfra.ProductPref.cardinalGridSliceStructure_of_additiveRep

/-! ### C1.a-3 — §IV.5 Thomsen-residue topology discharge (the crux wire-through)
    (§ `OptionB_C1aThomsenResidueDischarge.lean`, Route D
    `OptionB_C1aNamedInputClosure.lean`, Phase III `OptionB_C1aHexagon.lean`).

The genuine forward closure of the C1.a-3 crux from the **standard KLST structural
axiom set** (Wakker IV.2.7): A1 on `{j,k,t}` + `WakkerCoordinateTopology`
(connectedness/continuity/separability) + the documented §IV.2.6/§IV.5
measuring-stick residuals (the `DiagonalStickBracket`/`DiagonalStickMatch` reach +
matching data, each soundness-gated) + the Route C `RestrictedSolvability`
compensators.

* `tBlockDiagonalResidue_of_topology_bracket_and_match` (Phase III) — discharges the
  single `t`-block diagonal Thomsen residue from `WakkerCoordinateTopology` + the
  named measuring-stick residuals at one orientation.
* `crossPairCancellationData_of_klst` — the **full cross-pair data** from A1 +
  topology + the residuals at the three permuted orientations (Phase IV core); the
  three block residues are the same Thomsen statement at permuted coordinate roles.
* `c1a3NamedInputs_of_klst` — rebuilds Route D's `C1a3NamedInputs` bundle with both
  §IV.5 diagonal residues (`kdiag`/`jdiag`) topology-discharged (Phase III at the
  `K`/`J` orientations + the permutation equivalences).
* `c1a3_of_klst` — the **off-cal diagonal crux step** from A1 + topology + the
  measuring-stick residuals + the Route C interior compensators, delegating to
  Route D's `diagonalOffCalAtSt_of_namedInputs` over the topology-discharged bundle.
* `*_of_klst_additiveRep` — soundness gates (the routes are sound under a rep).

**Honest determination.**  This is a *carried-named-input* discharge, parallel to
Route D — NOT a foundational-clean elimination.  Phase IV(b) discharges the two
diagonal Thomsen residues Route D carried, from the `WakkerCoordinateTopology`
bundle.  The genuinely-open content is now exactly the documented §IV.2.6 Archimedean
reach + §IV.5 Thomsen matching measuring-stick residuals (`DiagonalStickBracket`/
`DiagonalStickMatch`/sep/compensation), carried as explicit, necessity-proven
structural inputs, plus the Route C solvability compensators — the intended Wakker
IV.2.7 / KLST assumption set.  Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_topology_bracket_and_match
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_klst
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_klst_additiveRep
#print axioms WakkerInfra.ProductPref.c1a3NamedInputs_of_klst
#print axioms WakkerInfra.ProductPref.c1a3_of_klst
#print axioms WakkerInfra.ProductPref.c1a3NamedInputs_of_klst_additiveRep
