/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — Residual 2 soundness gate: the single-sequence target is REFUTED;
  the sound target is the refined mesh family

Executing R2.2/R2.3 of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md` triggered the
mandatory soundness gate (the discipline that the §5 gate, WP-CI, WP-density, and
the two WP-C1.a probes all vindicated).  The gate **fails** for the target the
infrastructure roadmap originally named, and this file records the machine-checked
correction.

## The refutation

The infrastructure roadmap's residual 2 named
`SelectedRefinedGridBetweenPointsCertificate` (equivalently
`SelectedRefinedDenseGridCertificate`): **one** strict standard sequence whose
grid is dense.  But `M2Frontier.additiveRealBool_not_selectedRefinedDenseGridCertificate_{true,false}`
already proves this is **false** in the additive-real Bool model — a model that
*has* an additive representation (`additiveRealBool_rep`).  Under any
representation, a strict standard sequence's grid is a utility arithmetic
progression (`additiveRep_standardSequence_Vj_arithmetic`), so its range is never
dense.  Hence the single-sequence target is **unsound**, not merely underivable:
no forward proof of it can exist.

`escapeGrid_singleSequence_target_is_unsound` packages this: there is a
preference with a representation for which the single-sequence target fails.

## The sound target (already in the repo)

`M2Frontier.CoordinateUtilityRefinedMeshFamilyCertificate R` — a *rational-indexed
family* of strict standard sequences whose **union** of utility images is
interval-dense.  This is sound (it holds under a representation) and is the genuine
Wakker §IV.2.6 "refinement family / mesh" target.  The repo already proves the
entire forward chain from it:

* `coordinateUtilityRefinedMeshFamilyCertificate_of_rationalImage_and_extensionData`
  — mesh family from `CoordinateRationalImageCertificate` + extension data;
* `coordinateBetweenPointsCoverageCertificate_of_refinedMeshFamilyCertificate`
  — mesh family ⇒ between-points coverage;
* `coordinateDenseRangeCertificate_of_refinedMeshFamilyCertificate`
  — ⇒ dense range (⇒ X2 continuity).

`escapeGrid_meshFamily_target_is_sound` re-exports the soundness witness: the mesh
family holds for `additiveRealBoolPref` (the very model that refutes the single
sequence), given its rational-image coverage and extension data — confirming the
re-scoped target hides nothing false.

## Determination

Residual 2's genuine remaining content is **`CoordinateRationalImageCertificate`**
(rational-image coverage of each coordinate utility) plus
`CoordinateStandardSequenceExtensionData`; everything above it (mesh family ⇒
between-points ⇒ dense range ⇒ continuity) is **already theorem-backed**.  R2.1's
bisection engine (`OptionB_EscapeGridRefinement.lean`) is the atomic step toward
rational-image coverage.  The infrastructure roadmap is corrected accordingly.

This file imports `M2Frontier` and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.M2Frontier

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBEscapeGridSoundnessGate

open WakkerInfra

/-- **Soundness gate (negative): the single-sequence escape-grid target is
unsound.**

There is a preference `Q` with an additive representation for which the
single-strict-sequence dense-grid target
`SelectedRefinedDenseGridCertificate` **fails** on some coordinate.  So the
infrastructure roadmap's original residual-2 target cannot be proved — it is false
in a genuine additive model, not merely underivable.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem escapeGrid_singleSequence_target_is_unsound :
    ∃ (Q : ProductPref (fun _ : Bool => ℝ)) (_R : WakkerDebreuKoopmans.AdditiveRep Q),
      ¬ SelectedRefinedDenseGridCertificate Q true := by
  refine ⟨additiveRealBoolPref, additiveRealBool_rep, ?_⟩
  exact additiveRealBool_not_selectedRefinedDenseGridCertificate_true

/-- **Soundness gate (positive): the refined mesh-family target is sound.**

For any preference with an additive representation, rational-image coverage plus
standard-sequence extension data yield the refined mesh family
`CoordinateUtilityRefinedMeshFamilyCertificate` — so the re-scoped residual-2
target holds whenever its genuine input (`CoordinateRationalImageCertificate`)
does.  This is the soundness witness for the corrected target.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem escapeGrid_meshFamily_target_is_sound
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : WakkerDebreuKoopmans.AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hRat : CoordinateRationalImageCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P)) :
    CoordinateUtilityRefinedMeshFamilyCertificate R :=
  coordinateUtilityRefinedMeshFamilyCertificate_of_rationalImage_and_extensionData
    R hsolv hRat hExt

/-- **Re-scoped residual 2 is theorem-backed above rational-image coverage.**

The mesh family yields between-points coverage and hence dense range (which feeds
X2 continuity) with no further open work.  So residual 2's *entire* remaining
obligation is `CoordinateRationalImageCertificate` (+ extension data); everything
downstream is proved.  Audit foundational-only. -/
theorem escapeGrid_denseRange_of_rationalImage_and_extensionData
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : WakkerDebreuKoopmans.AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hRat : CoordinateRationalImageCertificate R)
    (hExt : CoordinateStandardSequenceExtensionData (P := P)) :
    CoordinateDenseRangeCertificate R :=
  coordinateDenseRangeCertificate_of_refinedMeshFamilyCertificate R
    (escapeGrid_meshFamily_target_is_sound R hsolv hRat hExt)

end OptionBEscapeGridSoundnessGate
end CertificateChecklist
end WakkerRoadmap

/-! ## Residual 2 soundness-gate audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridSoundnessGate.escapeGrid_singleSequence_target_is_unsound
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridSoundnessGate.escapeGrid_meshFamily_target_is_sound
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridSoundnessGate.escapeGrid_denseRange_of_rationalImage_and_extensionData
