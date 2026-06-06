/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — shared §IV.2.6 measuring stick: `CoordinateRationalImageCertificate`
  from connectedness + continuity + unboundedness

This file executes the decisive forward step on the **shared** residual-2/3 input
(`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`): rational-image
coverage of the coordinate utilities, which was the last named open input feeding
both the residual-2 mesh family and residual-3's affine companion.

## What it discharges

`M2Frontier.CoordinateRationalImageCertificate R` (`∀ i q, ∃ x, R.V i x = q`) was
flagged as the genuine remaining §IV.2.6 content.  It turns out to be **already
derivable** from the topology bundle:

* `Topology.coordinateSurjectivityCertificate_of_connected_continuous_unbounded`
  — surjectivity of each `R.V i` from `ConnectedCoordinates` + continuity +
  unboundedness (preconnected unbounded image ⟹ all of `ℝ`);
* `M2Frontier.coordinateRationalImageCertificate_of_coordinateSurjectivityCertificate`
  — rational image from surjectivity;
* `Topology.connectedCoordinates_realProduct` — `ConnectedCoordinates` is **free**
  for real coordinates (`ℝ` is connected).

So rational image follows from **continuity + unboundedness alone** (connectedness
is automatic).

## What this file delivers (machine-checked, sound)

* `coordinateRationalImage_of_continuous_unbounded` — `CoordinateRationalImageCertificate`
  from `∀ i, Continuous (R.V i)` + `∀ i, CoordinateUtilityUnboundedCertificate R i`.
* `coordinateUtilityRefinedMeshFamily_of_continuous_unbounded` — **residual 2's
  sound target** (the mesh family) from continuity + unboundedness + solvability,
  with rational image now discharged (composing the previous file).
* `coordinateDenseRange_of_continuous_unbounded` — dense range of each utility from
  continuity + unboundedness (the X2 continuity input is then theorem-backed too).

This reduces the entire residual-2/3 §IV.2.6 frontier to the **topology bundle**
(`∀ i, Continuous (R.V i)` + unboundedness), which is the genuine Wakker IV.2.3
analytic content — and which the construction stack produces from the structural
axioms via the standard-sequence/monotonicity route.  Only R1.1 (the §IV.5 grid
Thomsen cross-pair crux) now stands separately.

This file imports the previous extension-data file, `Topology`, and `M2Frontier`,
and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_ExtensionDataFromContinuity
import WakkerDebreuKoopmans.Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBRationalImageFromTopology

open WakkerInfra
open WakkerDebreuKoopmans (AdditiveRep)

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- **Rational-image coverage from continuity + unboundedness.**

`CoordinateRationalImageCertificate R` from `∀ i, Continuous (R.V i)` and
`∀ i, CoordinateUtilityUnboundedCertificate R i`.  `ConnectedCoordinates` is free
for real coordinates (`connectedCoordinates_realProduct`), so surjectivity follows
(`coordinateSurjectivityCertificate_of_connected_continuous_unbounded`), and
rational image is its corollary.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem coordinateRationalImage_of_continuous_unbounded
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hCont : ∀ i, Continuous (R.V i))
    (hUnb : ∀ i, CoordinateUtilityUnboundedCertificate R i) :
    CoordinateRationalImageCertificate R :=
  coordinateRationalImageCertificate_of_coordinateSurjectivityCertificate R
    (coordinateSurjectivityCertificate_of_connected_continuous_unbounded R
      (connectedCoordinates_realProduct P) hCont hUnb)

/-- **Dense range of each coordinate utility from continuity + unboundedness.**

Composes rational image ⇒ between-points ⇒ dense range.  This makes the X2
continuity input (`coordinateUtilityContinuityCertificate_univ_of_monotone_denseRange`)
theorem-backed from the same topology data.  Audit foundational-only. -/
theorem coordinateDenseRange_of_continuous_unbounded
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hCont : ∀ i, Continuous (R.V i))
    (hUnb : ∀ i, CoordinateUtilityUnboundedCertificate R i) :
    CoordinateDenseRangeCertificate R :=
  coordinateDenseRangeCertificate_of_coordinateBetweenPointsCoverageCertificate R
    (coordinateBetweenPointsCoverageCertificate_of_coordinateRationalImageCertificate R
      (coordinateRationalImage_of_continuous_unbounded R hCont hUnb))

/-- **Residual 2's mesh family from continuity + unboundedness + solvability.**

With rational image now discharged from the topology data, the refined mesh family
(residual 2's sound target) follows.  Composes
`coordinateRationalImage_of_continuous_unbounded` into
`coordinateUtilityRefinedMeshFamily_of_continuous_unbounded_rationalImage`.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem coordinateUtilityRefinedMeshFamily_of_continuous_unbounded
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hCont : ∀ i, Continuous (R.V i))
    (hUnb : ∀ i, CoordinateUtilityUnboundedCertificate R i) :
    CoordinateUtilityRefinedMeshFamilyCertificate R :=
  OptionBExtensionDataFromContinuity.coordinateUtilityRefinedMeshFamily_of_continuous_unbounded_rationalImage
    R hsolv hCont hUnb
    (coordinateRationalImage_of_continuous_unbounded R hCont hUnb)

end OptionBRationalImageFromTopology
end CertificateChecklist
end WakkerRoadmap

/-! ## Rational-image-from-topology audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBRationalImageFromTopology.coordinateRationalImage_of_continuous_unbounded
#print axioms WakkerRoadmap.CertificateChecklist.OptionBRationalImageFromTopology.coordinateDenseRange_of_continuous_unbounded
#print axioms WakkerRoadmap.CertificateChecklist.OptionBRationalImageFromTopology.coordinateUtilityRefinedMeshFamily_of_continuous_unbounded
