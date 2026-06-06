/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — shared §IV.2.6 measuring stick: `CoordinateStandardSequenceExtensionData`
  from continuity + unboundedness

This file executes a genuine forward step on the **shared standard-sequence
measuring-stick** input that both residual 2 (R2.2) and residual 3 (R3.2b-tail)
bottom out at (per `OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`).

## What it discharges

`M2Frontier.CoordinateStandardSequenceExtensionData (P := P)` —
`∀ i, ∃ k ≠ i, ∃ base, ∀ r s, r ≠ s → OneStepExtensible P i base k r s` — is the
one-step extension interface consumed by `extend_to_standard_sequence` (and hence
by the rational-bisection / mesh-family / affine-companion machinery).

The repo's `ConstructionStack.oneStepExtensible_of_continuity_unbounded` already
proves a single `OneStepExtensible` from `Continuous (R.V i)` +
`CoordinateUtilityUnboundedCertificate R i` (an additive-representation IVT).  This
file lifts that to the **full extension-data interface** by quantifying over `i`,
choosing the companion `k ≠ i` from `3 ≤ card ι` (the X3 selector), and discharging
`OneStepExtensible` for every reference exchange.

## What this file delivers (machine-checked, sound)

* `coordinateStandardSequenceExtensionData_of_continuous_unbounded` — from
  `∀ i, Continuous (R.V i)` and `∀ i, CoordinateUtilityUnboundedCertificate R i`
  (with `3 ≤ card ι`), the full `CoordinateStandardSequenceExtensionData`.
* `coordinateRationalRefinementBisection_of_continuous_unbounded_rationalImage` —
  feeding it into the repo's rational-bisection theorem: with rational-image
  coverage added, the rational refinement/bisection certificate holds (the R2.2
  chain, now needing only continuity + unboundedness + rational image).
* `coordinateUtilityRefinedMeshFamily_of_continuous_unbounded_rationalImage` — the
  mesh family itself (residual 2's sound target) from the same inputs.

This reduces the **shared** measuring-stick residual to: continuity +
unboundedness + rational-image coverage of the coordinate utilities — all of which
are downstream of the genuine §IV.2.6 standard-sequence construction, but now
assembled into the exact interface the mesh family and affine companion consume.

This file imports `M2Frontier` and `ConstructionStack` and is **not** in the
umbrella import.
-/

import WakkerDebreuKoopmans.M2Frontier
import WakkerDebreuKoopmans.ConstructionStack
import WakkerDebreuKoopmans.OptionB_ResidualSharedInfrastructure

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBExtensionDataFromContinuity

open WakkerInfra
open WakkerDebreuKoopmans (AdditiveRep)

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- **Shared measuring-stick step: `CoordinateStandardSequenceExtensionData` from
continuity + unboundedness.**

With `3 ≤ Fintype.card ι`, an additive representation `R` whose every coordinate
utility is continuous and unbounded supplies the full one-step extension interface:
for each `i`, pick a companion `k ≠ i` (X3 selector), any base, and discharge
`OneStepExtensible P i base k r s` for every reference exchange via
`oneStepExtensible_of_continuity_unbounded` (the additive-representation IVT).
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem coordinateStandardSequenceExtensionData_of_continuous_unbounded
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (hCont : ∀ i, Continuous (R.V i))
    (hUnb : ∀ i, CoordinateUtilityUnboundedCertificate R i) :
    CoordinateStandardSequenceExtensionData (P := P) := by
  intro i
  -- Companion coordinate k ≠ i from 3 ≤ card ι (use X3 with j := i).
  obtain ⟨k, hki, _⟩ := WakkerInfra.ProductPref.exists_third_coordinate (ι := ι) i i
  refine ⟨k, hki, fun _ => (0 : ℝ), ?_⟩
  intro r s _hrs
  exact oneStepExtensible_of_continuity_unbounded R hki (fun _ => 0) r s
    (hCont i) (hUnb i)

/-- **Rational refinement/bisection from continuity + unboundedness + rational
image.**

Feeds the extension data discharged above into the repo's
`coordinateRationalRefinementBisectionCertificate_of_rationalImage_and_extensionData`:
with rational-image coverage added, the rational refinement/bisection certificate
(residual 2's R2.2 standard-sequence-shaped output) holds.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem coordinateRationalRefinementBisection_of_continuous_unbounded_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hCont : ∀ i, Continuous (R.V i))
    (hUnb : ∀ i, CoordinateUtilityUnboundedCertificate R i)
    (hRat : CoordinateRationalImageCertificate R) :
    CoordinateRationalRefinementBisectionCertificate R :=
  coordinateRationalRefinementBisectionCertificate_of_rationalImage_and_extensionData
    R hsolv hRat
    (coordinateStandardSequenceExtensionData_of_continuous_unbounded R hCont hUnb)

/-- **Refined mesh family (residual 2's sound target) from continuity +
unboundedness + rational image.**

The full residual-2 target `CoordinateUtilityRefinedMeshFamilyCertificate` from the
assembled inputs, via the repo's
`coordinateUtilityRefinedMeshFamilyCertificate_of_rationalImage_and_extensionData`.
Audit foundational-only. -/
theorem coordinateUtilityRefinedMeshFamily_of_continuous_unbounded_rationalImage
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (R : AdditiveRep P)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hCont : ∀ i, Continuous (R.V i))
    (hUnb : ∀ i, CoordinateUtilityUnboundedCertificate R i)
    (hRat : CoordinateRationalImageCertificate R) :
    CoordinateUtilityRefinedMeshFamilyCertificate R :=
  coordinateUtilityRefinedMeshFamilyCertificate_of_rationalImage_and_extensionData
    R hsolv hRat
    (coordinateStandardSequenceExtensionData_of_continuous_unbounded R hCont hUnb)

end OptionBExtensionDataFromContinuity
end CertificateChecklist
end WakkerRoadmap

/-! ## Shared measuring-stick extension-data audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBExtensionDataFromContinuity.coordinateStandardSequenceExtensionData_of_continuous_unbounded
#print axioms WakkerRoadmap.CertificateChecklist.OptionBExtensionDataFromContinuity.coordinateRationalRefinementBisection_of_continuous_unbounded_rationalImage
#print axioms WakkerRoadmap.CertificateChecklist.OptionBExtensionDataFromContinuity.coordinateUtilityRefinedMeshFamily_of_continuous_unbounded_rationalImage
