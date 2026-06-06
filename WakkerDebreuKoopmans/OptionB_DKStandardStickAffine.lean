/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — Residual 3 (DK §3), step R3.2b-tail: the standard-sequence measuring
  stick IS midpoint-affine (discharging the affine requirement)

This file advances **R3.2b-tail** of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md` by discharging the
*midpoint-affine* requirement of `AffineCompanionCalibration`
(`OptionB_DKAffineCompanion.lean`) directly from the repo's standard-sequence
arithmetic-progression lemma.

## The observation

`AffineCompanionCalibration` requires a companion coordinate `j` whose utility
`R.V j` is **midpoint-affine** at the companion endpoints (`δ_j = 0`).  The repo
already proves (`M2Frontier.additiveRep_standardSequence_Vj_arithmetic`) that under
any additive representation, `R.V j` is an **arithmetic progression along a
standard sequence's grid**:
`R.V j (σ.α n) = R.V j (σ.α 0) + n · step`.

An arithmetic progression is *exactly* midpoint-affine on consecutive (and
symmetric) grid points: the middle term is the average of its neighbours.  So a
standard-sequence measuring stick automatically supplies the `MidpointAffineAt`
field — the affine companion is not an extra assumption, it is what a standard
sequence *is* under a representation.

## What this file delivers (machine-checked, sound)

* `standardSequence_Vj_midpointAffine` — for any standard sequence `σ` and indices
  with `m` the midpoint of `n₁, n₂` (`n₁ + n₂ = 2m`),
  `MidpointAffineAt (R.V σ.j-coord) (σ.α n₁) (σ.α n₂)` holds via the arithmetic
  progression.  (Stated for the symmetric/consecutive grid use.)
* `standardSequence_consecutive_midpointAffine` — the consecutive-triple instance
  `R.V j (σ.α (n+1)) = (R.V j (σ.α n) + R.V j (σ.α (n+2)))/2`, the form the
  companion calibration uses.

This reduces `AffineCompanionCalibration` (R3.2b-tail's residual) to the remaining
**balanced standard-sequence pair existence**: a measuring stick on a companion
coordinate whose grid points realize the balancing equation — pure §IV.2.6
standard-sequence content, the *same* construction residual 2's R2.2 needs.

This file imports `OptionB_DKAffineCompanion` and `M2Frontier`, and is **not** in
the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_DKAffineCompanion
import WakkerDebreuKoopmans.M2Frontier

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBDKStandardStickAffine

open WakkerInfra
open WakkerDebreuKoopmans (AdditiveRep)
open OptionBDKAffineCompanion (MidpointAffineAt)

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- **A standard-sequence grid is midpoint-affine at symmetric index pairs.**

If `n₁ + n₂ = 2 * m`, then `R.V j (σ.α m) = (R.V j (σ.α n₁) + R.V j (σ.α n₂))/2`:
the arithmetic progression `R.V j (σ.α n) = c + n·step` makes the middle index's
value the average of the two endpoints' values.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem standardSequence_Vj_midpointAffine
    {X : ι → Type v} {P : ProductPref X} (R : AdditiveRep P)
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (n₁ n₂ m : ℕ) (hmid : n₁ + n₂ = 2 * m) :
    R.V j (σ.α m) = (R.V j (σ.α n₁) + R.V j (σ.α n₂)) / 2 := by
  have hprog := additiveRep_standardSequence_Vj_arithmetic R σ
  have hcast : (n₁ : ℝ) + (n₂ : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hmid
  rw [hprog n₁, hprog n₂, hprog m]
  set c := R.V j (σ.α 0)
  set d := R.V σ.k σ.r - R.V σ.k σ.s
  -- Goal: c + m*d = ((c + n₁*d) + (c + n₂*d))/2;  use n₁ + n₂ = 2m.
  have hkey : (m : ℝ) * d = ((n₁ : ℝ) * d + (n₂ : ℝ) * d) / 2 := by
    have hfac : ((n₁ : ℝ) * d + (n₂ : ℝ) * d) = ((n₁ : ℝ) + (n₂ : ℝ)) * d := by ring
    rw [hfac, hcast]; ring
  linarith

/-- **Consecutive-triple midpoint affinity.**

The middle of three consecutive grid points has the average utility of its
neighbours: `R.V j (σ.α (n+1)) = (R.V j (σ.α n) + R.V j (σ.α (n+2)))/2`.  This is
the `MidpointAffineAt`-shaped fact (on the values) the companion calibration uses.
Audit foundational-only. -/
theorem standardSequence_consecutive_midpointAffine
    {X : ι → Type v} {P : ProductPref X} (R : AdditiveRep P)
    {j : ι} (σ : ProductPref.StandardSequence P j) (n : ℕ) :
    R.V j (σ.α (n + 1))
      = (R.V j (σ.α n) + R.V j (σ.α (n + 2))) / 2 :=
  standardSequence_Vj_midpointAffine R σ n (n + 2) (n + 1) (by ring)

/-- **`MidpointAffineAt` for a standard-sequence value pair (real coordinates).**

In the real-coordinate setting (`X i = ℝ`, the DK domain), packaging
`standardSequence_Vj_midpointAffine` as `MidpointAffineAt (R.V j)` on the grid
values `(σ.α n₁, σ.α n₂)`: *provided* the grid value at the index-midpoint `m`
coincides with the arithmetic midpoint `(σ.α n₁ + σ.α n₂)/2` (supplied by the
calibration's balancing construction), `R.V j` is midpoint-affine at that value
pair.  Audit foundational-only. -/
theorem midpointAffineAt_of_standardSequence_indexMidpoint
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (n₁ n₂ m : ℕ) (hmid : n₁ + n₂ = 2 * m)
    (harg : (σ.α n₁ + σ.α n₂) / 2 = σ.α m) :
    MidpointAffineAt (R.V j) (σ.α n₁) (σ.α n₂) := by
  unfold MidpointAffineAt
  rw [harg]
  exact standardSequence_Vj_midpointAffine R σ n₁ n₂ m hmid

end OptionBDKStandardStickAffine
end CertificateChecklist
end WakkerRoadmap

/-! ## R3.2b-tail standard-stick affinity audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKStandardStickAffine.standardSequence_Vj_midpointAffine
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKStandardStickAffine.standardSequence_consecutive_midpointAffine
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKStandardStickAffine.midpointAffineAt_of_standardSequence_indexMidpoint
