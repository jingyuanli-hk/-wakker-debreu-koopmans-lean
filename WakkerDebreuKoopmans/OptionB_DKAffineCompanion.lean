/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — Residual 3 (DK §3), step R3.2b-tail: single-coordinate midpoint
  concavity from an affine companion

This file executes the next sound forward step of **R3.2b-tail** of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`, building on the
cross-coordinate midpoint core (`OptionB_DKTwoCoordMidpoint.lean`).

## The separation, made precise

R3.2b core proved: for `i ≠ j` at a *balanced* two-coordinate configuration
(`V_i xi + V_j aj = V_i yi + V_j bj`), global quasiconcavity forces the **joint**
midpoint-deficit nonnegativity `δ_i + δ_j ≥ 0`, where
`δ_f(u,v) = V_f((u+v)/2) - (V_f u + V_f v)/2`.

To isolate **`δ_i ≥ 0`** (midpoint concavity of `V_i` alone) we need the companion
coordinate `j` to contribute **`δ_j = 0`** at its endpoints — i.e. `V_j` is
*midpoint-affine* on `(aj, bj)`.  That is exactly the role of a Wakker
standard-sequence **measuring stick**: its grid points are equally spaced, so its
utility is affine on the grid (`V_j` advances by a constant per step).  This is the
genuine `n ≥ 3` content (a third/companion coordinate calibrating the deficit).

## What this file delivers (machine-checked, sound)

* `MidpointConcaveAt` / `MidpointAffineAt` — the per-point midpoint predicates.
* `midpointConcaveAt_of_affineCompanion` — **the separation**: from global
  quasiconcavity, a companion coordinate `j ≠ i`, endpoints `(aj, bj)` that are
  (1) **balanced** with the target and (2) **midpoint-affine** for `V_j`, and the
  two profiles in `D`, conclude `MidpointConcaveAt (R.V i) xi yi`.  Pure `linarith`
  from `twoCoord_sum_midpointDeficit_nonneg`.
* `midpointConcaveAt_of_affineCompanion_convexPref` — packaged from `ConvexPref`.

This reduces R3.2b-tail to the **existence of an affine companion calibration**
(`AffineCompanionCalibration` below): for each target `(xi, yi)` on coordinate `i`,
a companion coordinate `j` with balanced, midpoint-affine endpoints and both
profiles in `D`.  Constructing that calibration from restricted solvability + the
standard-sequence measuring stick (`n ≥ 3`) is the genuine remaining DK §3 /
Wakker §IV.2.6 work; `sliceMidpointConcavity_of_concaveOn`
(`OptionB_DKConcavityEndpoint.lean`) proves the per-summand target necessary.

This file imports `OptionB_DKTwoCoordMidpoint` and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_DKTwoCoordMidpoint

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBDKAffineCompanion

open WakkerInfra
open WakkerDebreuKoopmans (AdditiveRep)
open OptionBDKGlobalQuasiconcavity (additiveSum)
open OptionBDKTwoCoordMidpoint

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- `f` is **midpoint-concave at the pair `(u, v)`**: `(f u + f v)/2 ≤ f((u+v)/2)`.
The per-point content of `SliceMidpointConcavityCertificate`. -/
def MidpointConcaveAt (f : ℝ → ℝ) (u v : ℝ) : Prop :=
  (f u + f v) / 2 ≤ f ((u + v) / 2)

/-- `f` is **midpoint-affine at the pair `(u, v)`**: `f((u+v)/2) = (f u + f v)/2`
(zero midpoint deficit).  A standard-sequence measuring stick is midpoint-affine on
its equally-spaced grid. -/
def MidpointAffineAt (f : ℝ → ℝ) (u v : ℝ) : Prop :=
  f ((u + v) / 2) = (f u + f v) / 2

/-- **R3.2b-tail separation: single-coordinate midpoint concavity from an affine
companion.**

Given the additive sum quasiconcave on `D` (R3.2a, from convex preference), a
companion coordinate `j ≠ i`, and companion endpoints `(aj, bj)` that are

* **balanced** with the target: `R.V i xi + R.V j aj = R.V i yi + R.V j bj`, and
* **midpoint-affine** for `R.V j`: `MidpointAffineAt (R.V j) aj bj`,

with both two-coordinate profiles in `D`, the target coordinate `i` is
**midpoint-concave at `(xi, yi)`**: `MidpointConcaveAt (R.V i) xi yi`.

This is the honest DK §3 deficit separation: the companion's vanishing deficit
turns the joint `δ_i + δ_j ≥ 0` into `δ_i ≥ 0`.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem midpointConcaveAt_of_affineCompanion
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {D : Set (ι → ℝ)} (hQ : QuasiconcaveOn ℝ D (additiveSum R))
    {i j : ι} (hij : i ≠ j) (a : ι → ℝ) (xi yi aj bj : ℝ)
    (hp : Function.update (Function.update a i xi) j aj ∈ D)
    (hq : Function.update (Function.update a i yi) j bj ∈ D)
    (hbal : R.V i xi + R.V j aj = R.V i yi + R.V j bj)
    (haff : MidpointAffineAt (R.V j) aj bj) :
    MidpointConcaveAt (R.V i) xi yi := by
  -- Joint deficit nonnegativity from R3.2b core.
  have hjoint := twoCoord_sum_midpointDeficit_nonneg R hQ hij a xi yi aj bj hp hq hbal
  -- Companion deficit vanishes.
  unfold MidpointConcaveAt
  unfold MidpointAffineAt at haff
  -- hjoint : 0 ≤ (V_i mid_i - (V_i xi + V_i yi)/2) + (V_j mid_j - (V_j aj + V_j bj)/2)
  -- haff   : V_j mid_j = (V_j aj + V_j bj)/2, so the second bracket is 0.
  rw [haff] at hjoint
  linarith

/-- **R3.2b-tail separation, packaged from `ConvexPref`.**

Same as `midpointConcaveAt_of_affineCompanion` but taking convex preference
directly (composing R3.2a).  Audit foundational-only. -/
theorem midpointConcaveAt_of_affineCompanion_convexPref
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {D : Set (ι → ℝ)} (hConvex : WakkerInfra.ProductPref.ConvexPref P D)
    {i j : ι} (hij : i ≠ j) (a : ι → ℝ) (xi yi aj bj : ℝ)
    (hp : Function.update (Function.update a i xi) j aj ∈ D)
    (hq : Function.update (Function.update a i yi) j bj ∈ D)
    (hbal : R.V i xi + R.V j aj = R.V i yi + R.V j bj)
    (haff : MidpointAffineAt (R.V j) aj bj) :
    MidpointConcaveAt (R.V i) xi yi :=
  midpointConcaveAt_of_affineCompanion R
    (OptionBDKGlobalQuasiconcavity.additiveSum_quasiconcaveOn_of_convexPref R hConvex)
    hij a xi yi aj bj hp hq hbal haff

/-- **Affine companion calibration (the isolated R3.2b-tail residual).**

For coordinate `i` on slice `S i`, and every target pair `(xi, yi)` in `S i`,
there is a companion coordinate `j ≠ i`, a background `a`, and companion endpoints
`(aj, bj)` that are balanced with the target and midpoint-affine for `R.V j`, with
both two-coordinate profiles in `D`.

This is exactly the standard-sequence measuring-stick existence (the `n ≥ 3` +
restricted-solvability content).  Once supplied, `sliceMidpointConcavity_of_affineCompanionCalibration`
below yields the per-coordinate midpoint concavity that `debreu_koopmans_hard_of_per_pair_continuity_midpoint`
consumes. -/
def AffineCompanionCalibration
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (D : Set (ι → ℝ)) (S : ι → Set ℝ) (i : ι) : Prop :=
  ∀ xi ∈ S i, ∀ yi ∈ S i,
    ∃ (j : ι) (a : ι → ℝ) (aj bj : ℝ),
      i ≠ j ∧
      Function.update (Function.update a i xi) j aj ∈ D ∧
      Function.update (Function.update a i yi) j bj ∈ D ∧
      R.V i xi + R.V j aj = R.V i yi + R.V j bj ∧
      MidpointAffineAt (R.V j) aj bj

/-- **Per-coordinate midpoint concavity from the affine companion calibration.**

If coordinate `i` admits an affine companion calibration on its slice `S i` (and
the additive sum is quasiconcave on `D`, from convex preference), then `R.V i` is
midpoint-concave at every pair in `S i` — i.e. the single-slice content of
`SliceMidpointConcavityCertificate`.  Audit foundational-only. -/
theorem sliceMidpointConcavity_of_affineCompanionCalibration
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {D : Set (ι → ℝ)} (hQ : QuasiconcaveOn ℝ D (additiveSum R))
    {S : ι → Set ℝ} {i : ι}
    (hcal : AffineCompanionCalibration R D S i) :
    ∀ xi ∈ S i, ∀ yi ∈ S i, MidpointConcaveAt (R.V i) xi yi := by
  intro xi hxi yi hyi
  obtain ⟨j, a, aj, bj, hij, hp, hq, hbal, haff⟩ := hcal xi hxi yi hyi
  exact midpointConcaveAt_of_affineCompanion R hQ hij a xi yi aj bj hp hq hbal haff

end OptionBDKAffineCompanion
end CertificateChecklist
end WakkerRoadmap

/-! ## R3.2b-tail affine-companion separation audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKAffineCompanion.midpointConcaveAt_of_affineCompanion
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKAffineCompanion.midpointConcaveAt_of_affineCompanion_convexPref
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKAffineCompanion.sliceMidpointConcavity_of_affineCompanionCalibration
