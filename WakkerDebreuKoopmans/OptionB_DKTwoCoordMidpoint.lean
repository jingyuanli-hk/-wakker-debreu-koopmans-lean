/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — Residual 3 (DK §3), step R3.2b core: the cross-coordinate midpoint
  lemma from global quasiconcavity

This file proves the genuine forward core of **R3.2b** of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`: the
Debreu–Koopmans §3 cross-coordinate midpoint inequality, derived from the global
quasiconcavity of the additive sum established in R3.2a
(`OptionB_DKGlobalQuasiconcavity.lean`).

## The genuine content

The R3.2 derivability probe (`OptionB_DKMidpointProbe.lean`) showed quasiconcavity
of a *single* function does not give its midpoint concavity.  The DK §3 way out is
to use a **second coordinate** as a compensating measuring stick (the `n ≥ 3`
content).  This file makes that precise and proves the sound consequence:

* take two distinct coordinates `i, j`, a background `a`, endpoint values
  `xi, yi` (coord `i`) and `aj, bj` (coord `j`) chosen so the two profiles
  `p = a[i↦xi, j↦aj]` and `q = a[i↦yi, j↦bj]` have **equal additive sum**;
* then global quasiconcavity of the sum (its super-level sets are convex) forces
  the midpoint to be weakly above the common level, which decodes to the
  **joint** midpoint inequality
  `V_i xi + V_j aj ≤ V_i((xi+yi)/2) + V_j((aj+bj)/2)`.

Equivalently (`twoCoord_sum_midpointDeficit_nonneg`), the **sum of the two
coordinates' midpoint deficits is `≥ 0`**:
`δ_i + δ_j ≥ 0` where `δ_f(u,v) = f((u+v)/2) - (f u + f v)/2`.

## Why this is the honest core (and what remains, R3.2b-tail)

This is a real theorem (sound, machine-checked), and it is exactly the cross-pair
content DK §3 produces.  It does **not** yet give midpoint concavity of `V_i`
*alone*: that requires isolating `δ_i ≥ 0` from `δ_i + δ_j ≥ 0`, which DK achieves
by running the same argument with a *third* coordinate to pin `δ_j` (the `n ≥ 3`
separation).  That separation is the precisely-isolated remaining gap (R3.2b-tail);
the per-summand target `SliceMidpointConcavityCertificate` is proved *necessary* in
`OptionB_DKConcavityEndpoint.sliceMidpointConcavity_of_concaveOn`.

This file imports `OptionB_DKGlobalQuasiconcavity` and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_DKGlobalQuasiconcavity

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBDKTwoCoordMidpoint

open WakkerInfra
open WakkerDebreuKoopmans (AdditiveRep)
open OptionBDKGlobalQuasiconcavity (additiveSum)

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The additive sum of a two-coordinate update splits off the two coordinates
plus a base remainder over the other coordinates. -/
private lemma additiveSum_twoUpdate
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (a : ι → ℝ) {i j : ι} (hij : i ≠ j) (u v : ℝ) :
    additiveSum R (Function.update (Function.update a i u) j v)
      = R.V i u + R.V j v
        + ∑ t ∈ (Finset.univ.erase i).erase j, R.V t (a t) := by
  unfold additiveSum
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (show j ∈ Finset.univ.erase i from
        Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
  have hi : (Function.update (Function.update a i u) j v) i = u := by
    rw [Function.update_of_ne hij, Function.update_self]
  have hj : (Function.update (Function.update a i u) j v) j = v := by
    rw [Function.update_self]
  rw [hi, hj]
  have hrest : (∑ t ∈ (Finset.univ.erase i).erase j,
        R.V t (Function.update (Function.update a i u) j v t))
      = ∑ t ∈ (Finset.univ.erase i).erase j, R.V t (a t) := by
    apply Finset.sum_congr rfl
    intro t ht
    have htj : t ≠ j := Finset.ne_of_mem_erase ht
    have hti : t ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht)
    rw [Function.update_of_ne htj, Function.update_of_ne hti]
  rw [hrest]; ring

/-- The `½`–`½` convex combination of the two endpoint profiles is the
two-coordinate **midpoint** update. -/
private lemma half_combo_eq_midpoint
    (a : ι → ℝ) {i j : ι} (xi yi aj bj : ℝ) :
    (1/2 : ℝ) • (Function.update (Function.update a i xi) j aj)
      + (1/2 : ℝ) • (Function.update (Function.update a i yi) j bj)
      = Function.update (Function.update a i ((xi + yi)/2)) j ((aj + bj)/2) := by
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.update_apply]
  split_ifs <;> ring

/-- **R3.2b core — the cross-coordinate midpoint inequality.**

Let `R` represent `P`, let the additive sum be quasiconcave on `D` (R3.2a, from
convex preference), let `i ≠ j`, and let the two profiles
`p = a[i↦xi, j↦aj]`, `q = a[i↦yi, j↦bj]` lie in `D` with **equal additive
contribution on `{i,j}`** (`R.V i xi + R.V j aj = R.V i yi + R.V j bj`).  Then

`R.V i xi + R.V j aj ≤ R.V i ((xi+yi)/2) + R.V j ((aj+bj)/2)`.

This is the genuine Debreu–Koopmans §3 cross-pair midpoint consequence of global
quasiconcavity.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem twoCoord_midpoint_ge_of_quasiconcave
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {D : Set (ι → ℝ)} (hQ : QuasiconcaveOn ℝ D (additiveSum R))
    {i j : ι} (hij : i ≠ j) (a : ι → ℝ) (xi yi aj bj : ℝ)
    (hp : Function.update (Function.update a i xi) j aj ∈ D)
    (hq : Function.update (Function.update a i yi) j bj ∈ D)
    (hsum : R.V i xi + R.V j aj = R.V i yi + R.V j bj) :
    R.V i xi + R.V j aj ≤ R.V i ((xi + yi)/2) + R.V j ((aj + bj)/2) := by
  classical
  set p : ι → ℝ := Function.update (Function.update a i xi) j aj with hpdef
  set q : ι → ℝ := Function.update (Function.update a i yi) j bj with hqdef
  -- Score splits.
  have hΦp : additiveSum R p
      = R.V i xi + R.V j aj
        + ∑ t ∈ (Finset.univ.erase i).erase j, R.V t (a t) :=
    additiveSum_twoUpdate R a hij xi aj
  have hΦq : additiveSum R q
      = R.V i yi + R.V j bj
        + ∑ t ∈ (Finset.univ.erase i).erase j, R.V t (a t) :=
    additiveSum_twoUpdate R a hij yi bj
  -- Equal additive contribution ⟹ equal sums.
  have hpq_eq : additiveSum R p = additiveSum R q := by
    rw [hΦp, hΦq]; linarith
  -- Both endpoints lie in the super-level set of the sum at level `Φ p`.
  have hpmem : p ∈ {x ∈ D | additiveSum R p ≤ additiveSum R x} :=
    Set.mem_sep hp (le_refl _)
  have hqmem : q ∈ {x ∈ D | additiveSum R p ≤ additiveSum R x} :=
    Set.mem_sep hq (le_of_eq hpq_eq)
  -- Quasiconcavity: the ½–½ combination stays in the super-level set.
  have hmid := hQ (additiveSum R p) hpmem hqmem (by norm_num) (by norm_num)
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  rcases hmid with ⟨_hmidD, hmid_ge⟩
  -- The ½–½ combination is the midpoint two-update.
  have hcombo : (1/2 : ℝ) • p + (1/2 : ℝ) • q
      = Function.update (Function.update a i ((xi + yi)/2)) j ((aj + bj)/2) := by
    rw [hpdef, hqdef]; exact half_combo_eq_midpoint a xi yi aj bj
  rw [hcombo, additiveSum_twoUpdate R a hij ((xi + yi)/2) ((aj + bj)/2)] at hmid_ge
  -- hmid_ge : Φ p ≤ V_i mid_i + V_j mid_j + rest;  rewrite Φ p.
  rw [hΦp] at hmid_ge
  linarith

/-- **R3.2b core (deficit form) — the two midpoint deficits sum to `≥ 0`.**

Under the same hypotheses, writing the per-coordinate midpoint deficit
`δ_f(u,v) := f((u+v)/2) - (f u + f v)/2`, the deficits of the two coordinates sum
to a nonnegative number:

`(R.V i ((xi+yi)/2) - (R.V i xi + R.V i yi)/2)
   + (R.V j ((aj+bj)/2) - (R.V j aj + R.V j bj)/2) ≥ 0`.

This is the clean DK §3 cross-pair statement: global quasiconcavity forces the
*joint* midpoint deficit nonnegative.  Isolating a single coordinate's deficit
`≥ 0` (i.e. its midpoint concavity) is the remaining `n ≥ 3` separation.  Audit
foundational-only. -/
theorem twoCoord_sum_midpointDeficit_nonneg
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {D : Set (ι → ℝ)} (hQ : QuasiconcaveOn ℝ D (additiveSum R))
    {i j : ι} (hij : i ≠ j) (a : ι → ℝ) (xi yi aj bj : ℝ)
    (hp : Function.update (Function.update a i xi) j aj ∈ D)
    (hq : Function.update (Function.update a i yi) j bj ∈ D)
    (hsum : R.V i xi + R.V j aj = R.V i yi + R.V j bj) :
    0 ≤ (R.V i ((xi + yi)/2) - (R.V i xi + R.V i yi)/2)
        + (R.V j ((aj + bj)/2) - (R.V j aj + R.V j bj)/2) := by
  have hge := twoCoord_midpoint_ge_of_quasiconcave R hQ hij a xi yi aj bj hp hq hsum
  linarith

/-- **R3.2b core from convex preference (corollary).**

Packages R3.2a + the cross-coordinate midpoint lemma: from `ConvexPref P D` and a
representation, the two-coordinate midpoint inequality holds directly (no separate
quasiconcavity hypothesis).  Audit foundational-only. -/
theorem twoCoord_midpoint_ge_of_convexPref
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {D : Set (ι → ℝ)} (hConvex : WakkerInfra.ProductPref.ConvexPref P D)
    {i j : ι} (hij : i ≠ j) (a : ι → ℝ) (xi yi aj bj : ℝ)
    (hp : Function.update (Function.update a i xi) j aj ∈ D)
    (hq : Function.update (Function.update a i yi) j bj ∈ D)
    (hsum : R.V i xi + R.V j aj = R.V i yi + R.V j bj) :
    R.V i xi + R.V j aj ≤ R.V i ((xi + yi)/2) + R.V j ((aj + bj)/2) :=
  twoCoord_midpoint_ge_of_quasiconcave R
    (OptionBDKGlobalQuasiconcavity.additiveSum_quasiconcaveOn_of_convexPref R hConvex)
    hij a xi yi aj bj hp hq hsum

end OptionBDKTwoCoordMidpoint
end CertificateChecklist
end WakkerRoadmap

/-! ## R3.2b cross-coordinate midpoint audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKTwoCoordMidpoint.twoCoord_midpoint_ge_of_quasiconcave
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKTwoCoordMidpoint.twoCoord_sum_midpointDeficit_nonneg
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKTwoCoordMidpoint.twoCoord_midpoint_ge_of_convexPref
