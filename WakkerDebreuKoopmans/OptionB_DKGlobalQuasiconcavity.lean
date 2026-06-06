/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — Residual 3 (DK §3), step R3.2a: global quasiconcavity of the
  additive sum from convex preference

This file executes the first sound forward sub-step of **R3.2** of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`, after the
derivability gate (`OptionB_DKMidpointProbe.lean`) established that *per-slice*
quasiconcavity (R3.1) is insufficient for the midpoint target.

## The right entry point: the GLOBAL additive sum

The Debreu–Koopmans §3 argument does not start from per-slice quasiconcavity; it
starts from the **global** convex-preference structure.  `ConvexPref P D` says the
upper-contour set `{x ∈ D | x ≽ y}` of every profile `y` is convex.  Under an
additive representation `R` (`R.represents : x ≽ y ↔ ∑V(y) ≤ ∑V(x)`), that
upper-contour set is **exactly** the super-level set
`{x ∈ D | ∑V(y) ≤ ∑V(x)}` of the additive sum `Φ x := ∑ i, R.V i (x i)`.  Since
super-level sets characterize quasiconcavity (`QuasiconcaveOn` = all super-level
sets convex), convex preference is *equivalent* to **global quasiconcavity of the
additive sum** on `D`.

## What this file delivers (machine-checked, sound)

* `additiveSum` — the additive sum `Φ x = ∑ i, R.V i (x i)`.
* `additiveSum_quasiconcaveOn_of_convexPref` — **the forward sub-step**: from
  `ConvexPref P D` and a representation `R`, the additive sum is
  `QuasiconcaveOn ℝ D`.  This is the genuine DK §3 entry point (it uses the global
  convex-preference structure, not per-slice content), and is sound and fully
  provable now.
* `convexPref_of_additiveSum_quasiconcaveOn` — the **converse** (sound check): if
  the additive sum is quasiconcave on a convex `D`, then `ConvexPref P D` holds.
  Together these show convex preference ⇔ global quasiconcavity of the sum.

## Where this leaves R3.2

The remaining genuine gap (R3.2b) is the strictly-harder upgrade from *global*
quasiconcavity of the **sum** to *midpoint concavity of each summand* `R.V i` —
the additive `n ≥ 3` separation argument (Debreu–Koopmans §3 proper).  The probe
already showed quasiconcavity ⇏ midpoint concavity even for a single function, so
R3.2b genuinely needs the additive cross-coordinate structure; it is the named
residual, proved *necessary* in
`OptionB_DKConcavityEndpoint.sliceMidpointConcavity_of_concaveOn`.  This file
supplies the sound first half (R3.2a) and isolates R3.2b precisely.

This file imports `WakkerDebreuKoopmans.Core` and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.Core
import Mathlib.Analysis.Convex.Quasiconvex

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBDKGlobalQuasiconcavity

open WakkerInfra
open WakkerDebreuKoopmans (AdditiveRep)

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The additive sum `Φ x = ∑ i, R.V i (x i)` of a representation. -/
def additiveSum {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    (x : ι → ℝ) : ℝ :=
  ∑ i, R.V i (x i)

/-- **R3.2a — global quasiconcavity of the additive sum from convex preference.**

From `ConvexPref P D` (convex upper-contour sets) and an additive representation
`R`, the additive sum `additiveSum R` is `QuasiconcaveOn ℝ D`.

Proof: a super-level set `{x ∈ D | r ≤ Φ x}` equals the convex upper-contour set
`{x ∈ D | x ≽ y}` for any `y` with `∑V(y) = r` — but to avoid choosing such a `y`,
we use that quasiconcavity is equivalent to convexity of every super-level set,
and each super-level set of `Φ` at level `r` is `{x ∈ D | ∑V(y₀) ≤ Φ x}` for the
contour structure.  Concretely we show convexity of `{x ∈ D | r ≤ Φ x}` directly
from convexity of the upper-contour sets via `R.represents`, picking the contour
threshold by `r`.  We instead route through the equivalent characterization: the
upper-contour set of `y` is the super-level set at `Φ y`, and convexity of
super-level sets at *every* attained level plus the order structure gives
quasiconcavity.

Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem additiveSum_quasiconcaveOn_of_convexPref
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {D : Set (ι → ℝ)} (hConvex : WakkerInfra.ProductPref.ConvexPref P D) :
    QuasiconcaveOn ℝ D (additiveSum R) := by
  -- `QuasiconcaveOn` unfolds to: ∀ r, Convex ℝ {x ∈ D | r ≤ Φ x}.
  intro r
  -- The upper-contour set of any profile `y` is convex (ConvexPref).
  -- We show {x ∈ D | r ≤ Φ x} is convex by the min-le segment criterion.
  rw [Convex]
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxD, hxr⟩
  rcases hy with ⟨hyD, hyr⟩
  -- WLOG the smaller-Φ endpoint is the contour reference; both endpoints lie in
  -- its upper-contour set, which is convex by ConvexPref.
  -- Choose ref ∈ {x, y} minimizing Φ.
  obtain ⟨ref, hrefD, href_le_x, href_le_y, hr_le_ref⟩ :
      ∃ ref : ι → ℝ, ref ∈ D ∧
        additiveSum R ref ≤ additiveSum R x ∧
        additiveSum R ref ≤ additiveSum R y ∧
        r ≤ additiveSum R ref := by
    rcases le_total (additiveSum R x) (additiveSum R y) with h | h
    · exact ⟨x, hxD, le_refl _, h, hxr⟩
    · exact ⟨y, hyD, h, le_refl _, hyr⟩
  -- Both x and y are in the upper-contour set of `ref`: x ≽ ref and y ≽ ref.
  have hx_pref : P.weakPref x ref :=
    (R.represents x ref).mpr href_le_x
  have hy_pref : P.weakPref y ref :=
    (R.represents y ref).mpr href_le_y
  have hxmem : x ∈ { z ∈ D | P.weakPref z ref } := ⟨hxD, hx_pref⟩
  have hymem : y ∈ { z ∈ D | P.weakPref z ref } := ⟨hyD, hy_pref⟩
  -- The upper-contour set of `ref` is convex.
  have hconv := (hConvex.2 ref) hxmem hymem ha hb hab
  rcases hconv with ⟨hmemD, hmem_pref⟩
  refine ⟨hmemD, ?_⟩
  -- a•x + b•y ≽ ref  ⟹  Φ ref ≤ Φ (a•x+b•y);  and r ≤ Φ ref.
  have : additiveSum R ref ≤ additiveSum R (a • x + b • y) :=
    (R.represents (a • x + b • y) ref).mp hmem_pref
  exact le_trans hr_le_ref this

/-- **Converse (soundness check): convex preference from global quasiconcavity of
the additive sum.**

If the additive sum `additiveSum R` is `QuasiconcaveOn ℝ D` and `D` is convex,
then `ConvexPref P D` holds: each upper-contour set is the super-level set of the
sum, hence convex.  Together with `additiveSum_quasiconcaveOn_of_convexPref` this
shows the two are equivalent.  Audit foundational-only. -/
theorem convexPref_of_additiveSum_quasiconcaveOn
    {P : ProductPref (fun _ : ι => ℝ)} (R : AdditiveRep P)
    {D : Set (ι → ℝ)} (hD : Convex ℝ D)
    (hQ : QuasiconcaveOn ℝ D (additiveSum R)) :
    WakkerInfra.ProductPref.ConvexPref P D := by
  refine ⟨hD, ?_⟩
  intro y
  -- {x ∈ D | x ≽ y} = {x ∈ D | Φ y ≤ Φ x}, the super-level set at level Φ y.
  have h_eq :
      { x ∈ D | P.weakPref x y }
        = { x ∈ D | additiveSum R y ≤ additiveSum R x } := by
    ext x
    constructor
    · rintro ⟨hxD, hxy⟩
      exact ⟨hxD, (R.represents x y).mp hxy⟩
    · rintro ⟨hxD, hxy⟩
      exact ⟨hxD, (R.represents x y).mpr hxy⟩
  rw [h_eq]
  exact hQ (additiveSum R y)

end OptionBDKGlobalQuasiconcavity
end CertificateChecklist
end WakkerRoadmap

/-! ## R3.2a global-quasiconcavity audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKGlobalQuasiconcavity.additiveSum_quasiconcaveOn_of_convexPref
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKGlobalQuasiconcavity.convexPref_of_additiveSum_quasiconcaveOn
