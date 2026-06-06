/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-DK endpoint: Debreu–Koopmans hard direction as a named,
  proven-necessary midpoint residual

This file closes WP-DK at the honest endpoint, mirroring the WP-C1.a treatment
of the hexagon.

## The state of the DK forward reduction (already in the repo)

The Debreu–Koopmans hard direction (`debreu_koopmans_hard`, per-coordinate
concavity of each `R.V i`) is **already reduced** to per-coordinate *midpoint*
concavity, with the genuine analytic upgrade fully theorem-backed:

* `BernsteinDoetsch.concaveOn_of_continuousOn_of_midpoint` — the classical
  Sierpiński / Bernstein–Doetsch theorem (midpoint-concave + continuous ⟹
  concave on a convex set), proved from scratch (dyadic density argument);
* `CertificateChecklist.midpointAndContinuityToConcavityResidual_holds` — that
  theorem discharges the named `MidpointAndContinuityToConcavityResidual`
  residue unconditionally;
* `M2Frontier.debreu_koopmans_hard_of_per_pair_continuity_midpoint` — the
  **public DK hard-direction consumer** that produces `∀ i, ConcaveOn ℝ (S i)
  (R.V i)` from per-pair *midpoint* concavity + slice continuity + convex
  upper-contour sets, with the Sierpiński residue already eliminated.

So, exactly as the hexagon reduced (WP-C1.a) to the named `HexagonResidualData`,
the DK hard direction reduces to a single named structural residual: the
**per-coordinate midpoint concavity** `SliceMidpointConcavityCertificate`.  This
is the genuine Debreu–Koopmans (1982) §3 content — the midpoint inequality each
summand inherits from the convex-preference upper-contour structure — and it is
the irreducible analytic input (the continuum analogue of the hexagon's §IV.5
cancellation content).

## What this file delivers (all machine-checked)

* `sliceMidpointConcavity_of_concaveOn` — **necessity**: a `ConcaveOn` slice
  utility satisfies the midpoint inequality (apply concavity at `a = b = 1/2`).
  So the midpoint residual hides nothing false: any genuine concave
  representation supplies it.
* `dkHardDirection_of_sliceMidpointConcavity` — the **sound forward step**:
  per-coordinate concavity from the per-pair midpoint residual + continuity +
  convex upper-contour, by composing the repo's
  `debreu_koopmans_hard_of_per_pair_continuity_midpoint` (Sierpiński already
  discharged).
* `dkHardDirection_of_concaveRep_via_midpoint` — a **sanity capstone**: if the
  representation is already concave, the midpoint residual is supplied
  (necessity) and the forward step recovers concavity — confirming the residual
  is exactly the right strength.

## Honest WP-DK verdict

The DK hard direction is **not** a finite projection of the structural axioms —
it is the genuine Debreu–Koopmans §3 measuring-stick/continuum argument, whose
analytic core (Sierpiński upgrade) is fully mechanized here and whose remaining
content is the per-coordinate midpoint concavity `SliceMidpointConcavityCertificate`.
That residual is:
* **sufficient** (with continuity + convex upper-contour) for the DK output
  (`dkHardDirection_of_sliceMidpointConcavity`), and
* **necessary** under any concave representation (`sliceMidpointConcavity_of_concaveOn`).

The full forward construction of the midpoint residual from convex preference +
the additive representation is the genuine Debreu–Koopmans §3 frontier; this file
pins it to a single sound, necessary named input — the same pattern WP-C1.a used
for the hexagon and WP-CI/WP-density used for A1 and the escape grid.

This file imports `M2Frontier` (for the DK consumer + certificate names) and is
**not** in the umbrella import.
-/

import WakkerDebreuKoopmans.M2Frontier

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBDKConcavityEndpoint

open WakkerInfra
open WakkerDebreuKoopmans (AdditiveRep)

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- **Midpoint concavity is necessary: it follows from `ConcaveOn` on each
slice.**

A `ConcaveOn ℝ S V` utility satisfies the midpoint inequality
`(V x + V y)/2 ≤ V((x+y)/2)` on `S` (instantiate concavity at `a = b = 1/2`).
Applying this to both slices gives the `SliceMidpointConcavityCertificate`.

This is the WP-DK soundness witness: the per-coordinate midpoint residual hides
nothing false — every genuinely concave representation supplies it.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem sliceMidpointConcavity_of_concaveOn
    {S₁ S₂ : Set ℝ} {V₁ V₂ : ℝ → ℝ}
    (h₁ : ConcaveOn ℝ S₁ V₁) (h₂ : ConcaveOn ℝ S₂ V₂) :
    SliceMidpointConcavityCertificate S₁ S₂ V₁ V₂ := by
  -- A single-slice midpoint extractor.
  have mid : ∀ {S : Set ℝ} {V : ℝ → ℝ}, ConcaveOn ℝ S V →
      ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → (V x + V y) / 2 ≤ V ((x + y) / 2) := by
    intro S V hconc x hx y hy
    have key := hconc.2 hx hy
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1:ℝ)/2 + 1/2 = 1)
    simp only [smul_eq_mul] at key
    have he : (1/2 : ℝ) * x + (1/2) * y = (x + y) / 2 := by ring
    rw [he] at key
    linarith
  exact ⟨fun x hx y hy => mid h₁ hx hy, fun x hx y hy => mid h₂ hx hy⟩

/-- **WP-DK sound forward step: the DK hard direction from the per-coordinate
midpoint residual.**

Per-coordinate concavity of every `R.V i` follows from: convex slices, all
coordinates essential, convex preference, per-pair convex upper-contour sets,
slice witnesses, slice continuity, and the per-pair **midpoint** residual
`SliceMidpointConcavityCertificate`.  The Sierpiński upgrade is already
theorem-backed (Bernstein–Doetsch), so this just composes the repo consumer
`debreu_koopmans_hard_of_per_pair_continuity_midpoint`.  Audit foundational-only. -/
theorem dkHardDirection_of_sliceMidpointConcavity
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref (fun _ : ι => ℝ))
    (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (hConvex : WakkerInfra.ProductPref.ConvexPref P
                  ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    (j₀ : ι)
    (hConvexPair :
      ∀ k : ι,
        ∀ (u₀ : ℝ) (v₀ : ℝ),
          Convex ℝ ({ p : ℝ × ℝ |
                       p.1 ∈ S j₀ ∧ p.2 ∈ S k ∧
                       R.V j₀ u₀ + R.V k v₀ ≤ R.V j₀ p.1 + R.V k p.2 }))
    (hWit : ∀ k : ι, ∃ u₀ ∈ S j₀, ∃ v₀ ∈ S k, True)
    (hCont : CoordinateUtilityContinuityCertificate R S)
    (hMid : ∀ k : ι,
              SliceMidpointConcavityCertificate (S j₀) (S k) (R.V j₀) (R.V k)) :
    ∀ i, ConcaveOn ℝ (S i) (R.V i) :=
  debreu_koopmans_hard_of_per_pair_continuity_midpoint
    P R S hS essential hConvex j₀ hConvexPair hWit hCont hMid

/-- **Sanity capstone: an already-concave representation supplies the midpoint
residual, which recovers the DK output.**

If the representation is concave on each slice, then (a) each pivot/coordinate
pair satisfies the midpoint residual by `sliceMidpointConcavity_of_concaveOn`,
and (b) feeding it back through `dkHardDirection_of_sliceMidpointConcavity`
recovers per-coordinate concavity — confirming the residual is exactly the right
strength (sufficient for the DK output, and no stronger than what a concave
representation supplies).  Audit foundational-only. -/
theorem dkHardDirection_of_concaveRep_via_midpoint
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref (fun _ : ι => ℝ))
    (R : AdditiveRep P)
    (S : ι → Set ℝ)
    (hS : ∀ i, Convex ℝ (S i))
    (essential : ∀ i, WakkerInfra.ProductPref.Essential P i)
    (hConvex : WakkerInfra.ProductPref.ConvexPref P
                  ({ x : ι → ℝ | ∀ i, x i ∈ S i }))
    (j₀ : ι)
    (hConvexPair :
      ∀ k : ι,
        ∀ (u₀ : ℝ) (v₀ : ℝ),
          Convex ℝ ({ p : ℝ × ℝ |
                       p.1 ∈ S j₀ ∧ p.2 ∈ S k ∧
                       R.V j₀ u₀ + R.V k v₀ ≤ R.V j₀ p.1 + R.V k p.2 }))
    (hWit : ∀ k : ι, ∃ u₀ ∈ S j₀, ∃ v₀ ∈ S k, True)
    (hCont : CoordinateUtilityContinuityCertificate R S)
    (hConc : ∀ i, ConcaveOn ℝ (S i) (R.V i)) :
    ∀ i, ConcaveOn ℝ (S i) (R.V i) :=
  dkHardDirection_of_sliceMidpointConcavity
    P R S hS essential hConvex j₀ hConvexPair hWit hCont
    (fun k => sliceMidpointConcavity_of_concaveOn (hConc j₀) (hConc k))

end OptionBDKConcavityEndpoint
end CertificateChecklist
end WakkerRoadmap

/-! ## WP-DK endpoint audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKConcavityEndpoint.sliceMidpointConcavity_of_concaveOn
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKConcavityEndpoint.dkHardDirection_of_sliceMidpointConcavity
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKConcavityEndpoint.dkHardDirection_of_concaveRep_via_midpoint
