/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — Residual 3 (DK §3) soundness gate: quasiconcavity does NOT give
  midpoint concavity

Executing R3.2 of `OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`
triggers the mandatory soundness/derivability gate (the discipline the §5 gate,
WP-CI, WP-density, the two WP-C1.a probes, and the residual-2 escape-grid gate all
vindicated).  Before attempting to prove `SliceMidpointConcavityCertificate` from
the convex-preference inputs, we test whether the piece **already in hand** — R3.1
per-slice *quasi*concavity (`two_coord_quasiconcave_left/right`, theorem-backed
from convex upper-contour sets) — is by itself enough.

## The probe verdict: NO — quasiconcavity ⇏ midpoint concavity.

Mathlib's `quasiconcaveOn_iff_min_le` shows quasiconcavity only gives
`min (f x) (f y) ≤ f (midpoint)`, strictly weaker than the midpoint-concavity
inequality `(f x + f y)/2 ≤ f (midpoint)`.  A concrete witness: `Real.exp` is

* **quasiconcave** on `univ` (it is monotone, `Monotone.quasiconcaveOn`), yet
* **not midpoint-concave** — it is strictly convex (`strictConvexOn_exp`), so at
  `x = 0, y = 1` we have `(exp 0 + exp 1)/2 > exp (1/2)`.

`exp_quasiconcave_not_midpointConcave` packages both facts.  Hence R3.2 is **not**
a consequence of R3.1: the genuine Debreu–Koopmans §3 content (the additive `n ≥ 3`
cross-coordinate alignment turning convex *preference* into per-summand midpoint
concavity) is required.  The midpoint target is therefore a genuine named residual,
proved *necessary* (under a concave representation) in
`OptionB_DKConcavityEndpoint.sliceMidpointConcavity_of_concaveOn` — sound, but not
free from quasiconcavity alone.

This file imports only Mathlib convex-analysis and is **not** in the umbrella
import.
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
set_option linter.unusedVariables false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBDKMidpointProbe

open Real Set

/-- The midpoint-concavity inequality for a function `f` on a set `S` (the
content of one slice of `SliceMidpointConcavityCertificate`). -/
def MidpointConcaveOn (S : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → (f x + f y) / 2 ≤ f ((x + y) / 2)

/-- `Real.exp` is quasiconcave on `univ` (it is monotone). -/
theorem exp_quasiconcave : QuasiconcaveOn ℝ univ Real.exp :=
  Real.exp_monotone.quasiconcaveOn

/-- `Real.exp` is **not** midpoint-concave on `univ`: at `x = 0, y = 1`,
strict convexity forces `(exp 0 + exp 1)/2 > exp (1/2)`. -/
theorem exp_not_midpointConcave : ¬ MidpointConcaveOn univ Real.exp := by
  intro h
  -- Midpoint concavity at 0, 1 would give (exp 0 + exp 1)/2 ≤ exp (1/2).
  have hmid := h (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
  -- Strict convexity gives the strict reverse at the distinct points 0 ≠ 1.
  have hconv := strictConvexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) ≠ 1)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  -- hconv : exp ((1/2)•0 + (1/2)•1) < (1/2)•exp 0 + (1/2)•exp 1
  simp only [smul_eq_mul] at hconv
  -- Rewrite both sides to match hmid's (·+·)/2 form.
  have hpt : (1/2 : ℝ) * 0 + (1/2) * 1 = (0 + 1) / 2 := by norm_num
  rw [hpt] at hconv
  have hrhs : (1/2 : ℝ) * Real.exp 0 + (1/2) * Real.exp 1
      = (Real.exp 0 + Real.exp 1) / 2 := by ring
  rw [hrhs] at hconv
  linarith

/-- **DK §3 soundness-gate verdict (packaged).**

There is a function that is quasiconcave on `univ` but not midpoint-concave.
Hence R3.1 (per-slice quasiconcavity, theorem-backed from convex upper-contour
sets) does **not** imply R3.2's `SliceMidpointConcavityCertificate`: the midpoint
inequality is genuine Debreu–Koopmans §3 content (the additive `n ≥ 3` alignment),
not a free consequence of quasiconcavity.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem quasiconcave_does_not_imply_midpointConcave :
    ∃ f : ℝ → ℝ, QuasiconcaveOn ℝ univ f ∧ ¬ MidpointConcaveOn univ f :=
  ⟨Real.exp, exp_quasiconcave, exp_not_midpointConcave⟩

end OptionBDKMidpointProbe
end CertificateChecklist
end WakkerRoadmap

/-! ## DK §3 midpoint-probe audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKMidpointProbe.exp_quasiconcave
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKMidpointProbe.exp_not_midpointConcave
#print axioms WakkerRoadmap.CertificateChecklist.OptionBDKMidpointProbe.quasiconcave_does_not_imply_midpointConcave
