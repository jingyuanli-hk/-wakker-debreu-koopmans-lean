/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — Residual 2: escape-grid refinement family (§IV.2.6), step R2.1

This file executes item **R2.1 (midpoint refinement step)** of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`: the genuine
bisection engine underneath the §IV.2.6 escape-grid refinement family.

## What R2.1 needs

A single one-sided strict standard sequence is an arithmetic progression, hence
not dense (repo no-go `additiveRealBool_strictStandardSequence_not_dense`).
Density requires *refining* each grid gap.  The atomic refinement is: **given a
strict bracket `(a with j ↦ v) ≻ b ≻ (a with j ↦ w)` produce an interior slice
value `c` strictly between `v` and `w` in the coordinate order, indifferent to the
intermediate target `b`.**

## What this file delivers (machine-checked, sound)

* `coordStrictMid_of_restrictedSolvability` — from a strict bracket around a
  target `b`, restricted solvability yields `c` with `(a with j ↦ c) ∼ b` lying
  **strictly between** the bracket endpoints in the coordinate order:
  `(a with j ↦ v) ≻ (a with j ↦ c) ≻ (a with j ↦ w)`.  This is the sound
  bisection step: it produces a genuine new interior grid value.
* `coordStrictBetween_of_restrictedSolvability` — the `coordPref`-phrased
  corollary: the new value `c` strictly refines the gap `(v, w)`.

These are sound (necessity: under a representation, the interior point is the
solvability preimage of `b`'s score, strictly between `V v` and `V w`).  The
remaining R2.2/R2.3 content — iterating the bisection to rational-image coverage
and packaging as `SelectedRefinedGridBetweenPointsCertificate` — is the genuine
§IV.2.6 induction, scaffolded on this engine.

This file imports the shared infrastructure (X1) and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_ResidualSharedInfrastructure

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open Function

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-- **R2.1 midpoint/bisection step.**

Given a **strict** bracket around an intermediate target `b`:
`(a with j ↦ v) ≻ b` and `b ≻ (a with j ↦ w)`, restricted solvability produces a
slice value `c` with `(a with j ↦ c) ∼ b` that is **strictly between** the
endpoints in the coordinate order:
`(a with j ↦ v) ≻ (a with j ↦ c)` and `(a with j ↦ c) ≻ (a with j ↦ w)`.

This is the sound atomic refinement: it manufactures a genuinely new interior
grid value `c` strictly inside the gap `(v, w)`.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem coordStrictMid_of_restrictedSolvability
    [ProductPref.IsWeakOrder P]
    (hsolv : RestrictedSolvability P)
    (a b : Profile X) (j : ι) (v w : X j)
    (hvb : P.strict (Function.update a j v) b)
    (hbw : P.strict b (Function.update a j w)) :
    ∃ c : X j,
      P.indiff (Function.update a j c) b ∧
      P.strict (Function.update a j v) (Function.update a j c) ∧
      P.strict (Function.update a j c) (Function.update a j w) := by
  -- Solvability needs only the weak bracket.
  obtain ⟨c, hc⟩ := hsolv a b j v w hvb.1 hbw.1
  refine ⟨c, hc, ?_, ?_⟩
  · -- (a↦v) ≻ (a↦c):  weak from hvb.1 ∘ hc.2; strict since ¬ (a↦c) ≽ (a↦v).
    refine ⟨ProductPref.IsWeakOrder.transitive _ _ _ hvb.1 hc.2, ?_⟩
    intro hcontra
    -- hcontra : (a↦c) ≽ (a↦v).  b ≽ c ≽ v gives b ≽ (a↦v), contradicting hvb strictness.
    exact hvb.2 (ProductPref.IsWeakOrder.transitive _ _ _ hc.2 hcontra)
  · -- (a↦c) ≻ (a↦w):  weak from hc.1 ∘ hbw.1; strict since ¬ (a↦w) ≽ (a↦c).
    refine ⟨ProductPref.IsWeakOrder.transitive _ _ _ hc.1 hbw.1, ?_⟩
    intro hcontra
    -- hcontra : (a↦w) ≽ (a↦c).  w ≽ c ≽ b gives (a↦w) ≽ b, contradicting hbw strictness.
    exact hbw.2 (ProductPref.IsWeakOrder.transitive _ _ _ hcontra hc.1)

/-- **R2.1 corollary (coordPref phrasing).**  The refined value `c` strictly
splits the gap `(v, w)` in the coordinate order: `v ≻_j c` and `c ≻_j w` (strict
coordinate preference both sides).  Audit foundational-only. -/
theorem coordStrictBetween_of_restrictedSolvability
    [ProductPref.IsWeakOrder P]
    (hsolv : RestrictedSolvability P)
    (a b : Profile X) (j : ι) (v w : X j)
    (hvb : P.strict (Function.update a j v) b)
    (hbw : P.strict b (Function.update a j w)) :
    ∃ c : X j,
      (P.coordPref j a v c ∧ ¬ P.coordPref j a c v) ∧
      (P.coordPref j a c w ∧ ¬ P.coordPref j a w c) := by
  obtain ⟨c, _hindiff, hvc, hcw⟩ :=
    coordStrictMid_of_restrictedSolvability hsolv a b j v w hvb hbw
  exact ⟨c, ⟨hvc.1, hvc.2⟩, ⟨hcw.1, hcw.2⟩⟩

end ProductPref
end WakkerInfra

/-! ## R2.1 escape-grid refinement-step audit -/

#print axioms WakkerInfra.ProductPref.coordStrictMid_of_restrictedSolvability
#print axioms WakkerInfra.ProductPref.coordStrictBetween_of_restrictedSolvability
