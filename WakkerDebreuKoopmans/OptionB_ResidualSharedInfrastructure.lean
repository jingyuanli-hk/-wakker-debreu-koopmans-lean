/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — shared infrastructure for the three residual forward constructions

This file executes the **cross-cutting infrastructure** items X1 and X3 of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`.  They are the
cheap, shared prerequisites for the §IV.5 cross-pair construction (residual 1)
and the §IV.2.6 escape-grid refinement family (residual 2).

## X1 — Solvability-driven slice-indifference selector

`RestrictedSolvability` already *is* the "between ⟹ equal" statement, but the two
forward constructions consume it in the `coordPref`-oriented form: from a
single-coordinate bracket around a target, produce the indifferent slice value.
`sliceIndiffSelector_of_restrictedSolvability` states it once, in both the
forward and the symmetric (reversed-bracket) orientation, with the `coordPref`
phrasing the constructions use.

## X3 — `n ≥ 3` third essential coordinate selector

The measuring-stick argument (residual 1) needs a third coordinate `t ∉ {j,k}`.
`exists_third_coordinate` provides it from `3 ≤ Fintype.card ι`, and
`exists_third_essential_coordinate` additionally certifies it essential (from the
capstone's `∀ i, Essential P i`).

Both items are sound by construction (X1 is the solvability axiom re-expressed; X3
is finite combinatorics) and audit `[propext, Classical.choice, Quot.sound]`.

This file imports `WakkerDebreuKoopmans.Core` and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.Core

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open Function Finset

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-! ## X1 — Solvability-driven slice-indifference selector -/

/-- **X1 (forward orientation).**  From a single-coordinate bracket around a
target `b` — `(a with j ↦ v) ≽ b ≽ (a with j ↦ w)` — restricted solvability
produces a slice value `c` with `(a with j ↦ c) ∼ b`.

This is `RestrictedSolvability` re-exported with explicit naming for the forward
constructions (residuals 1 and 2).  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem sliceIndiffSelector_of_restrictedSolvability
    (hsolv : RestrictedSolvability P)
    (a b : Profile X) (j : ι) (v w : X j)
    (hvb : P.weakPref (Function.update a j v) b)
    (hbw : P.weakPref b (Function.update a j w)) :
    ∃ c : X j, P.indiff (Function.update a j c) b :=
  hsolv a b j v w hvb hbw

/-- **X1 (symmetric orientation).**  The reversed bracket
`b ≽ (a with j ↦ v)` and `(a with j ↦ w) ≽ b` also yields an indifferent slice
value.  Thin wrapper over `restrictedSolvability_symm`. -/
theorem sliceIndiffSelector_symm_of_restrictedSolvability
    [ProductPref.IsWeakOrder P]
    (hsolv : RestrictedSolvability P)
    (a b : Profile X) (j : ι) (v w : X j)
    (hvb : P.weakPref b (Function.update a j v))
    (hbw : P.weakPref (Function.update a j w) b) :
    ∃ c : X j, P.indiff (Function.update a j c) b :=
  restrictedSolvability_symm P hsolv a b j v w hvb hbw

/-- **X1 (coordPref phrasing).**  Restated through `coordPref`: a bracket
`coordPref j a v (b j-slot)`-style pair around the target's `j`-value yields the
indifferent value.  Here the bracket is given directly on the updated profiles
(the form `archimedean_slice_crossing` and the interpolation certificates emit).
Identical content to the forward selector; provided so call sites need not unfold
`coordPref`. -/
theorem sliceIndiffSelector_coordPref_of_restrictedSolvability
    (hsolv : RestrictedSolvability P)
    (a b : Profile X) (j : ι) (v w : X j)
    (hvb : P.weakPref (Function.update a j v) b)
    (hbw : P.weakPref b (Function.update a j w)) :
    ∃ c : X j, P.indiff (Function.update a j c) b :=
  sliceIndiffSelector_of_restrictedSolvability hsolv a b j v w hvb hbw

/-! ## X3 — third (essential) coordinate selector -/

/-- **X3 (bare).**  With at least three coordinates, for any two `j, k` there is a
third coordinate `t` distinct from both.  Pure finite combinatorics from
`3 ≤ Fintype.card ι`.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem exists_third_coordinate [_hcard : Fact (3 ≤ Fintype.card ι)]
    (j k : ι) : ∃ t : ι, t ≠ j ∧ t ≠ k := by
  classical
  -- The set {j, k} has at most 2 elements; univ has ≥ 3, so the complement is nonempty.
  by_contra h
  push_neg at h
  -- h : ∀ t, t ≠ j → t = k
  have hsub : (Finset.univ : Finset ι) ⊆ {j, k} := by
    intro t _
    by_cases htj : t = j
    · subst htj; exact Finset.mem_insert_self _ _
    · have : t = k := h t htj
      subst this
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hpair_le : ({j, k} : Finset ι).card ≤ 2 := by
    calc ({j, k} : Finset ι).card ≤ ({k} : Finset ι).card + 1 :=
          Finset.card_insert_le j {k}
      _ = 2 := by simp
  have hcard_le : Fintype.card ι ≤ 2 := by
    calc Fintype.card ι = (Finset.univ : Finset ι).card := (Finset.card_univ).symm
      _ ≤ ({j, k} : Finset ι).card := Finset.card_le_card hsub
      _ ≤ 2 := hpair_le
  have h3 : 3 ≤ Fintype.card ι := _hcard.out
  omega

/-- **X3 (essential).**  With `3 ≤ card ι` and every coordinate essential, for any
`j, k` there is a third coordinate `t ∉ {j,k}` that is essential.  This is the
measuring-stick coordinate residual 1 needs.  Audit foundational-only. -/
theorem exists_third_essential_coordinate
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (hess : ∀ i, ProductPref.Essential P i) (j k : ι) :
    ∃ t : ι, t ≠ j ∧ t ≠ k ∧ ProductPref.Essential P t := by
  obtain ⟨t, htj, htk⟩ := exists_third_coordinate (ι := ι) j k
  exact ⟨t, htj, htk, hess t⟩

end ProductPref
end WakkerInfra

/-! ## X1 + X3 shared-infrastructure audit -/

#print axioms WakkerInfra.ProductPref.sliceIndiffSelector_of_restrictedSolvability
#print axioms WakkerInfra.ProductPref.sliceIndiffSelector_symm_of_restrictedSolvability
#print axioms WakkerInfra.ProductPref.sliceIndiffSelector_coordPref_of_restrictedSolvability
#print axioms WakkerInfra.ProductPref.exists_third_coordinate
#print axioms WakkerInfra.ProductPref.exists_third_essential_coordinate
