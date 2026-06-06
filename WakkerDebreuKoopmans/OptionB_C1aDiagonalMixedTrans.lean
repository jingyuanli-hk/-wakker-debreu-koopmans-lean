/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: mixed-class transitivity of the diagonal trichotomy

This file proves another real, structural theorem about the single Thomsen
residue `TBlockDiagonalResidue` (R1.1's final-piece content,
`OptionB_C1aDiagonalUnifiedCapstone.lean`):

**Mixed-class transitivity** — chaining a uniform strict relation with a
uniform indifference (in either order) produces a uniform strict relation;
chaining a uniform `≽` with a uniform `∼` (in either order) produces a uniform
`≽`.  This is the standard preorder-with-equivalence calculus on the trade-off
space.

`OptionB_C1aDiagonalTransitivity.lean` proved same-class transitivity
(`≻ ∘ ≻`, `∼ ∘ ∼`, `≽ ∘ ≽`).  The setoid file proved indifference is reflexive,
symmetric, and transitive.  This file fills the *cross-class* corner: how
strict and indifference compose.  Together with the prior facts, this completes
the standard total-preorder-modulo-equivalence calculus on the trichotomy
classes — exactly the Wakker §IV.2.5 trade-off-consistency vocabulary.

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_trans_strict_indiff` — `≻ ∘ ∼ → ≻`: a uniform strict
  followed by a uniform indifference is a uniform strict.
* `tBlockDiagonalResidue_trans_indiff_strict` — `∼ ∘ ≻ → ≻`: a uniform
  indifference followed by a uniform strict is a uniform strict.
* `tBlockDiagonalResidue_trans_weakPref_indiff` — `≽ ∘ ∼ → ≽`: a uniform `≽`
  followed by a uniform indifference is a uniform `≽`.
* `tBlockDiagonalResidue_trans_indiff_weakPref` — `∼ ∘ ≽ → ≽`: a uniform
  indifference followed by a uniform `≽` is a uniform `≽`.

These are pure `IsWeakOrder` consequences at each level (no T-diag content
beyond the framework that quantifies "uniform across levels"); the substantive
sample-stability is in the prior diagonal-strict and -indiff theorems.  Audit
`[propext, Quot.sound]`.

This file imports `OptionB_C1aDiagonalTransitivity` and is **not** in the
umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalTransitivity

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open WakkerDebreuKoopmans
open Function

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-- **Mixed-class transitivity: `≻` then `∼` chains to `≻`.**

If `(x,r,c) ≻ (z,p,c)` for all `c` (uniform strict) and
`(z,p,c) ∼ (y,q,c)` for all `c` (uniform indifference), then
`(x,r,c) ≻ (y,q,c)` for all `c`.  Per-level: a strict-then-indiff chain forces
strict by the standard preorder calculus.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_trans_strict_indiff
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z y : X j) (p q r : X k)
    (h₁ : ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c))
    (h₂ : ∀ c : X t, P.indiff (tri a j k t z p c) (tri a j k t y q c)) :
    ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t y q c) := by
  intro c
  rcases h₁ c with ⟨h1fwd, h1nbwd⟩
  rcases h₂ c with ⟨h2fwd, h2bwd⟩
  refine ⟨?_, ?_⟩
  · -- `≽` direction: chain the forward `≽`s.
    exact ProductPref.IsWeakOrder.transitive _ _ _ h1fwd h2fwd
  · -- Reverse `≽` would imply `(z,p) ≽ (x,r)` via the indiff's reverse leg,
    -- contradicting strictness's negation of the reverse.
    intro hbwd
    -- hbwd : weakPref (tri y q c) (tri x r c).
    -- h2bwd : weakPref (tri y q c) (tri z p c) — wait, that's backwards.
    -- Indiff is symmetric in its two legs; h2bwd : weakPref (tri y q c) (tri z p c).
    -- We need: weakPref (tri z p c) (tri x r c) to contradict h1nbwd.
    -- Chain: (z,p) ≽ (y,q) by h2bwd's reverse direction... actually h2bwd IS
    -- weakPref (tri y q c) (tri z p c).  So (z,p) ≽ (y,q) is h2.1 = h2fwd? No,
    -- h2 is indiff (z,p) (y,q), so h2fwd : (z,p) ≽ (y,q) and h2bwd : (y,q) ≽ (z,p).
    -- We have hbwd : (y,q) ≽ (x,r) and h2fwd : (z,p) ≽ (y,q).
    -- Chain: (z,p) ≽ (y,q) ≽ (x,r), giving (z,p) ≽ (x,r), contradicting h1nbwd.
    have : P.weakPref (tri a j k t z p c) (tri a j k t x r c) :=
      ProductPref.IsWeakOrder.transitive _ _ _ h2fwd hbwd
    exact h1nbwd this

/-- **Mixed-class transitivity: `∼` then `≻` chains to `≻`.**

If `(x,r,c) ∼ (z,p,c)` for all `c` and `(z,p,c) ≻ (y,q,c)` for all `c`, then
`(x,r,c) ≻ (y,q,c)` for all `c`.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_trans_indiff_strict
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z y : X j) (p q r : X k)
    (h₁ : ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c))
    (h₂ : ∀ c : X t, P.strict (tri a j k t z p c) (tri a j k t y q c)) :
    ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t y q c) := by
  intro c
  rcases h₁ c with ⟨h1fwd, h1bwd⟩
  rcases h₂ c with ⟨h2fwd, h2nbwd⟩
  refine ⟨?_, ?_⟩
  · -- `≽` direction: chain the forward `≽`s.
    exact ProductPref.IsWeakOrder.transitive _ _ _ h1fwd h2fwd
  · -- Reverse `≽` would chain with indiff to give (y,q) ≽ (z,p), contradicting strict.
    intro hbwd
    -- hbwd : weakPref (tri y q c) (tri x r c).
    -- h1fwd : weakPref (tri x r c) (tri z p c).
    -- Chain: (y,q) ≽ (x,r) ≽ (z,p), giving (y,q) ≽ (z,p), contradicting h2nbwd.
    have : P.weakPref (tri a j k t y q c) (tri a j k t z p c) :=
      ProductPref.IsWeakOrder.transitive _ _ _ hbwd h1fwd
    exact h2nbwd this

/-- **Mixed-class transitivity: `≽` then `∼` chains to `≽`.**

If `(x,r,c) ≽ (z,p,c)` for all `c` and `(z,p,c) ∼ (y,q,c)` for all `c`, then
`(x,r,c) ≽ (y,q,c)` for all `c`.  Pure transitivity of `≽` after extracting the
forward leg of the indifference.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_trans_weakPref_indiff
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z y : X j) (p q r : X k)
    (h₁ : ∀ c : X t, P.weakPref (tri a j k t x r c) (tri a j k t z p c))
    (h₂ : ∀ c : X t, P.indiff (tri a j k t z p c) (tri a j k t y q c)) :
    ∀ c : X t, P.weakPref (tri a j k t x r c) (tri a j k t y q c) := by
  intro c
  exact ProductPref.IsWeakOrder.transitive _ _ _ (h₁ c) (h₂ c).1

/-- **Mixed-class transitivity: `∼` then `≽` chains to `≽`.**

If `(x,r,c) ∼ (z,p,c)` for all `c` and `(z,p,c) ≽ (y,q,c)` for all `c`, then
`(x,r,c) ≽ (y,q,c)` for all `c`.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_trans_indiff_weakPref
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z y : X j) (p q r : X k)
    (h₁ : ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c))
    (h₂ : ∀ c : X t, P.weakPref (tri a j k t z p c) (tri a j k t y q c)) :
    ∀ c : X t, P.weakPref (tri a j k t x r c) (tri a j k t y q c) := by
  intro c
  exact ProductPref.IsWeakOrder.transitive _ _ _ (h₁ c).1 (h₂ c)

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-mixed-trans audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_strict_indiff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_indiff_strict
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_weakPref_indiff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_indiff_weakPref
