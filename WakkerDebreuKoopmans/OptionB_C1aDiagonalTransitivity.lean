/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: transitivity of the diagonal trichotomy classes

This file proves another real, useful structural theorem about the single
Thomsen residue `TBlockDiagonalResidue` (R1.1's final-piece content):
**transitivity** of the trichotomy classes (uniform `≻`, uniform `∼`, uniform
`≺`) across two-coord-different profile pairs.

## The content

The trichotomy classification (`OptionB_C1aDiagonalTrichotomy.lean`) shows the
diagonal residue assigns to each two-coord-different profile pair exactly one of
three uniform classes.  This file proves the classes **compose by transitivity**:
chaining two uniform `≻` (or `∼`) gives a uniform `≻` (or `∼`) on the chained
pair.

This formalizes Wakker §IV.2.5's claim that the trade-off relation forms a
genuine total preorder on the trade-off space — not merely a level-by-level
classification, but compositionally consistent.

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_trans_strict` — transitivity of uniform `≻`: if
  `(x,r,·) ≻ (z,p,·)` uniformly and `(z,p,·) ≻ (y,q,·)` uniformly, then
  `(x,r,·) ≻ (y,q,·)` uniformly (modulo distinctness of the chain endpoints).
* `tBlockDiagonalResidue_trans_indiff` — transitivity of uniform `∼`.
* `tBlockDiagonalResidue_trans_weakPref` — uniform `≽` is preserved across
  chains (which subsumes the previous two by case analysis).

These confirm the diagonal residue's classes form a genuine total preorder on
the trade-off space.

This file imports `OptionB_C1aDiagonalTrichotomy` and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalTrichotomy

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

/-- **Transitivity of uniform `≽` under `T-diag`.**

If `(x,r,c) ≽ (z,p,c)` for all `c` and `(z,p,c) ≽ (y,q,c)` for all `c`, then
`(x,r,c) ≽ (y,q,c)` for all `c`.  Direct from `IsWeakOrder.transitive` at each
level.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_trans_weakPref
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z y : X j) (p q r : X k)
    (h₁ : ∀ c : X t, P.weakPref (tri a j k t x r c) (tri a j k t z p c))
    (h₂ : ∀ c : X t, P.weakPref (tri a j k t z p c) (tri a j k t y q c)) :
    ∀ c : X t, P.weakPref (tri a j k t x r c) (tri a j k t y q c) := by
  intro c
  exact ProductPref.IsWeakOrder.transitive _ _ _ (h₁ c) (h₂ c)

/-- **Transitivity of uniform `∼` under `T-diag`.**

Indifference is two-direction `≽`; transitivity follows from
`tBlockDiagonalResidue_trans_weakPref` applied to each direction.  Audit
`[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_trans_indiff
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z y : X j) (p q r : X k)
    (h₁ : ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c))
    (h₂ : ∀ c : X t, P.indiff (tri a j k t z p c) (tri a j k t y q c)) :
    ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t y q c) := by
  intro c
  refine ⟨?_, ?_⟩
  · exact ProductPref.IsWeakOrder.transitive _ _ _ (h₁ c).1 (h₂ c).1
  · exact ProductPref.IsWeakOrder.transitive _ _ _ (h₂ c).2 (h₁ c).2

/-- **Transitivity of uniform `≻` under `T-diag`.**

If `(x,r,c) ≻ (z,p,c)` for all `c` and `(z,p,c) ≻ (y,q,c)` for all `c`, then
`(x,r,c) ≻ (y,q,c)` for all `c`.  At each level: weak-order strict-transitivity.
Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_trans_strict
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z y : X j) (p q r : X k)
    (h₁ : ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c))
    (h₂ : ∀ c : X t, P.strict (tri a j k t z p c) (tri a j k t y q c)) :
    ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t y q c) := by
  intro c
  rcases h₁ c with ⟨h1fwd, h1nbwd⟩
  rcases h₂ c with ⟨h2fwd, h2nbwd⟩
  refine ⟨?_, ?_⟩
  · exact ProductPref.IsWeakOrder.transitive _ _ _ h1fwd h2fwd
  · -- ¬ weakPref (tri y q c) (tri x r c).
    intro hbwd
    -- weakPref (tri y q c) (tri x r c) ∧ weakPref (tri x r c) (tri z p c)
    --   → weakPref (tri y q c) (tri z p c).
    have : P.weakPref (tri a j k t y q c) (tri a j k t z p c) :=
      ProductPref.IsWeakOrder.transitive _ _ _ hbwd h1fwd
    exact h2nbwd this

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-transitivity audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_weakPref
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_indiff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trans_strict
