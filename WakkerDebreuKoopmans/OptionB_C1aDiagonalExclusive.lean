/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: pairwise mutual exclusivity of the trichotomy classes

This file proves that the three trichotomy classes of the single Thomsen residue
`TBlockDiagonalResidue` (R1.1's final-piece content,
`OptionB_C1aDiagonalUnifiedCapstone.lean`) are **pairwise mutually exclusive** —
strengthening the previously-proved exhaustive trichotomy
(`OptionB_C1aDiagonalTrichotomy.lean`) to an "exactly one" classification.

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_strict_indiff_exclusive` — uniform `≻` and uniform `∼`
  cannot both hold for the same profile pair.
* `tBlockDiagonalResidue_strict_dual_exclusive` — uniform `≻` (forward) and
  uniform `≻` (reversed) cannot both hold.
* `tBlockDiagonalResidue_indiff_strict_dual_exclusive` — uniform `∼` and uniform
  `≻` (reversed) cannot both hold.
* `tBlockDiagonalResidue_trichotomy_unique` — packaged: exactly one of the three
  trichotomy classes holds.

These complete the classification: the diagonal residue assigns to each
two-coord-different profile pair *exactly one* of `{≻, ∼, ≺}`, never two — the
sharpest possible total-classification statement.

This file imports `OptionB_C1aDiagonalAntisym` (for the level-rigidity machinery)
and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalAntisym

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

/-- **Uniform `≻` and uniform `∼` are incompatible.**

If `(x,r,·) ≻ (z,p,·)` for all `c` (uniform strict) and `(x,r,·) ∼ (z,p,·)` for
all `c` (uniform indifference), then a contradiction at any single level: an
indifference's reverse `≽` contradicts strictness's negation of the reverse.
Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_strict_indiff_exclusive
    {j k t : ι}
    (a : Profile X) (x z : X j) (p r : X k) [Inhabited (X t)]
    (hStrict : ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c))
    (hIndiff : ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c)) :
    False := by
  let c : X t := default
  rcases hStrict c with ⟨_, hnbwd⟩
  rcases hIndiff c with ⟨_, hbwd⟩
  exact hnbwd hbwd

/-- **Uniform forward and reversed `≻` are incompatible.**

If `(x,r,·) ≻ (z,p,·)` for all `c` and `(z,p,·) ≻ (x,r,·)` for all `c`, then
contradiction at any single level: forward `≻` gives `≽`, reversed `≻` gives the
reverse `≽`, and forward strict's negation of the reverse contradicts the
reverse `≽`.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_strict_dual_exclusive
    {j k t : ι}
    (a : Profile X) (x z : X j) (p r : X k) [Inhabited (X t)]
    (hFwd : ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c))
    (hBwd : ∀ c : X t, P.strict (tri a j k t z p c) (tri a j k t x r c)) :
    False := by
  let c : X t := default
  rcases hFwd c with ⟨_, hnbwd⟩
  rcases hBwd c with ⟨hbwd, _⟩
  exact hnbwd hbwd

/-- **Uniform `∼` and uniform reversed `≻` are incompatible.**

Indifference's forward direction contradicts the reversed-strict's negation of
its forward direction.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_indiff_strict_dual_exclusive
    {j k t : ι}
    (a : Profile X) (x z : X j) (p r : X k) [Inhabited (X t)]
    (hIndiff : ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c))
    (hBwd : ∀ c : X t, P.strict (tri a j k t z p c) (tri a j k t x r c)) :
    False := by
  let c : X t := default
  rcases hIndiff c with ⟨hfwd, _⟩
  rcases hBwd c with ⟨_, hnfwd⟩
  exact hnfwd hfwd

/-- **Trichotomy uniqueness: at most one class holds (combined with the
exhaustive trichotomy, exactly one).**

Packaged conjunction of the three pairwise-exclusivity theorems: any two of
{uniform `≻`, uniform `∼`, uniform `≻`-reversed} are jointly inconsistent.
Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_trichotomy_unique
    {j k t : ι}
    (a : Profile X) (x z : X j) (p r : X k) [Inhabited (X t)] :
    -- "≻ and ∼ exclusive"
    ((∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c)) ∧
       (∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c)) → False) ∧
    -- "≻ and ≻-reversed exclusive"
    ((∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c)) ∧
       (∀ c : X t, P.strict (tri a j k t z p c) (tri a j k t x r c)) → False) ∧
    -- "∼ and ≻-reversed exclusive"
    ((∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c)) ∧
       (∀ c : X t, P.strict (tri a j k t z p c) (tri a j k t x r c)) → False) :=
  ⟨fun ⟨h1, h2⟩ =>
     tBlockDiagonalResidue_strict_indiff_exclusive a x z p r h1 h2,
   fun ⟨h1, h2⟩ =>
     tBlockDiagonalResidue_strict_dual_exclusive a x z p r h1 h2,
   fun ⟨h1, h2⟩ =>
     tBlockDiagonalResidue_indiff_strict_dual_exclusive a x z p r h1 h2⟩

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-exclusive audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_indiff_exclusive
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_dual_exclusive
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_strict_dual_exclusive
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trichotomy_unique
