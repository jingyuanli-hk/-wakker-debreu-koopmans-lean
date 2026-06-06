/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 final-piece: diagonal Thomsen residues are background-independent

This file proves another real structural theorem about the diagonal Thomsen
residues isolated in `OptionB_C1aDiagonalResidue.lean`: the truth of each diagonal
residue is **independent of the background's `j`-, `k`-, and `t`-values** (which
the `tri` profile overwrites anyway).  More substantively, it is also independent
of the background's values **at any single non-`{j,k,t}` coordinate** — no, this
is *not* automatic and is in general false (background changes off `{j,k,t}`
genuinely change the profile), so the precise honest statement is stronger:

**The diagonal residue's truth depends on the background only through its values
off `{j,k,t}`.** Backgrounds that agree off `{j,k,t}` give the same `tri` profiles
(so the residue is the same).  Backgrounds that disagree off `{j,k,t}` may give
different residue truth — that is a feature of the residue, not a bug, since the
residue is per-`a` quantified.

## What this file delivers (machine-checked, sound)

* `tri_eq_of_agreeOff` — two backgrounds that agree off `{j,k,t}` give the same
  `tri` profile (pure `Function.update` algebra).
* `tBlockDiagonalResidue_apply_of_agreeOff` — `T`-diag applied at one background
  with a witness from another background that agrees off `{j,k,t}` — confirming
  the residue is genuinely a property of the off-`{j,k,t}` part of the background.
* The `K`- and `J`-block analogues.

These confirm the diagonal residues do not gratuitously depend on coordinate
values they overwrite, and isolate exactly which background data they actually
consume — useful structural information that the §IV.5 forward construction can
exploit (it lets the forward proof relocate the background freely along the
overwritten coordinates).

This file imports `OptionB_C1aDiagonalResidue` and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalResidue

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

/-- **`tri` profiles for backgrounds agreeing off `{j,k,t}` are equal.**

If `a₁` and `a₂` agree at every coordinate `i ∉ {j,k,t}` (i.e. `a₁ i = a₂ i`),
then `tri a₁ j k t u v c = tri a₂ j k t u v c`.  Pure `Function.update` algebra:
the `j`-, `k`-, `t`-values are overwritten, and the off-`{j,k,t}` values agree by
hypothesis.  Audit `[propext, Quot.sound]`. -/
theorem tri_eq_of_agreeOff (a₁ a₂ : Profile X) (j k t : ι)
    (hagree : ∀ i, i ≠ j → i ≠ k → i ≠ t → a₁ i = a₂ i)
    (u : X j) (v : X k) (c : X t) :
    tri a₁ j k t u v c = tri a₂ j k t u v c := by
  unfold tri
  funext i
  by_cases hit : i = t
  · subst hit; simp [Function.update_self]
  · rw [Function.update_of_ne hit, Function.update_of_ne hit]
    by_cases hik : i = k
    · subst hik; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hik, Function.update_of_ne hik]
      by_cases hij : i = j
      · subst hij; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hij, Function.update_of_ne hij]
        exact hagree i hij hik hit

/-- **`T`-diagonal residue is a property of the off-`{j,k,t}` background.**

Backgrounds that agree off `{j,k,t}` produce identical `tri` profiles, so a
`T`-diag application at `a₁` directly transports to a witness at `a₂`.  Audit
`[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_apply_of_agreeOff
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a₁ a₂ : Profile X)
    (hagree : ∀ i, i ≠ j → i ≠ k → i ≠ t → a₁ i = a₂ i)
    (x z : X j) (p r : X k) (w c : X t)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (hw : P.weakPref (tri a₂ j k t x r w) (tri a₂ j k t z p w)) :
    P.weakPref (tri a₂ j k t x r c) (tri a₂ j k t z p c) := by
  -- Convert to a₁-form via tri equality, apply hDiag, convert back.
  rw [← tri_eq_of_agreeOff a₁ a₂ j k t hagree x r w,
      ← tri_eq_of_agreeOff a₁ a₂ j k t hagree z p w] at hw
  have h := hDiag a₁ x z p r w c hxz hrp hw
  rw [tri_eq_of_agreeOff a₁ a₂ j k t hagree x r c,
      tri_eq_of_agreeOff a₁ a₂ j k t hagree z p c] at h
  exact h

/-- **`K`-diagonal residue is a property of the off-`{j,k,t}` background.** -/
theorem kBlockDiagonalResidue_apply_of_agreeOff
    {j k t : ι} (hDiag : KBlockDiagonalResidue P j k t)
    (a₁ a₂ : Profile X)
    (hagree : ∀ i, i ≠ j → i ≠ k → i ≠ t → a₁ i = a₂ i)
    (u u' : X j) (v v' : X k) (c c' : X t)
    (huu : u ≠ u') (hcc : c ≠ c')
    (hw : P.weakPref (tri a₂ j k t u v c) (tri a₂ j k t u' v c')) :
    P.weakPref (tri a₂ j k t u v' c) (tri a₂ j k t u' v' c') := by
  rw [← tri_eq_of_agreeOff a₁ a₂ j k t hagree u v c,
      ← tri_eq_of_agreeOff a₁ a₂ j k t hagree u' v c'] at hw
  have h := hDiag a₁ u u' v v' c c' huu hcc hw
  rw [tri_eq_of_agreeOff a₁ a₂ j k t hagree u v' c,
      tri_eq_of_agreeOff a₁ a₂ j k t hagree u' v' c'] at h
  exact h

/-- **`J`-diagonal residue is a property of the off-`{j,k,t}` background.** -/
theorem jBlockDiagonalResidue_apply_of_agreeOff
    {j k t : ι} (hDiag : JBlockDiagonalResidue P j k t)
    (a₁ a₂ : Profile X)
    (hagree : ∀ i, i ≠ j → i ≠ k → i ≠ t → a₁ i = a₂ i)
    (u u' : X j) (v₁ v₂ : X k) (c₁ c₂ : X t)
    (hvv : v₁ ≠ v₂) (hcc : c₁ ≠ c₂)
    (hw : P.weakPref (tri a₂ j k t u v₁ c₁) (tri a₂ j k t u v₂ c₂)) :
    P.weakPref (tri a₂ j k t u' v₁ c₁) (tri a₂ j k t u' v₂ c₂) := by
  rw [← tri_eq_of_agreeOff a₁ a₂ j k t hagree u v₁ c₁,
      ← tri_eq_of_agreeOff a₁ a₂ j k t hagree u v₂ c₂] at hw
  have h := hDiag a₁ u u' v₁ v₂ c₁ c₂ hvv hcc hw
  rw [tri_eq_of_agreeOff a₁ a₂ j k t hagree u' v₁ c₁,
      tri_eq_of_agreeOff a₁ a₂ j k t hagree u' v₂ c₂] at h
  exact h

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-base-independence audit -/

#print axioms WakkerInfra.ProductPref.tri_eq_of_agreeOff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_apply_of_agreeOff
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_apply_of_agreeOff
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_apply_of_agreeOff
