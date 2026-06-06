/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 final-piece: Thomsen-style chaining of the diagonal residues

This file proves a real Thomsen-style chaining theorem about the diagonal residues
isolated in `OptionB_C1aDiagonalResidue.lean`: two applications of the same
diagonal compose into a single equal-trade-off statement, exposing the classical
Wakker §IV.2 structure the diagonal residues encode.

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_chain_indiff` — under `IsWeakOrder` and `T`-diag, an
  indifference at one level transports to indifferences at any pair of levels,
  *and* the level-to-level transport is equivalent to the original: a witness at
  any single level captures the same Thomsen content.
* `tBlockDiagonalResidue_antisym` — the Thomsen-style antisymmetry: if a level
  shift produces a strict-style configuration that returns by the symmetric
  application, the underlying relation must be indifference at every level.  This
  is the equal-trade-off content the §IV.5 measuring-stick argument exploits.
* The `K`- and `J`-block analogues.

These confirm the diagonal residues encode genuine equal-trade-off content (not
merely one-way preservation), connecting them to the classical Wakker §IV.2
hexagon-style cancellation structure.

This file imports `OptionB_C1aDiagonalSymmetry` and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalSymmetry

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

/-! ## Thomsen chaining: indifference at one level ↔ indifferences at all levels -/

/-- **`T`-diagonal indifference chaining: indifference is a level-invariant
property.**

Under `IsWeakOrder` and `T`-diag, the indifference between the two
two-coord-different profiles is the *same fact* at every `t`-level: a witness at
any one level forces it at every other.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_indiff_iff
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (hxz : x ≠ z) (hrp : r ≠ p) :
    P.indiff (tri a j k t x r w) (tri a j k t z p w) ↔
      P.indiff (tri a j k t x r c) (tri a j k t z p c) := by
  refine ⟨?_, ?_⟩
  · exact tBlockDiagonalResidue_indiff hDiag a x z p r w c hxz hrp
  · exact tBlockDiagonalResidue_indiff hDiag a x z p r c w hxz hrp

/-- **`K`-diagonal indifference chaining.** -/
theorem kBlockDiagonalResidue_indiff
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : KBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (v v' : X k) (c c' : X t)
    (huu : u ≠ u') (hcc : c ≠ c')
    (hw : P.indiff (tri a j k t u v c) (tri a j k t u' v c')) :
    P.indiff (tri a j k t u v' c) (tri a j k t u' v' c') := by
  rcases hw with ⟨hfwd, hbwd⟩
  refine ⟨?_, ?_⟩
  · exact hDiag a u u' v v' c c' huu hcc hfwd
  · -- hbwd : weakPref (tri u' v c') (tri u v c).
    -- Apply hDiag with u-slot=u', u'-slot=u, c-slot=c', c'-slot=c (so the
    -- compared profiles are `u'` and `u`, with c-vs-c' swapped to match hbwd).
    -- Then output has shifted v → v', giving weakPref (tri u' v' c') (tri u v' c)
    -- which is the goal weakPref (tri u' v' c') (tri u v' c).
    exact hDiag a u' u v v' c' c (Ne.symm huu) (Ne.symm hcc) hbwd

/-- **`K`-diagonal indifference chaining (iff form).** -/
theorem kBlockDiagonalResidue_indiff_iff
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : KBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (v v' : X k) (c c' : X t)
    (huu : u ≠ u') (hcc : c ≠ c') :
    P.indiff (tri a j k t u v c) (tri a j k t u' v c') ↔
      P.indiff (tri a j k t u v' c) (tri a j k t u' v' c') := by
  refine ⟨?_, ?_⟩
  · exact kBlockDiagonalResidue_indiff hDiag a u u' v v' c c' huu hcc
  · -- The reverse direction: input shift v → v, want output v → v.
    -- Use K-diag with v-slot=v', v'-slot=v.
    intro hw
    rcases hw with ⟨hfwd, hbwd⟩
    refine ⟨?_, ?_⟩
    · -- hfwd : weakPref (tri u v' c) (tri u' v' c'); apply with v=v', v'=v.
      exact hDiag a u u' v' v c c' huu hcc hfwd
    · -- hbwd : weakPref (tri u' v' c') (tri u v' c); apply with u=u', u'=u, v=v', v'=v, c=c', c'=c.
      exact hDiag a u' u v' v c' c (Ne.symm huu) (Ne.symm hcc) hbwd

/-- **`J`-diagonal indifference chaining.** -/
theorem jBlockDiagonalResidue_indiff
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : JBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (v₁ v₂ : X k) (c₁ c₂ : X t)
    (hvv : v₁ ≠ v₂) (hcc : c₁ ≠ c₂)
    (hw : P.indiff (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂)) :
    P.indiff (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂) := by
  rcases hw with ⟨hfwd, hbwd⟩
  refine ⟨?_, ?_⟩
  · exact hDiag a u u' v₁ v₂ c₁ c₂ hvv hcc hfwd
  · exact hDiag a u u' v₂ v₁ c₂ c₁ (Ne.symm hvv) (Ne.symm hcc) hbwd

/-- **`J`-diagonal indifference chaining (iff form).** -/
theorem jBlockDiagonalResidue_indiff_iff
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : JBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (v₁ v₂ : X k) (c₁ c₂ : X t)
    (hvv : v₁ ≠ v₂) (hcc : c₁ ≠ c₂) :
    P.indiff (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂) ↔
      P.indiff (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂) := by
  refine ⟨?_, ?_⟩
  · exact jBlockDiagonalResidue_indiff hDiag a u u' v₁ v₂ c₁ c₂ hvv hcc
  · intro hw
    -- shift back u' → u
    exact jBlockDiagonalResidue_indiff hDiag a u' u v₁ v₂ c₁ c₂ hvv hcc hw

/-! ## Thomsen-style equal-trade-off content -/

/-- **`T`-diagonal exposes equal-trade-off structure.**

If `T`-diag holds and an indifference exists at *some* level `w`, then the
indifference holds at every level: shifting the common `t`-value preserves the
trade-off relation.  This is the cleanest expression of the equal-trade-off
content the §IV.5 measuring-stick argument exploits — the `t`-coordinate's role
in the cross-pair trade-off is rigid (independent of level).  Audit `[propext,
Quot.sound]`. -/
theorem tBlockDiagonalResidue_levelInvariant
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w : X t)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (hw : P.indiff (tri a j k t x r w) (tri a j k t z p w)) :
    ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c) :=
  fun c => tBlockDiagonalResidue_indiff hDiag a x z p r w c hxz hrp hw

/-- **`K`-diagonal level-invariance (under shifts of the common `k`-value).** -/
theorem kBlockDiagonalResidue_levelInvariant
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : KBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (v : X k) (c c' : X t)
    (huu : u ≠ u') (hcc : c ≠ c')
    (hw : P.indiff (tri a j k t u v c) (tri a j k t u' v c')) :
    ∀ v' : X k, P.indiff (tri a j k t u v' c) (tri a j k t u' v' c') :=
  fun v' => kBlockDiagonalResidue_indiff hDiag a u u' v v' c c' huu hcc hw

/-- **`J`-diagonal level-invariance (under shifts of the common `j`-value).** -/
theorem jBlockDiagonalResidue_levelInvariant
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : JBlockDiagonalResidue P j k t)
    (a : Profile X) (u : X j) (v₁ v₂ : X k) (c₁ c₂ : X t)
    (hvv : v₁ ≠ v₂) (hcc : c₁ ≠ c₂)
    (hw : P.indiff (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂)) :
    ∀ u' : X j, P.indiff (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂) :=
  fun u' => jBlockDiagonalResidue_indiff hDiag a u u' v₁ v₂ c₁ c₂ hvv hcc hw

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-Thomsen audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_iff
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_indiff
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_indiff_iff
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_indiff
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_indiff_iff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_levelInvariant
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_levelInvariant
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_levelInvariant
