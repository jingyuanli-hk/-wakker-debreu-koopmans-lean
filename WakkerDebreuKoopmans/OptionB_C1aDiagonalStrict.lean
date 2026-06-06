/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: the diagonal Thomsen residue preserves strict preference

This file proves another real structural theorem about the single Thomsen residue
`TBlockDiagonalResidue` (R1.1's final-piece content,
`OptionB_C1aDiagonalUnifiedCapstone.lean`): the residue preserves not just `≽`
but also **strict preference** `≻`.  Combined with prior level-invariance, this
shows the residue transfers the *whole* trade-off relation (≽, ≻, ∼) across
`t`-levels — the genuine Wakker IV.2.5 trade-off consistency content.

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_strict` — under `T-diag`, strict preference between two
  two-coordinate-different profiles transfers between any `t`-levels:
  `(x,r,w) ≻ (z,p,w) → (x,r,c) ≻ (z,p,c)`.
* `tBlockDiagonalResidue_strict_iff` — equivalent forms at any pair of levels.
* `kBlockDiagonalResidue_strict`, `jBlockDiagonalResidue_strict` — analogous
  strict-preservation theorems for the two permutation-instances.

These confirm the diagonal residue captures the **full trade-off relation**
(weak, strict, indifference all transfer), not merely a one-way preservation of
`≽`.  This is the cleanest expression of Wakker's IV.2.5 trade-off-consistency
content for the cross-pair on the third coordinate.

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

/-- **`T`-diagonal preserves strict preference between two-coord-different
profiles across `t`-levels.**

If `(x,r,w) ≻ (z,p,w)` (strict) and `T-diag` holds, then `(x,r,c) ≻ (z,p,c)` for
every `c : X t`.  Strict = `≽` (preserved by `T-diag` directly) plus negation of
the reverse `≽` (preserved by `T-diag` via the symmetric form
`tBlockDiagonalResidue_symm`: a `(z,p,c) ≽ (x,r,c)` reverse at `c` would imply
the same at `w`, contradicting strictness).  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_strict
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (hw : P.strict (tri a j k t x r w) (tri a j k t z p w)) :
    P.strict (tri a j k t x r c) (tri a j k t z p c) := by
  rcases hw with ⟨hfwd, hnotbwd⟩
  refine ⟨?_, ?_⟩
  · -- ≽-direction: T-diag direct.
    exact hDiag a x z p r w c hxz hrp hfwd
  · -- Reverse ≽ would contradict strictness at w.
    intro hrev_c
    -- hrev_c : weakPref (tri ... z p c) (tri ... x r c).
    -- T-diag with (x,z) → (z,x), (p,r) → (r,p) shifts c → w:
    -- weakPref (tri ... z p c) (tri ... x r c) → weakPref (tri ... z p w) (tri ... x r w).
    have hrev_w : P.weakPref (tri a j k t z p w) (tri a j k t x r w) :=
      hDiag a z x r p c w (Ne.symm hxz) (Ne.symm hrp) hrev_c
    exact hnotbwd hrev_w

/-- **Iff form of `T`-diag's strict preservation.**

`T-diag` makes strict preference between two-coord-different profiles equivalent
across any pair of `t`-levels.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_strict_iff
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (hxz : x ≠ z) (hrp : r ≠ p) :
    P.strict (tri a j k t x r w) (tri a j k t z p w) ↔
      P.strict (tri a j k t x r c) (tri a j k t z p c) :=
  ⟨tBlockDiagonalResidue_strict hDiag a x z p r w c hxz hrp,
   tBlockDiagonalResidue_strict hDiag a x z p r c w hxz hrp⟩

/-- **`K`-diagonal preserves strict preference.** -/
theorem kBlockDiagonalResidue_strict
    {j k t : ι} (hDiag : KBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (v v' : X k) (c c' : X t)
    (huu : u ≠ u') (hcc : c ≠ c')
    (hw : P.strict (tri a j k t u v c) (tri a j k t u' v c')) :
    P.strict (tri a j k t u v' c) (tri a j k t u' v' c') := by
  rcases hw with ⟨hfwd, hnotbwd⟩
  refine ⟨?_, ?_⟩
  · exact hDiag a u u' v v' c c' huu hcc hfwd
  · intro hrev_v'
    -- hrev_v' : weakPref (tri ... u' v' c') (tri ... u v' c).
    -- K-diag with input shape (u-slot, u'-slot) = (u', u), v-slot=v', shift v'-slot=v,
    -- (c, c') = (c', c): the residue takes
    -- weakPref (tri u' v' c') (tri u v' c) → weakPref (tri u' v c') (tri u v c).
    have hrev_v : P.weakPref (tri a j k t u' v c') (tri a j k t u v c) :=
      hDiag a u' u v' v c' c (Ne.symm huu) (Ne.symm hcc) hrev_v'
    exact hnotbwd hrev_v

/-- **`J`-diagonal preserves strict preference.** -/
theorem jBlockDiagonalResidue_strict
    {j k t : ι} (hDiag : JBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (v₁ v₂ : X k) (c₁ c₂ : X t)
    (hvv : v₁ ≠ v₂) (hcc : c₁ ≠ c₂)
    (hw : P.strict (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂)) :
    P.strict (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂) := by
  rcases hw with ⟨hfwd, hnotbwd⟩
  refine ⟨?_, ?_⟩
  · exact hDiag a u u' v₁ v₂ c₁ c₂ hvv hcc hfwd
  · intro hrev_u'
    -- hrev_u' : weakPref (tri ... u' v₂ c₂) (tri ... u' v₁ c₁).
    -- J-diag: shift first slot u' → u (output is independent of which u/u' we name as "common";
    -- swap (v₁, v₂) and (c₁, c₂) in the input to match the residue's signature).
    -- The residue takes: wp (tri u v₁ c₁) (tri u v₂ c₂) → wp (tri u' v₁ c₁) (tri u' v₂ c₂),
    -- with v₁ ≠ v₂ and c₁ ≠ c₂.  Apply with (v₁,v₂)=(v₂,v₁), (c₁,c₂)=(c₂,c₁):
    -- input wp (tri u v₂ c₂) (tri u v₁ c₁); output wp (tri u' v₂ c₂) (tri u' v₁ c₁).
    -- We have hrev_u' : wp (tri u' v₂ c₂) (tri u' v₁ c₁).  Need to convert to `u`-form:
    -- swap roles of u and u' in the residue (apply with (u, u') = (u', u)).
    have hrev_u : P.weakPref (tri a j k t u v₂ c₂) (tri a j k t u v₁ c₁) :=
      hDiag a u' u v₂ v₁ c₂ c₁ (Ne.symm hvv) (Ne.symm hcc) hrev_u'
    exact hnotbwd hrev_u

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-strict audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_iff
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_strict
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_strict
