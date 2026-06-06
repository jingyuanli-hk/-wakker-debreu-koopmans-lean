/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: trichotomy classification of the diagonal Thomsen residue

This file proves a real, substantive structural classification theorem about the
single Thomsen residue `TBlockDiagonalResidue` (R1.1's final-piece content,
`OptionB_C1aDiagonalUnifiedCapstone.lean`):

**Under `T-diag` + `IsWeakOrder`, the trade-off relation between two
two-coordinate-different profiles is a single rigid relation uniformly across
all levels — exactly one of `≻`, `∼`, `≺`.**

This formalizes Wakker's IV.2.5 trichotomy: trade-off comparisons between
profiles are level-independent and totally ordered.

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_trichotomy` — at any fixed level `w`, one of three
  uniform alternatives across **all** levels holds: uniform `≻`, uniform `∼`, or
  uniform `≺`.
* `kBlockDiagonalResidue_trichotomy`, `jBlockDiagonalResidue_trichotomy` —
  analogous trichotomy theorems for the K- and J-permutation instances.

These confirm the residue's content is a genuine total preorder on the trade-
off space — not merely level-shift preservation, but full classification into
three uniform classes.

This file imports `OptionB_C1aDiagonalAntisym` and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalAntisym
import WakkerDebreuKoopmans.OptionB_C1aDiagonalThomsen
import WakkerDebreuKoopmans.OptionB_C1aDiagonalStrict

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

/-- **`T`-diagonal trichotomy: the trade-off relation falls into exactly one of
three uniform classes across all levels.**

Under `T-diag` and `IsWeakOrder`, for any background `a`, distinct `j`-values
`x ≠ z`, distinct `k`-values `r ≠ p`, and a sample level `w`, exactly one of:
* uniform strict `(x,r,c) ≻ (z,p,c)` for **all** levels `c`;
* uniform indifference `(x,r,c) ∼ (z,p,c)` for **all** levels `c`;
* uniform strict `(z,p,c) ≻ (x,r,c)` for **all** levels `c`.

(The existence direction; the at-most-one part follows from `tBlockDiagonalResidue_antisym`.)
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockDiagonalResidue_trichotomy
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w : X t)
    (hxz : x ≠ z) (hrp : r ≠ p) :
    (∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c)) ∨
    (∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c)) ∨
    (∀ c : X t, P.strict (tri a j k t z p c) (tri a j k t x r c)) := by
  -- By weak-order completeness at level w: either fwd or bwd `≽`.
  rcases ProductPref.IsWeakOrder.complete (P := P)
    (tri a j k t x r w) (tri a j k t z p w) with hfwd | hbwd
  · -- fwd: (x,r,w) ≽ (z,p,w).
    -- Subcase: also bwd at w?
    by_cases hbwd_w : P.weakPref (tri a j k t z p w) (tri a j k t x r w)
    · -- Indifference at w; level-invariance gives indifference at all c.
      right; left
      intro c
      exact tBlockDiagonalResidue_indiff hDiag a x z p r w c hxz hrp ⟨hfwd, hbwd_w⟩
    · -- Strict fwd at w; level-invariance and strict_one_direction give strict at all c.
      left
      intro c
      have hstrict_w : P.strict (tri a j k t x r w) (tri a j k t z p w) := ⟨hfwd, hbwd_w⟩
      exact tBlockDiagonalResidue_strict hDiag a x z p r w c hxz hrp hstrict_w
  · -- bwd: (z,p,w) ≽ (x,r,w).
    by_cases hfwd_w : P.weakPref (tri a j k t x r w) (tri a j k t z p w)
    · -- Indifference at w; uniform indifference at all c.
      right; left
      intro c
      exact tBlockDiagonalResidue_indiff hDiag a x z p r w c hxz hrp ⟨hfwd_w, hbwd⟩
    · -- Strict bwd at w; uniform strict bwd at all c (apply strict-preservation to reversed).
      right; right
      intro c
      have hstrict_w : P.strict (tri a j k t z p w) (tri a j k t x r w) := ⟨hbwd, hfwd_w⟩
      exact tBlockDiagonalResidue_strict hDiag a z x r p w c (Ne.symm hxz) (Ne.symm hrp)
        hstrict_w

/-- **`K`-diagonal trichotomy.** -/
theorem kBlockDiagonalResidue_trichotomy
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : KBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (c c' : X t) (v : X k)
    (huu : u ≠ u') (hcc : c ≠ c') :
    (∀ v' : X k, P.strict (tri a j k t u v' c) (tri a j k t u' v' c')) ∨
    (∀ v' : X k, P.indiff (tri a j k t u v' c) (tri a j k t u' v' c')) ∨
    (∀ v' : X k, P.strict (tri a j k t u' v' c') (tri a j k t u v' c)) := by
  rcases ProductPref.IsWeakOrder.complete (P := P)
    (tri a j k t u v c) (tri a j k t u' v c') with hfwd | hbwd
  · by_cases hbwd_v : P.weakPref (tri a j k t u' v c') (tri a j k t u v c)
    · right; left
      intro v'
      exact kBlockDiagonalResidue_indiff hDiag a u u' v v' c c' huu hcc ⟨hfwd, hbwd_v⟩
    · left
      intro v'
      exact kBlockDiagonalResidue_strict hDiag a u u' v v' c c' huu hcc ⟨hfwd, hbwd_v⟩
  · by_cases hfwd_v : P.weakPref (tri a j k t u v c) (tri a j k t u' v c')
    · right; left
      intro v'
      exact kBlockDiagonalResidue_indiff hDiag a u u' v v' c c' huu hcc ⟨hfwd_v, hbwd⟩
    · right; right
      intro v'
      -- Strict reversed at common k=v.  Need uniform strict reversed at every v'.
      -- Apply k-diag-strict with (u, u') swapped, (c, c') swapped: residue takes
      -- input strict (tri u' v c') (tri u v c), output strict (tri u' v' c') (tri u v' c).
      have hstrict_v : P.strict (tri a j k t u' v c') (tri a j k t u v c) := ⟨hbwd, hfwd_v⟩
      exact kBlockDiagonalResidue_strict hDiag a u' u v v' c' c
        (Ne.symm huu) (Ne.symm hcc) hstrict_v

/-- **`J`-diagonal trichotomy.** -/
theorem jBlockDiagonalResidue_trichotomy
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : JBlockDiagonalResidue P j k t)
    (a : Profile X) (v₁ v₂ : X k) (c₁ c₂ : X t) (u : X j)
    (hvv : v₁ ≠ v₂) (hcc : c₁ ≠ c₂) :
    (∀ u' : X j, P.strict (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂)) ∨
    (∀ u' : X j, P.indiff (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂)) ∨
    (∀ u' : X j, P.strict (tri a j k t u' v₂ c₂) (tri a j k t u' v₁ c₁)) := by
  rcases ProductPref.IsWeakOrder.complete (P := P)
    (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂) with hfwd | hbwd
  · by_cases hbwd_u : P.weakPref (tri a j k t u v₂ c₂) (tri a j k t u v₁ c₁)
    · right; left
      intro u'
      exact jBlockDiagonalResidue_indiff hDiag a u u' v₁ v₂ c₁ c₂ hvv hcc ⟨hfwd, hbwd_u⟩
    · left
      intro u'
      exact jBlockDiagonalResidue_strict hDiag a u u' v₁ v₂ c₁ c₂ hvv hcc ⟨hfwd, hbwd_u⟩
  · by_cases hfwd_u : P.weakPref (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂)
    · right; left
      intro u'
      exact jBlockDiagonalResidue_indiff hDiag a u u' v₁ v₂ c₁ c₂ hvv hcc ⟨hfwd_u, hbwd⟩
    · right; right
      intro u'
      have hstrict_u : P.strict (tri a j k t u v₂ c₂) (tri a j k t u v₁ c₁) := ⟨hbwd, hfwd_u⟩
      exact jBlockDiagonalResidue_strict hDiag a u u' v₂ v₁ c₂ c₁
        (Ne.symm hvv) (Ne.symm hcc) hstrict_u

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-trichotomy audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trichotomy
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_trichotomy
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_trichotomy
