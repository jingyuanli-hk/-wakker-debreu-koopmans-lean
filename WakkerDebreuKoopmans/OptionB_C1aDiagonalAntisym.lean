/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: antisymmetry / rigidity of the diagonal Thomsen residue

This file proves a real, useful structural theorem about the single Thomsen
residue `TBlockDiagonalResidue` (R1.1's final-piece content,
`OptionB_C1aDiagonalUnifiedCapstone.lean`): under the residue, the trade-off
relation between two two-coordinate-different profiles is **antisymmetric across
levels** — if the relation runs in opposite directions at two different levels,
both must be indifferences.

## The content

Under `T-diag`, level shifts preserve `≽` (and `≻`, and `∼`) — proved already.
Now: combining a `≽` at level `w` with the *reverse* `≽` at a different level
`c` forces both to actually be indifferences.  Equivalently: a strict preference
in one direction at *some* level is incompatible with any (even non-strict)
reverse preference at *any other* level.

This is the rigidity content classical Wakker §IV.2.5 trade-off consistency
encodes: the trade-off relation between two profiles is a single, level-
invariant relation (≻, ∼, or ≺) — not a pattern that can vary with the
auxiliary level.

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_antisym` — the antisymmetry-across-levels theorem: if
  `(x,r,w) ≽ (z,p,w)` and `(z,p,c) ≽ (x,r,c)`, then both are indifferences.
* `tBlockDiagonalResidue_strict_one_direction` — corollary: a strict preference
  at one level rules out the reverse preference at every other level.
* `kBlockDiagonalResidue_antisym`, `jBlockDiagonalResidue_antisym` — analogous
  antisymmetry theorems for the K- and J-permutation instances.

This file imports `OptionB_C1aDiagonalSymmetry` (for the `≽`-iff theorems
needed) and is **not** in the umbrella import.
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

/-- **`T`-diagonal antisymmetry across levels.**

Under `T-diag`, if `(x,r,w) ≽ (z,p,w)` at level `w` and `(z,p,c) ≽ (x,r,c)` at
some other level `c`, then *both* relations are indifferences (not strict
either way).

Proof: by the level-invariance of `≽`, the `≽` at `w` transports to `≽` at `c`,
and combined with the given reverse `≽` at `c` gives the `c`-indifference; the
same argument symmetrically gives the `w`-indifference.  Audit `[propext,
Quot.sound]`. -/
theorem tBlockDiagonalResidue_antisym
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (hfwd_w : P.weakPref (tri a j k t x r w) (tri a j k t z p w))
    (hbwd_c : P.weakPref (tri a j k t z p c) (tri a j k t x r c)) :
    P.indiff (tri a j k t x r w) (tri a j k t z p w) ∧
      P.indiff (tri a j k t x r c) (tri a j k t z p c) := by
  -- Transport hfwd_w to level c.
  have hfwd_c : P.weakPref (tri a j k t x r c) (tri a j k t z p c) :=
    hDiag a x z p r w c hxz hrp hfwd_w
  -- Transport hbwd_c to level w.
  have hbwd_w : P.weakPref (tri a j k t z p w) (tri a j k t x r w) :=
    hDiag a z x r p c w (Ne.symm hxz) (Ne.symm hrp) hbwd_c
  -- Both directions hold at both levels: indifferences.
  exact ⟨⟨hfwd_w, hbwd_w⟩, ⟨hfwd_c, hbwd_c⟩⟩

/-- **`T`-diagonal: strict one-direction is preserved at every level.**

Corollary of the antisymmetry: if `(x,r,w) ≻ (z,p,w)` strictly at level `w`,
then for every level `c`, the reverse `≽` at `c` cannot hold (i.e. only `≻`
holds, never `≼`).  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_strict_one_direction
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (hstrict_w : P.strict (tri a j k t x r w) (tri a j k t z p w)) :
    ¬ P.weakPref (tri a j k t z p c) (tri a j k t x r c) := by
  intro hbwd_c
  -- If hbwd_c held, antisymmetry would force the relation at w to be indifference,
  -- contradicting strictness.
  rcases hstrict_w with ⟨hfwd_w, hnotbwd_w⟩
  obtain ⟨hindiff_w, _⟩ :=
    tBlockDiagonalResidue_antisym hDiag a x z p r w c hxz hrp hfwd_w hbwd_c
  exact hnotbwd_w hindiff_w.2

/-- **`K`-diagonal antisymmetry across `k`-shifts.** -/
theorem kBlockDiagonalResidue_antisym
    {j k t : ι} (hDiag : KBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (v v' : X k) (c c' : X t)
    (huu : u ≠ u') (hcc : c ≠ c')
    (hfwd : P.weakPref (tri a j k t u v c) (tri a j k t u' v c'))
    (hbwd : P.weakPref (tri a j k t u' v' c') (tri a j k t u v' c)) :
    P.indiff (tri a j k t u v c) (tri a j k t u' v c') ∧
      P.indiff (tri a j k t u v' c) (tri a j k t u' v' c') := by
  -- Transport hfwd to common k-value v'.
  have hfwd_v' : P.weakPref (tri a j k t u v' c) (tri a j k t u' v' c') :=
    hDiag a u u' v v' c c' huu hcc hfwd
  -- Transport hbwd to common k-value v.
  -- hbwd : weakPref (tri u' v' c') (tri u v' c).  Apply K-diag with (u-slot=u', u'-slot=u,
  -- v-slot=v', v'-slot=v, c-slot=c', c'-slot=c) — input matches hbwd, output shifts v' → v:
  -- weakPref (tri u' v c') (tri u v c).
  have hbwd_v : P.weakPref (tri a j k t u' v c') (tri a j k t u v c) :=
    hDiag a u' u v' v c' c (Ne.symm huu) (Ne.symm hcc) hbwd
  exact ⟨⟨hfwd, hbwd_v⟩, ⟨hfwd_v', hbwd⟩⟩

/-- **`J`-diagonal antisymmetry across `j`-shifts.** -/
theorem jBlockDiagonalResidue_antisym
    {j k t : ι} (hDiag : JBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (v₁ v₂ : X k) (c₁ c₂ : X t)
    (hvv : v₁ ≠ v₂) (hcc : c₁ ≠ c₂)
    (hfwd : P.weakPref (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂))
    (hbwd : P.weakPref (tri a j k t u' v₂ c₂) (tri a j k t u' v₁ c₁)) :
    P.indiff (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂) ∧
      P.indiff (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂) := by
  -- Transport hfwd to common j-value u'.
  have hfwd_u' : P.weakPref (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂) :=
    hDiag a u u' v₁ v₂ c₁ c₂ hvv hcc hfwd
  -- Transport hbwd (input direction reversed: v₂,c₂ → v₁,c₁) to common j-value u.
  have hbwd_u : P.weakPref (tri a j k t u v₂ c₂) (tri a j k t u v₁ c₁) :=
    hDiag a u' u v₂ v₁ c₂ c₁ (Ne.symm hvv) (Ne.symm hcc) hbwd
  exact ⟨⟨hfwd, hbwd_u⟩, ⟨hfwd_u', hbwd⟩⟩

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-antisymmetry audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_antisym
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_one_direction
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_antisym
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_antisym
