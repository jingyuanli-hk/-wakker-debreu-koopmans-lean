/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 final-piece: the `(j,t)` permutation reassociation on `tri`

This file proves the `(j,t)` coordinate-role swap on `tri`, complementing the
`(j,k)` and `(k,t)` swaps in `OptionB_C1aDiagonalPermutation.lean`.  Together the
three transpositions generate every permutation of the three coordinate roles,
which is the basis for showing the three diagonal residues are permutation-
instances of one another.

## What this file delivers (machine-checked, sound)

* `tri_perm_jt` — coordinate-role swap on `tri` for `(j,t)`:
  `tri a j k t u v c = tri a t k j c v u` (proved pointwise via `funext`).
* `jBlockDiagonalResidue_iff_tBlock_perm` —
  `JBlockDiagonalResidue P j k t ↔ TBlockDiagonalResidue P t k j`.

## Net effect on R1.1's open frontier

Combined with `OptionB_C1aDiagonalPermutation.kBlockDiagonalResidue_iff_tBlock_perm`,
**all three diagonal residues are permutation-instances of one another**:
* `T-diag P j k t` itself;
* `K-diag P j k t = T-diag P j t k` (k↔t roles swapped);
* `J-diag P j k t = T-diag P t k j` (j↔t roles swapped).

So R1.1's genuinely-open content is **a single Thomsen-type theorem**
(`TBlockDiagonalResidue`), and discharging it for every triple of coordinates
closes all three diagonals — and with the prior work, the entire
`CrossPairCancellationData` and R1.1.

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

/-- **Coordinate-role swap on `tri`: `(j,t)`.**

`tri a j k t u v c = tri a t k j c v u`: the `j` and `t` roles are interchanged
(values move with the names; the underlying profile is unchanged).  Proved
pointwise via `funext` on each `i : ι`.  Audit `[propext, Quot.sound]`. -/
theorem tri_perm_jt (a : Profile X) (j k t : ι) (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (u : X j) (v : X k) (c : X t) :
    tri a j k t u v c = tri a t k j c v u := by
  unfold tri
  funext i
  by_cases hij : i = j
  · subst hij
    -- LHS at i=j:
    --   update (update (update a j u) k v) t c j = u    (since j ≠ k, j ≠ t)
    -- RHS at i=j:
    --   update (update (update a t c) k v) j u j = u    (Function.update_self)
    rw [Function.update_of_ne hjt, Function.update_of_ne hjk, Function.update_self,
        Function.update_self]
  · by_cases hik : i = k
    · subst hik
      -- LHS at i=k:
      --   update (update (update a j u) k v) t c k = v    (since k ≠ t)
      -- RHS at i=k:
      --   update (update (update a t c) k v) j u k = v    (since k ≠ j)
      rw [Function.update_of_ne hkt, Function.update_self,
          Function.update_of_ne hjk.symm, Function.update_self]
    · by_cases hit : i = t
      · subst hit
        -- LHS at i=t:
        --   update ... t c t = c    (Function.update_self)
        -- RHS at i=t:
        --   update (update (update a t c) k v) j u t = c    (since t ≠ j, t ≠ k)
        rw [Function.update_self,
            Function.update_of_ne hjt.symm, Function.update_of_ne hkt.symm,
            Function.update_self]
      · -- All four updates miss `i`; LHS = RHS = a i.
        rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij,
            Function.update_of_ne hij, Function.update_of_ne hik, Function.update_of_ne hit]

/-- **`JBlockDiagonalResidue P j k t` is `TBlockDiagonalResidue P t k j` under
the `(j,t)` role-swap.**

The same Thomsen content with the `j` and `t` role-labels swapped: `J-diag`
shifts the *first* slot of `tri a j k t · · ·` (the `j`-slot, common value
`u → u'`) when the second and third slots differ, while `T-diag P t k j` shifts
the *third* slot of `tri a t k j · · ·` (the `j`-slot of the original
coordinates, since the third arg of `T-diag P j' k' t'` is the `t'`-of-T-diag-
which-is-`j`-here).  Proof: rewrite via `tri_perm_jt` to align profile shapes;
the residue quantifications then match by argument-renaming.  Audit `[propext,
Quot.sound]`. -/
theorem jBlockDiagonalResidue_iff_tBlock_perm
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    JBlockDiagonalResidue P j k t ↔ TBlockDiagonalResidue P t k j := by
  -- Helper: tri a t k j A B C = tri a j k t C B A.  Apply tri_perm_jt to coords
  -- (t, k, j) with disequalities (t≠k = hkt.symm), (t≠j = hjt.symm), (k≠j = hjk.symm).
  have eqPerm : ∀ (a : Profile X) (A : X t) (B : X k) (C : X j),
      tri a t k j A B C = tri a j k t C B A := by
    intro a A B C
    exact tri_perm_jt a t k j (Ne.symm hkt) (Ne.symm hjt) (Ne.symm hjk) A B C
  constructor
  · -- J-diag → T-diag P t k j.
    intro hJ a x z p r w c hxz hrp hw
    -- Goal:  weakPref (tri a t k j x r c) (tri a t k j z p c).
    -- Premise hw:  weakPref (tri a t k j x r w) (tri a t k j z p w).
    -- Rewrite both sides via eqPerm to T-diag-of-J-diag-coords form.
    rw [eqPerm a x r w, eqPerm a z p w] at hw
    rw [eqPerm a x r c, eqPerm a z p c]
    -- Now hw:    weakPref (tri a j k t w r x) (tri a j k t w p z)   (j-slot=w common, k-slots r,p differ, t-slots x,z differ)
    -- Goal:      weakPref (tri a j k t c r x) (tri a j k t c p z)   (j-slot=c common, same k-slots, same t-slots)
    -- J-diag P j k t: ∀ a u u' v₁ v₂ c₁ c₂, v₁≠v₂ → c₁≠c₂ →
    --     wp (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂) → wp (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂).
    -- Match: u=w, u'=c, v₁=r, v₂=p, c₁=x, c₂=z.
    -- Inequalities: v₁≠v₂ = r≠p = hrp; c₁≠c₂ = x≠z = hxz.
    exact hJ a w c r p x z hrp hxz hw
  · -- T-diag P t k j → J-diag.
    intro hT a u u' v₁ v₂ c₁ c₂ hvv hcc hw
    -- Premise hw: weakPref (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂).
    -- Goal:       weakPref (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂).
    -- Rewrite via eqPerm.symm (tri a j k t C B A = tri a t k j A B C) to T-diag-form.
    rw [← eqPerm a c₁ v₁ u, ← eqPerm a c₂ v₂ u] at hw
    rw [← eqPerm a c₁ v₁ u', ← eqPerm a c₂ v₂ u']
    -- Now hw:    weakPref (tri a t k j c₁ v₁ u) (tri a t k j c₂ v₂ u)
    --   (t-slots c₁,c₂ differ, k-slots v₁,v₂ differ, j-slot=u common).
    -- Goal:      weakPref (tri a t k j c₁ v₁ u') (tri a t k j c₂ v₂ u')
    --   (j-slot=u' common — the shifted value).
    -- T-diag P t k j: ∀ a x z p r w c, x≠z → r≠p →
    --     wp (tri a t k j x r w) (tri a t k j z p w) → wp (tri a t k j x r c) (tri a t k j z p c).
    -- Match: x=c₁, z=c₂, r=v₁, p=v₂, w=u (common j-slot of T-diag), c=u'.
    -- Inequalities: x≠z = c₁≠c₂ = hcc; r≠p = v₁≠v₂ = hvv.
    exact hT a c₁ c₂ v₂ v₁ u u' hcc hvv hw

end ProductPref
end WakkerInfra

/-! ## R1.1 (j,t)-permutation reassociation audit -/

#print axioms WakkerInfra.ProductPref.tri_perm_jt
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_iff_tBlock_perm
