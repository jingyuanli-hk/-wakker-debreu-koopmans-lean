/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 final-piece: the three diagonal residues are the same statement
  under coordinate-role permutation

This file proves a real structural reduction on the three diagonal Thomsen
residues isolated in `OptionB_C1aDiagonalResidue.lean`: they are **the same
statement** applied to different role-assignments of the three coordinates.

## What this file delivers (machine-checked, sound)

* `tri_perm_kt` — coordinate-role swap on `tri` for `(k,t)`:
  `tri a j k t u v c = tri a j t k u c v`.  Pure `Function.update_comm`.
* `tri_perm_jk` — `(j,k)` swap: `tri a j k t u v c = tri a k j t v u c`.
* `kBlockDiagonalResidue_iff_tBlock_perm` — `KBlockDiagonalResidue P j k t` ↔
  `TBlockDiagonalResidue P j t k` (T-diag with k and t roles swapped).

## Net effect on R1.1's open frontier

The three diagonal residues are *not* fully independent — at least the K-diag is
the T-diag applied to the permuted coordinate triple `(j, t, k)`.  So the genuine
open frontier is at most two distinct Thomsen statements (T-diag P j k t and
J-diag P j k t), with K-diag a permutation-instance of T-diag.

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

/-- **Coordinate-role swap on `tri`: `(j,k)`.**

`tri a j k t u v c = tri a k j t v u c`: rename the first two coordinate roles
(values move with the names; the underlying profile is unchanged).  Audit
`[propext, Quot.sound]`. -/
theorem tri_perm_jk (a : Profile X) (j k t : ι) (hjk : j ≠ k)
    (u : X j) (v : X k) (c : X t) :
    tri a j k t u v c = tri a k j t v u c := by
  unfold tri
  rw [Function.update_comm hjk u v a]

/-- **Coordinate-role swap on `tri`: `(k,t)`.**

`tri a j k t u v c = tri a j t k u c v`: pure `Function.update_comm`.  Audit
`[propext, Quot.sound]`. -/
theorem tri_perm_kt (a : Profile X) (j k t : ι) (hkt : k ≠ t)
    (u : X j) (v : X k) (c : X t) :
    tri a j k t u v c = tri a j t k u c v := by
  unfold tri
  -- LHS: update (update (update a j u) k v) t c
  -- RHS: update (update (update a j u) t c) k v
  rw [Function.update_comm (Ne.symm hkt) c v (Function.update a j u)]

/-- **`KBlockDiagonalResidue P j k t` is `TBlockDiagonalResidue P j t k`
under the `(k,t)` role-swap.**

Both express the same Thomsen content (shifting one of the three "third"
coordinates' common value preserves `≽` between two profiles differing in the
other two), with the role-labels of `k` and `t` swapped.  Proof: rewrite via
`tri_perm_kt` to align the profile shapes; the residue quantifications then match
modulo argument renaming.  Audit `[propext, Quot.sound]`. -/
theorem kBlockDiagonalResidue_iff_tBlock_perm
    {j k t : ι} (hkt : k ≠ t) :
    KBlockDiagonalResidue P j k t ↔ TBlockDiagonalResidue P j t k := by
  constructor
  · -- K-diag → T-diag with (k,t) swapped.
    intro hK a x z p r w c hxz hrp hw
    -- Profile shape in the goal: tri a j t k _ _ _.
    -- Convert to tri a j k t form via (tri_perm_kt).symm (going from j-t-k order to j-k-t).
    have e : ∀ A B C, tri a j t k A B C = tri a j k t A C B := by
      intro A B C
      rw [tri_perm_kt a j k t hkt]
    rw [e x r w, e z p w] at hw
    rw [e x r c, e z p c]
    -- hw : weakPref (tri a j k t x w r) (tri a j k t z w p).  In K-diag terms
    -- (signature: (u,u') diff, v fixed, (c,c') diff): u=x, u'=z, v=w, c=r, c'=p.
    -- Inequalities: u≠u' = x≠z = hxz; c≠c' = r≠p = hrp.
    -- Output of K-diag: weakPref (tri a j k t x w' r) (tri a j k t z w' p) where
    -- w' is the new common k-value.  We want the goal's profile shape:
    -- tri a j k t x c r vs tri a j k t z c p.  So w' := c.
    exact hK a x z w c r p hxz hrp hw
  · -- T-diag with (k,t) swapped → K-diag.
    intro hT a u u' v v' c c' huu hcc hw
    -- Profile shape in the goal: tri a j k t _ _ _.
    -- Convert to tri a j t k form via tri_perm_kt directly.
    rw [tri_perm_kt a j k t hkt, tri_perm_kt a j k t hkt] at hw
    rw [tri_perm_kt a j k t hkt, tri_perm_kt a j k t hkt]
    -- After rewriting:
    --   hw : weakPref (tri a j t k u c v) (tri a j t k u' c' v).
    --   goal: weakPref (tri a j t k u c v') (tri a j t k u' c' v').
    -- T-diag P j t k signature: profile shape tri a j t k _ _ _, with the
    -- third (k-)slot being the shift parameter.
    -- T-diag premise: weakPref (tri a j t k x r w) (tri a j t k z p w);
    -- T-diag conclusion: weakPref (tri a j t k x r c) (tri a j t k z p c);
    -- with x ≠ z, r ≠ p (the first two slots differ).
    -- Match: x=u, z=u', r=c, p=c', w=v (the common k-slot value), c (output)=v'.
    -- Inequalities: x≠z = u≠u' = huu; r≠p = c≠c' = hcc.
    exact hT a u u' c' c v v' huu hcc hw

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-permutation audit -/

#print axioms WakkerInfra.ProductPref.tri_perm_jk
#print axioms WakkerInfra.ProductPref.tri_perm_kt
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_iff_tBlock_perm
