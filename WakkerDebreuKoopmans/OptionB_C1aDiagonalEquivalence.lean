/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: complete pairwise equivalence of the three diagonal residues
  under coordinate-role permutation

This file proves the **complete pairwise equivalence** of the three diagonal
Thomsen residues (R1.1's final-piece content) under coordinate-role
permutations.  Earlier files proved:
* `kBlockDiagonalResidue P j k t ↔ TBlockDiagonalResidue P j t k`
  (`OptionB_C1aDiagonalPermutation.lean`, K-diag is T-diag with k↔t roles
  swapped);
* `jBlockDiagonalResidue P j k t ↔ TBlockDiagonalResidue P t k j`
  (`OptionB_C1aDiagonalPermutationJ.lean`, J-diag is T-diag with j↔t roles
  swapped).

This file completes the pairwise picture.

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_iff_kBlock_perm` — the inverse: `T-diag P j k t ↔
  K-diag P j t k` (T-diag is K-diag with k↔t roles swapped).
* `tBlockDiagonalResidue_iff_jBlock_perm` — the inverse: `T-diag P j k t ↔
  J-diag P t k j` (T-diag is J-diag with j↔t roles swapped).
* `kBlockDiagonalResidue_iff_jBlock_perm` — the K↔J pairwise equivalence:
  `K-diag P j k t ↔ J-diag P k j t` (K-diag is J-diag with j↔k roles swapped, plus
  a permutation of the third).

These complete the symmetric `S_3`-equivariance picture: the three diagonals
form an orbit under the coordinate-role permutation group, and every diagonal is
the same Thomsen statement up to relabeling.

This file imports the prior diagonal-permutation files and is **not** in the
umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalPermutation
import WakkerDebreuKoopmans.OptionB_C1aDiagonalPermutationJ

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

/-- **`T-diag P j k t ↔ K-diag P j t k` (the inverse permutation).**

Direct from `kBlockDiagonalResidue_iff_tBlock_perm`: that lemma gives
`K-diag P j' k' t' ↔ T-diag P j' t' k'`.  Setting `(j', k', t') = (j, t, k)` gives
`K-diag P j t k ↔ T-diag P j k t`, i.e. `T-diag P j k t ↔ K-diag P j t k`.  Audit
`[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_iff_kBlock_perm
    {j k t : ι} (hkt : k ≠ t) :
    TBlockDiagonalResidue P j k t ↔ KBlockDiagonalResidue P j t k := by
  have h := kBlockDiagonalResidue_iff_tBlock_perm (P := P) (j := j) (k := t) (t := k)
              (Ne.symm hkt)
  -- h : K-diag P j t k ↔ T-diag P j k t.
  exact h.symm

/-- **`T-diag P j k t ↔ J-diag P t k j`.**

Direct from `jBlockDiagonalResidue_iff_tBlock_perm` with arguments
`(j', k', t') = (t, k, j)`: that lemma gives `J-diag P t k j ↔ T-diag P j k t`,
i.e. the desired equivalence flipped.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_iff_jBlock_perm
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    TBlockDiagonalResidue P j k t ↔ JBlockDiagonalResidue P t k j := by
  have h := jBlockDiagonalResidue_iff_tBlock_perm (P := P) (j := t) (k := k) (t := j)
              (Ne.symm hkt) (Ne.symm hjt) (Ne.symm hjk)
  -- h : J-diag P t k j ↔ T-diag P j k t.
  exact h.symm

/-- **`K-diag P j k t ↔ J-diag P k t j`** (composing the two equivalences).

Chain: K-diag P j k t ↔ T-diag P j t k (by `kBlockDiagonalResidue_iff_tBlock_perm`)
↔ J-diag P k t j (by `tBlockDiagonalResidue_iff_jBlock_perm` applied to T-diag's
coordinate triple `(j, t, k)`).  This shows K and J are also pairwise equivalent
under coordinate-role permutation.  Audit `[propext, Quot.sound]`. -/
theorem kBlockDiagonalResidue_iff_jBlock_perm
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    KBlockDiagonalResidue P j k t ↔ JBlockDiagonalResidue P k t j := by
  -- Step 1: K-diag P j k t ↔ T-diag P j t k.
  have h1 : KBlockDiagonalResidue P j k t ↔ TBlockDiagonalResidue P j t k :=
    kBlockDiagonalResidue_iff_tBlock_perm hkt
  -- Step 2: T-diag P j t k ↔ J-diag P k t j.  Apply tBlockDiagonalResidue_iff_jBlock_perm
  -- to coords (j', k', t') = (j, t, k); needs (j ≠ t) = hjt, (j ≠ k) = hjk, (t ≠ k) = Ne.symm hkt.
  have h2 : TBlockDiagonalResidue P j t k ↔ JBlockDiagonalResidue P k t j :=
    tBlockDiagonalResidue_iff_jBlock_perm hjt hjk (Ne.symm hkt)
  exact h1.trans h2

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-equivalence audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_iff_kBlock_perm
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_iff_jBlock_perm
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_iff_jBlock_perm
