/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 unified capstone: `CrossPairCancellationData` from A1 + a
  single Thomsen residue at three coordinate triples

This file proves the **unified capstone** for R1.1, consolidating the diagonal-
permutation reductions: the entire `CrossPairCancellationData = KzTransfer ∧
StripTransfer` follows from
* single-coordinate independence A1 on each of `j`, `k`, `t`, **plus**
* a single Thomsen-type residue `TBlockDiagonalResidue` instantiated at the
  three permuted coordinate triples `(j,k,t)`, `(j,t,k)`, `(t,k,j)`.

This is the sharpest possible statement of R1.1's open content: **one** Thomsen
statement applied at three role-assignments, with everything else discharged from
A1 by foundational-only proofs.

## What this file delivers (machine-checked, sound)

* `crossPairCancellationData_of_a1_and_oneThomsenResidue` — the unified capstone:
  `CrossPairCancellationData P j k t` from A1 on `{j,k,t}` plus `T-diag` at the
  three permuted triples.
* `crossPairCancellationData_of_additiveRep_via_oneThomsen` — sanity capstone:
  under a representation, A1 holds (theorem-backed), `T-diag` holds at every
  triple (necessity), so the unified capstone recovers `CrossPairCancellationData`.

This file imports the prior diagonal-residue capstone and the two permutation
files, and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalResidue
import WakkerDebreuKoopmans.OptionB_C1aDiagonalPermutation
import WakkerDebreuKoopmans.OptionB_C1aDiagonalPermutationJ

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open WakkerDebreuKoopmans

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-- **R1.1 unified capstone: `CrossPairCancellationData` from A1 + one Thomsen
residue at three coordinate triples.**

`CrossPairCancellationData P j k t` follows from:
* `CoordinateOrderIndependent P j`, `CoordinateOrderIndependent P k`,
  `CoordinateOrderIndependent P t` (A1 on each coordinate; the structural input);
* `TBlockDiagonalResidue P j k t` (the {j,k}-differ shift-t Thomsen statement);
* `TBlockDiagonalResidue P j t k` (the {j,t}-differ shift-k Thomsen statement,
  K-diag's permutation-equivalent);
* `TBlockDiagonalResidue P t k j` (the {k,t}-differ shift-j Thomsen statement,
  J-diag's permutation-equivalent).

So R1.1's genuinely-open content is **one** Thomsen-type theorem applied to the
three role-assignments of the three coordinates.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem crossPairCancellationData_of_a1_and_oneThomsenResidue
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (hTjkt : TBlockDiagonalResidue P j k t)
    (hTjtk : TBlockDiagonalResidue P j t k)
    (hTtkj : TBlockDiagonalResidue P t k j) :
    CrossPairCancellationData P j k t := by
  -- Convert hTjtk and hTtkj to K-diag and J-diag via the permutation equivalences.
  have hKDiag : KBlockDiagonalResidue P j k t :=
    (kBlockDiagonalResidue_iff_tBlock_perm hkt).mpr hTjtk
  have hJDiag : JBlockDiagonalResidue P j k t :=
    (jBlockDiagonalResidue_iff_tBlock_perm hjk hjt hkt).mpr hTtkj
  -- Apply the prior diagonal-residue capstone.
  exact crossPairCancellationData_of_a1_and_diagonalResidues
    hjk hjt hkt hA1j hA1k hA1t hTjkt hKDiag hJDiag

/-- **Sanity capstone: under a representation, the unified route recovers
`CrossPairCancellationData`.**

Each `T-diag` is necessary (`tBlockDiagonalResidue_of_additiveRep` instantiated at
the three coordinate triples), and A1 is theorem-backed
(`coordinateOrderIndependent_of_additiveRep`).  So the unified-Thomsen route
recovers the cross-pair data — confirming the strength is exactly right.  Audit
foundational-only. -/
theorem crossPairCancellationData_of_additiveRep_via_oneThomsen
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    CrossPairCancellationData P j k t :=
  crossPairCancellationData_of_a1_and_oneThomsenResidue
    hjk hjt hkt
    (coordinateOrderIndependent_of_additiveRep R j)
    (coordinateOrderIndependent_of_additiveRep R k)
    (coordinateOrderIndependent_of_additiveRep R t)
    (tBlockDiagonalResidue_of_additiveRep R hjk hjt hkt)
    -- T-diag P j t k: needs j-of-T ≠ k-of-T = j ≠ t = hjt,
    --                       j-of-T ≠ t-of-T = j ≠ k = hjk,
    --                       k-of-T ≠ t-of-T = t ≠ k = Ne.symm hkt.
    (tBlockDiagonalResidue_of_additiveRep R hjt hjk (Ne.symm hkt))
    -- T-diag P t k j: needs j-of-T ≠ k-of-T = t ≠ k = Ne.symm hkt,
    --                       j-of-T ≠ t-of-T = t ≠ j = Ne.symm hjt,
    --                       k-of-T ≠ t-of-T = k ≠ j = Ne.symm hjk.
    (tBlockDiagonalResidue_of_additiveRep R (Ne.symm hkt) (Ne.symm hjt) (Ne.symm hjk))

end ProductPref
end WakkerInfra

/-! ## R1.1 unified capstone audit -/

#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_a1_and_oneThomsenResidue
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_additiveRep_via_oneThomsen
