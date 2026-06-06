/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 final piece: the irreducible diagonal Thomsen residue

After `OptionB_BlockFromA1.lean` discharged the *single-coordinate-difference*
parts of each KLST block-independence condition from A1
(`CoordinateOrderIndependent`), this file completes the case-split decomposition
and **precisely isolates the irreducible Thomsen residue**:

* Adds the symmetric single-coord-diff cases each block condition has
  (every block has two: one where each block-coordinate is the equal one).
* Defines the **diagonal residue** of each block condition (the case where both
  block coordinates differ between the compared profiles — the genuine `n ≥ 3`
  Thomsen content).
* Proves the **decomposition theorems**: each full block condition equals the
  union of its (A1-derivable) single-coord-diff parts plus the diagonal residue.
* Proves necessity of the diagonal residues.
* **Capstone:** `CrossPairCancellationData` from A1 on every coordinate plus the
  three diagonal residues — the sharpest possible statement of what is open.

This is real progress: it factors the previously-named
`CrossPairCancellationData` residue into a **strictly smaller, sharper named
piece**, with everything around it discharged from A1 by foundational-only proofs.

This file imports `OptionB_BlockFromA1` (for the `x = z` / `u = u'` /  `v₁ = v₂`
restricted parts and the `tri_eq_update_*` helpers) and `OptionB_C1aKLSTCapstone`
(for the necessity theorems and the cross-pair assembly), and is **not** in the
umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_BlockFromA1
import WakkerDebreuKoopmans.OptionB_C1aKLSTCapstone

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

/-! ## §A.  The complementary single-coord-diff restricted forms (from A1) -/

/-- **`TBlockWeakIndependent` (restricted to `r = p`) from A1 on `j`.**

When the two profiles differ only in coordinate `j` (common `k`-value `r`), the
`t`-block comparison is the single-coordinate `j`-comparison; shifting the common
`t`-value `w → c` is a background change A1 on `j` absorbs.  Audit
`[propext, Quot.sound]`. -/
theorem tBlockWeakIndependentRestrictedJ_of_a1
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (a : Profile X) (x z : X j) (r : X k) (w c : X t)
    (hw : P.weakPref (tri a j k t x r w) (tri a j k t z r w)) :
    P.weakPref (tri a j k t x r c) (tri a j k t z r c) := by
  rw [tri_eq_update_j a hjk hjt, tri_eq_update_j a hjk hjt] at hw
  rw [tri_eq_update_j a hjk hjt, tri_eq_update_j a hjk hjt]
  exact hA1j (Function.update (Function.update a k r) t w)
             (Function.update (Function.update a k r) t c) x z hw

/-- **`KBlockWeakIndependent` (restricted to `c = c'`) from A1 on `j`.**

When the two profiles differ only in coordinate `j` (common `t`-value `c`), the
`k`-block comparison is the single-coordinate `j`-comparison; shifting the common
`k`-value `v → v'` is a background change A1 on `j` absorbs.  Audit
`[propext, Quot.sound]`. -/
theorem kBlockWeakIndependentRestrictedC_of_a1
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (a : Profile X) (u u' : X j) (v v' : X k) (c : X t)
    (hw : P.weakPref (tri a j k t u v c) (tri a j k t u' v c)) :
    P.weakPref (tri a j k t u v' c) (tri a j k t u' v' c) := by
  rw [tri_eq_update_j a hjk hjt, tri_eq_update_j a hjk hjt] at hw
  rw [tri_eq_update_j a hjk hjt, tri_eq_update_j a hjk hjt]
  exact hA1j (Function.update (Function.update a k v) t c)
             (Function.update (Function.update a k v') t c) u u' hw

/-- **`JBlockWeakIndependent` (restricted to `c₁ = c₂`) from A1 on `k`.**

When the two profiles differ only in coordinate `k` (common `t`-value `c`), the
`j`-block comparison is the single-coordinate `k`-comparison; shifting the common
`j`-value `u → u'` is a background change A1 on `k` absorbs.  Audit
`[propext, Quot.sound]`. -/
theorem jBlockWeakIndependentRestrictedC_of_a1
    {j k t : ι} (hkt : k ≠ t)
    (hA1k : CoordinateOrderIndependent P k)
    (a : Profile X) (u u' : X j) (v₁ v₂ : X k) (c : X t)
    (hw : P.weakPref (tri a j k t u v₁ c) (tri a j k t u v₂ c)) :
    P.weakPref (tri a j k t u' v₁ c) (tri a j k t u' v₂ c) := by
  rw [tri_eq_update_k a hkt, tri_eq_update_k a hkt] at hw
  rw [tri_eq_update_k a hkt, tri_eq_update_k a hkt]
  exact hA1k (Function.update (Function.update a j u) t c)
             (Function.update (Function.update a j u') t c) v₁ v₂ hw

/-! ## §B.  The diagonal residues (the irreducible Thomsen content) -/

/-- **`t`-block diagonal residue.**  The two-coordinate-difference (`x ≠ z` AND
`r ≠ p`) part of `TBlockWeakIndependent`: shifting the common `t`-value preserves
`≽` between two profiles that differ in **both** `j` and `k`.  This is the
genuine `n ≥ 3` Thomsen content the §IV.5 measuring-stick argument supplies. -/
def TBlockDiagonalResidue (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (x z : X j) (p r : X k) (w c : X t),
    x ≠ z → r ≠ p →
    P.weakPref (tri a j k t x r w) (tri a j k t z p w) →
    P.weakPref (tri a j k t x r c) (tri a j k t z p c)

/-- **`k`-block diagonal residue.**  The two-coordinate-difference (`u ≠ u'` AND
`c ≠ c'`) part of `KBlockWeakIndependent`. -/
def KBlockDiagonalResidue (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (u u' : X j) (v v' : X k) (c c' : X t),
    u ≠ u' → c ≠ c' →
    P.weakPref (tri a j k t u v c) (tri a j k t u' v c') →
    P.weakPref (tri a j k t u v' c) (tri a j k t u' v' c')

/-- **`j`-block diagonal residue.**  The two-coordinate-difference (`v₁ ≠ v₂` AND
`c₁ ≠ c₂`) part of `JBlockWeakIndependent`. -/
def JBlockDiagonalResidue (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (u u' : X j) (v₁ v₂ : X k) (c₁ c₂ : X t),
    v₁ ≠ v₂ → c₁ ≠ c₂ →
    P.weakPref (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂) →
    P.weakPref (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂)

/-! ## §C.  The decomposition theorems (full block from restricted + diagonal) -/

/-- **R1.1 decomposition: `TBlockWeakIndependent` from A1 + diagonal residue.**

The full `t`-block independence equals the union of its three case-split parts:
* `x = z` restriction (from A1 on `k`);
* `r = p` restriction (from A1 on `j`);
* `x ≠ z ∧ r ≠ p` diagonal residue (the irreducible §IV.5 Thomsen content).
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockWeakIndependent_of_decomposition
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hDiag : TBlockDiagonalResidue P j k t) :
    TBlockWeakIndependent P j k t := by
  intro a x z p r w c hw
  rcases Classical.em (x = z) with hxz | hxz
  · subst hxz
    exact tBlockWeakIndependentRestricted_of_a1 hkt hA1k a x p r w c hw
  · rcases Classical.em (r = p) with hrp | hrp
    · subst hrp
      exact tBlockWeakIndependentRestrictedJ_of_a1 hjk hjt hA1j a x z r w c hw
    · exact hDiag a x z p r w c hxz hrp hw

/-- **R1.1 decomposition: `KBlockWeakIndependent` from A1 + diagonal residue.** -/
theorem kBlockWeakIndependent_of_decomposition
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1t : CoordinateOrderIndependent P t)
    (hDiag : KBlockDiagonalResidue P j k t) :
    KBlockWeakIndependent P j k t := by
  intro a u u' v v' c c' hw
  rcases Classical.em (u = u') with huu | huu
  · subst huu
    exact kBlockWeakIndependentRestricted_of_a1 hkt hA1t a u v v' c c' hw
  · rcases Classical.em (c = c') with hcc | hcc
    · subst hcc
      exact kBlockWeakIndependentRestrictedC_of_a1 hjk hjt hA1j a u u' v v' c hw
    · exact hDiag a u u' v v' c c' huu hcc hw

/-- **R1.1 decomposition: `JBlockWeakIndependent` from A1 + diagonal residue.** -/
theorem jBlockWeakIndependent_of_decomposition
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (hDiag : JBlockDiagonalResidue P j k t) :
    JBlockWeakIndependent P j k t := by
  intro a u u' v₁ v₂ c₁ c₂ hw
  rcases Classical.em (v₁ = v₂) with hvv | hvv
  · subst hvv
    exact jBlockWeakIndependentRestricted_of_a1 hjk hjt hA1t a u u' v₁ c₁ c₂ hw
  · rcases Classical.em (c₁ = c₂) with hcc | hcc
    · subst hcc
      exact jBlockWeakIndependentRestrictedC_of_a1 hkt hA1k a u u' v₁ v₂ c₁ hw
    · exact hDiag a u u' v₁ v₂ c₁ c₂ hvv hcc hw

/-! ## §D.  Necessity of the diagonal residues -/

/-- **Necessity of the `t`-block diagonal residue.**

Every additive representation satisfies it (specialization of
`tBlockWeakIndependent_of_additiveRep`).  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem tBlockDiagonalResidue_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    TBlockDiagonalResidue P j k t := by
  intro a x z p r w c _ _ hw
  exact tBlockWeakIndependent_of_additiveRep R hjk hjt hkt a x z p r w c hw

/-- **Necessity of the `k`-block diagonal residue.** -/
theorem kBlockDiagonalResidue_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    KBlockDiagonalResidue P j k t := by
  intro a u u' v v' c c' _ _ hw
  exact kBlockWeakIndependent_of_additiveRep R hjk hjt hkt a u u' v v' c c' hw

/-- **Necessity of the `j`-block diagonal residue.** -/
theorem jBlockDiagonalResidue_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    JBlockDiagonalResidue P j k t := by
  intro a u u' v₁ v₂ c₁ c₂ _ _ hw
  exact jBlockWeakIndependent_of_additiveRep R hjk hjt hkt a u u' v₁ v₂ c₁ c₂ hw

/-! ## §E.  Final-piece capstone:
       `CrossPairCancellationData` from A1 + the three diagonal residues -/

/-- **R1.1 final-piece capstone: `CrossPairCancellationData` from A1 on every
coordinate plus the three diagonal residues.**

The sharpest possible statement of R1.1's open content: with single-coordinate
A1 on every coordinate (a structural input) plus the three diagonal residues
(`TBlockDiagonalResidue`, `KBlockDiagonalResidue`, `JBlockDiagonalResidue` —
each proved necessary, each the genuine two-coordinate-difference Thomsen
content), `CrossPairCancellationData P j k t` follows.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem crossPairCancellationData_of_a1_and_diagonalResidues
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (hTDiag : TBlockDiagonalResidue P j k t)
    (hKDiag : KBlockDiagonalResidue P j k t)
    (hJDiag : JBlockDiagonalResidue P j k t) :
    CrossPairCancellationData P j k t :=
  crossPairCancellationData_of_blockIndependence
    (tBlockWeakIndependent_of_decomposition hjk hjt hkt hA1j hA1k hTDiag)
    (kBlockWeakIndependent_of_decomposition hjk hjt hkt hA1j hA1t hKDiag)
    (jBlockWeakIndependent_of_decomposition hjk hjt hkt hA1k hA1t hJDiag)

/-- **Sanity capstone: under a representation, A1 holds on every coordinate
(theorem-backed) and the three diagonal residues hold (necessity), so the
final-piece route recovers `CrossPairCancellationData`.**

Audit foundational-only.  Confirms the decomposition is exactly the right
strength. -/
theorem crossPairCancellationData_of_additiveRep_via_diagonalResidues
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    CrossPairCancellationData P j k t :=
  crossPairCancellationData_of_a1_and_diagonalResidues
    hjk hjt hkt
    (coordinateOrderIndependent_of_additiveRep R j)
    (coordinateOrderIndependent_of_additiveRep R k)
    (coordinateOrderIndependent_of_additiveRep R t)
    (tBlockDiagonalResidue_of_additiveRep R hjk hjt hkt)
    (kBlockDiagonalResidue_of_additiveRep R hjk hjt hkt)
    (jBlockDiagonalResidue_of_additiveRep R hjk hjt hkt)

end ProductPref
end WakkerInfra

/-! ## R1.1 final-piece audit -/

#print axioms WakkerInfra.ProductPref.tBlockWeakIndependentRestrictedJ_of_a1
#print axioms WakkerInfra.ProductPref.kBlockWeakIndependentRestrictedC_of_a1
#print axioms WakkerInfra.ProductPref.jBlockWeakIndependentRestrictedC_of_a1
#print axioms WakkerInfra.ProductPref.tBlockWeakIndependent_of_decomposition
#print axioms WakkerInfra.ProductPref.kBlockWeakIndependent_of_decomposition
#print axioms WakkerInfra.ProductPref.jBlockWeakIndependent_of_decomposition
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_additiveRep
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_of_additiveRep
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_of_additiveRep
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_a1_and_diagonalResidues
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_additiveRep_via_diagonalResidues
