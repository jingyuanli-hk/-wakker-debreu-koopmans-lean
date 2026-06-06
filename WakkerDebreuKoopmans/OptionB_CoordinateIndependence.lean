/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-CI: the coordinate-independence / hexagon condition

This file executes work package **WP-CI** of
`OptionB_UnconditionalConstructionRoadmap.md`, following the §5 gate result.

## Background from the §5 gate

`OptionB_C1aSoundnessGate.lean` proved the formalized
`WakkerInfra.ProductPref.TradeoffConsistency` is *exactly* single-coordinate
**indifference** base-independence (`tradeoffConsistency_iff_indiffBaseIndependent`).
That is strictly weaker than what the additive representation needs.

## What this file establishes (all machine-checked, sorry-free)

Two genuine structural conditions, with their soundness (necessity) and their
relationship to the formalized axiom:

1. **`DoubleCancellation P j k`** — the standard additive-conjoint *Thomsen /
   hexagon* double-cancellation on a coordinate pair `{j,k}`.
   * `doubleCancellation_of_additiveRep` : **necessary** — every `AdditiveRep`
     satisfies it.  So assuming/using it adds no false content.

2. **`CoordinateOrderIndependent P i`** — full coordinate independence: the
   *weak-preference* order `≽_i` is background-independent (Krantz–Luce–Suppes–
   Tversky "independence").  This is **definitionally identical** to the
   Phase-71 A1 field `RawAxiomDischargersIVT.CoordinateWeakSeparable`, which the
   artifact already carries as a structural input.
   * `coordinateOrderIndependent_of_additiveRep` : **necessary**.
   * `indiffBaseIndependent_of_coordinateOrderIndependent` : full coordinate
     independence **implies** the formalized indiff-only `TradeoffConsistency`
     content — i.e. A1 is the correct strengthening, sitting *above* the
     formalized axiom in the hierarchy.

## The honest determination (revising the §5 first-pass framing)

The §5 gate's *equivalence theorem* is correct.  But the right conclusion is
**not** "add a brand-new axiom":

* The genuine coordinate-independence input is `CoordinateOrderIndependent`
  (= A1 `CoordinateWeakSeparable`), which is **already a structural field** of the
  artifact's topology bundle (Phase 71, where it was correctly identified as
  *not* derivable from topology and made explicit).
* For `n ≥ 3` essential coordinates, coordinate independence of every coordinate
  (= A1 for all `i`) together with restricted solvability, the Archimedean axiom,
  and per-coordinate continuity/connectedness is sufficient for an additive
  representation (Debreu 1960; KLST 1971, Theorem 6.2), and the hexagon /
  `DoubleCancellation` is **derivable** from it using the third coordinate as a
  standard-sequence measuring stick.  That derivation is exactly work package
  **WP-C1.a**; it is the hard `n ≥ 3` standard-sequence argument, not a new
  primitive.
* The repository's existing no-go theorems (`additiveRealBool`, `totalNatBool`)
  are all `n = 2` (`Bool`-indexed) models, i.e. the genuinely-harder Thomsen case
  where independence alone is insufficient.  They do **not** refute the `n ≥ 3`
  route, so `DoubleCancellation` must not be added as a primitive — it is a
  theorem-to-be (WP-C1.a) once A1 is in hand.

**Consequence for the papers.**  Option B's honest headline is "first
machine-checked proof of Wakker IV.2.7 from Wakker's structural axioms" where the
axiom set is understood to include **coordinate independence** (the A1 field,
= KLST independence) alongside weak order, restricted solvability, the
Archimedean axiom, essentiality, and per-coordinate connectedness/continuity.
This is exactly Wakker/KLST's own hypothesis set.  No content is hidden: A1 is an
explicit, necessary (`coordinateOrderIndependent_of_additiveRep`) structural
field, and `DoubleCancellation` is a necessary consequence to be derived, not
assumed.

This file imports only `Core` and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.Core
import WakkerDebreuKoopmans.OptionB_C1aSoundnessGate

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open WakkerDebreuKoopmans
open Function Finset

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-! ## §A.  Score-splitting helpers for an additive representation -/

/-- Score of a single-coordinate update splits as the coordinate term plus a
background remainder. -/
lemma score_update1 (R : AdditiveRep P) (a : Profile X) (i : ι) (v : X i) :
    (∑ l, R.V l (Function.update a i v l))
      = R.V i v + ∑ l ∈ Finset.univ.erase i, R.V l (a l) := by
  rw [← Finset.add_sum_erase _ (fun l => R.V l (Function.update a i v l))
        (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

/-- Score of a two-coordinate update splits as the two coordinate terms plus a
background remainder that does not depend on the two updated values. -/
lemma score_update2 (R : AdditiveRep P) (a : Profile X) {j k : ι} (hjk : j ≠ k)
    (u : X j) (t : X k) :
    (∑ l, R.V l (Function.update (Function.update a j u) k t l))
      = R.V j u + R.V k t + ∑ l ∈ (Finset.univ.erase j).erase k, R.V l (a l) := by
  have hkj : k ∈ Finset.univ.erase j :=
    Finset.mem_erase.mpr ⟨fun h => hjk h.symm, Finset.mem_univ k⟩
  rw [← Finset.add_sum_erase _
        (fun l => R.V l (Function.update (Function.update a j u) k t l))
        (Finset.mem_univ j),
      ← Finset.add_sum_erase _
        (fun l => R.V l (Function.update (Function.update a j u) k t l)) hkj]
  rw [show (Function.update (Function.update a j u) k t) j = u by
        rw [Function.update_of_ne hjk]; simp,
      show (Function.update (Function.update a j u) k t) k = t by simp]
  have hrest :
      (∑ l ∈ (Finset.univ.erase j).erase k,
          R.V l (Function.update (Function.update a j u) k t l))
        = ∑ l ∈ (Finset.univ.erase j).erase k, R.V l (a l) := by
    apply Finset.sum_congr rfl
    intro l hl
    have hlk : l ≠ k := Finset.ne_of_mem_erase hl
    have hlj : l ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
    rw [Function.update_of_ne hlk, Function.update_of_ne hlj]
  rw [hrest]; ring

/-- Indifference under an additive representation is equality of additive
scores. -/
theorem indiff_iff_score (R : AdditiveRep P) {x y : Profile X} :
    P.indiff x y ↔ (∑ i, R.V i (x i)) = (∑ i, R.V i (y i)) := by
  unfold ProductPref.indiff
  rw [R.represents, R.represents]
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · intro h; exact ⟨h.ge, h.le⟩

/-- Single-coordinate preference under an additive representation is the
coordinate-utility comparison — in particular background-independent. -/
theorem coordPref_iff_V (R : AdditiveRep P) {i : ι} {a : Profile X} {v w : X i} :
    P.coordPref i a v w ↔ R.V i w ≤ R.V i v := by
  unfold ProductPref.coordPref
  rw [R.represents, score_update1 R a i w, score_update1 R a i v]
  exact add_le_add_iff_right _

/-! ## §B.  The hexagon / Thomsen double-cancellation condition -/

/-- **Double cancellation (Thomsen / hexagon condition) on a coordinate pair.**

For a common background `a` and coordinate values `x,y,z : X j`, `p,q,r : X k`:
if the `{j,k}`-profile `(x,q)` is indifferent to `(y,p)` and `(y,r)` is
indifferent to `(z,q)`, then `(x,r)` is indifferent to `(z,p)`.  This is the
standard additive-conjoint cancellation axiom needed (beyond single-coordinate
independence) for additive representation; for `n = 2` it is genuinely extra, for
`n ≥ 3` it is derivable from coordinate independence via a third coordinate. -/
def DoubleCancellation (P : ProductPref X) (j k : ι) : Prop :=
  ∀ (a : Profile X) (x y z : X j) (p q r : X k),
    P.indiff (Function.update (Function.update a j x) k q)
             (Function.update (Function.update a j y) k p) →
    P.indiff (Function.update (Function.update a j y) k r)
             (Function.update (Function.update a j z) k q) →
    P.indiff (Function.update (Function.update a j x) k r)
             (Function.update (Function.update a j z) k p)

/-- **Necessity of double cancellation.**  Every additive representation
satisfies the hexagon condition.  (Adding/using it is therefore sound.) -/
theorem doubleCancellation_of_additiveRep (R : AdditiveRep P) {j k : ι}
    (hjk : j ≠ k) : DoubleCancellation P j k := by
  intro a x y z p q r h1 h2
  rw [indiff_iff_score R] at h1 h2 ⊢
  simp only [score_update2 R a hjk] at h1 h2 ⊢
  linarith

/-! ## §C.  Full coordinate independence and the hierarchy -/

/-- **Full coordinate independence** (KLST "independence").

The *weak-preference* order on coordinate `i` is background-independent: if
`v ≽_i w` at one background, then at every background.  This is definitionally
the Phase-71 A1 field `RawAxiomDischargersIVT.CoordinateWeakSeparable P i`,
already carried as a structural input by the artifact's topology bundle. -/
def CoordinateOrderIndependent (P : ProductPref X) (i : ι) : Prop :=
  ∀ (a b : Profile X) (v w : X i), P.coordPref i a v w → P.coordPref i b v w

/-- **Necessity of coordinate independence.**  Every additive representation
satisfies full coordinate independence. -/
theorem coordinateOrderIndependent_of_additiveRep (R : AdditiveRep P) (i : ι) :
    CoordinateOrderIndependent P i := by
  intro a b v w h
  rw [coordPref_iff_V R] at h ⊢
  exact h

/-- **Hierarchy: full coordinate independence implies the formalized indiff-only
condition.**

`CoordinateOrderIndependent` (for every coordinate) implies the §5-gate predicate
`IndiffBaseIndependent` (imported from `OptionB_C1aSoundnessGate`) — i.e. the A1
field is strictly above the formalized `TradeoffConsistency` in strength.  This
pins down *which* structural input Option B genuinely needs: A1, which the
artifact already has. -/
theorem indiffBaseIndependent_of_coordinateOrderIndependent
    (hci : ∀ i, CoordinateOrderIndependent P i) :
    IndiffBaseIndependent P := by
  intro j base base' v w h
  -- indiff = coordPref both directions; transport each direction by hci.
  obtain ⟨hvw, hwv⟩ := h
  exact ⟨hci j base base' v w hvw, hci j base base' w v hwv⟩

end ProductPref
end WakkerInfra

/-! ## WP-CI audit

All necessity and hierarchy results are sorry-free and foundational-only. -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep
#print axioms WakkerInfra.ProductPref.coordinateOrderIndependent_of_additiveRep
#print axioms WakkerInfra.ProductPref.indiffBaseIndependent_of_coordinateOrderIndependent
