/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — G4.a: construct the grid index-sum slice representation `S`

> **STATUS: `sorry`-free forward brick on the §IV.5 Link-B construction (G4.a).**
> Not in the umbrella import.

This file executes **G4.a** of `OptionB_SectionIV5GridConstructionRoadmap.md`: the
first brick of Link B (hexagon → per-slice additive representation).  It **constructs**
the grid index-sum function `S` and proves the order-tracking representation
`GridAdditiveSliceRep` (`RawAxiomDischargersHexagon`) — the §IV.5 Step-4 calibration
output restricted to the grid — from:

* the **grid normalization witness** `PairwiseGridNormalizationWitness` (integer-grid
  utilities `Vⱼ, Vₖ` exist on the two standard-sequence grids — theorem-backed from
  injective grids);
* the **grid Thomsen step** (G1, here in `ConcreteDiagonalStep` form), giving the
  equal-index-sum half of order-tracking;
* a single **grid strict-monotonicity** primitive `GridStepStrictMono` (one consecutive
  grid step is *strictly* preferred) — necessary under a rep, the genuine order half.

## Why *strict* monotonicity (an honest no-go for the weak form)

Order-tracking `weakPref (g n m) (g n' m') ↔ S(g n' m') ≤ S(g n m)` cannot follow from
*weak* step monotonicity: total indifference (`weakPref` everywhere) satisfies weak
monotonicity and equal-sum indifference, yet falsifies order-tracking (it makes
`weakPref` hold even when the index sum is larger).  So the genuine order primitive is
**strict** single-step preference — which is exactly what a representation with a
non-degenerate (strictly increasing) grid supplies.

## The construction

`S p := Vⱼ (p j) + Vₖ (p k)`.  On a grid profile `g n m`, the normalization witness
gives `S (g n m) = n + m` (property ii — free).  Order-tracking (property i) reduces,
via the equal-sum indifference `g n m ∼ g (n+m) 0` (G1), to the pure `j`-axis order at
`m = 0`, where strict monotone padding gives `weakPref (g a 0) (g b 0) ↔ b ≤ a`.

## What this file delivers (all machine-checked, no `sorry`)

* `gridIndexSumScore` + `gridIndexSumScore_eq_indexSum` — `S` and its index-sum value
  on grid profiles (property ii).
* `score_concreteGrid` — the additive score of a grid profile under a rep.
* `GridStepStrictMono` + `gridStepStrictMono_of_additiveRep` — the strict order
  primitive and its soundness gate.
* `concreteDiagonalStep_of_additiveRep_grid` — soundness gate for the G1 step.
* `gridAdditiveSliceRep_of_data` — **the G4.a construction** (general form): the slice
  rep from {`S`-index-sum + concrete diagonal step (G1) + strict monotonicity}.
* `gridAdditiveSliceRep_of_normalization_diagonal_monotone` — specialized to
  `S = gridIndexSumScore` with the normalization witness.
* `gridAdditiveSliceRep_of_additiveRep` — soundness capstone: a representation with a
  strictly-increasing, equal-spaced grid supplies all ingredients, hence the slice rep.

## Honest scope

G4.a constructs `S` and the grid representation from the §IV.5 Step-4 data.  The
normalization witness is theorem-backed (injective grids); the diagonal step is G1
(reduced to the block / cross-pair crux); the strict-monotone primitive is necessary
under a rep.  So Link-B's first brick is complete modulo the same G1 crux.  G4.b
(continuous extension off the grid via the G3 mesh density) and G4.c (assemble the C1
frontier field, already mechanized) follow.

Imports `RawAxiomDischargersHexagon`, `Certificates`, `OptionB_CoordinateIndependence`.
Not in the umbrella import.
-/

import WakkerDebreuKoopmans.RawAxiomDischargersHexagon
import WakkerDebreuKoopmans.Certificates
import WakkerDebreuKoopmans.OptionB_CoordinateIndependence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open WakkerInfra
open WakkerDebreuKoopmans
open WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon
open Function

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-! ## §A.  The grid index-sum score -/

/-- The grid index-sum score `S p = Vⱼ (p j) + Vₖ (p k)`. -/
def gridIndexSumScore (j k : ι) (Vⱼ : X j → ℝ) (Vₖ : X k → ℝ) : Profile X → ℝ :=
  fun p => Vⱼ (p j) + Vₖ (p k)

/-- **The index-sum score on a grid profile (PROVED).**

`gridIndexSumScore` on `concreteGrid base j k vⱼ vₖ n m` is `Vⱼ (vⱼ n) + Vₖ (vₖ m)`:
the `k`-update sets coordinate `k` (`update_self`), and the `j`-update is visible
through `update_of_ne` since `j ≠ k`.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem gridIndexSumScore_concreteGrid
    {j k : ι} (hjk : j ≠ k) (Vⱼ : X j → ℝ) (Vₖ : X k → ℝ)
    (base : Profile X) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) (n m : ℕ) :
    gridIndexSumScore j k Vⱼ Vₖ (concreteGrid base j k vⱼ vₖ n m)
      = Vⱼ (vⱼ n) + Vₖ (vₖ m) := by
  unfold gridIndexSumScore concreteGrid
  rw [Function.update_self, Function.update_of_ne hjk, Function.update_self]

/-- **The normalized index-sum score is `n + m` on a grid profile (PROVED).**

Combines `gridIndexSumScore_concreteGrid` with the normalization witness
`Vⱼ (vⱼ n) = n`, `Vₖ (vₖ m) = m`.  This is property (ii) of `GridAdditiveSliceRep`.
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridIndexSumScore_eq_indexSum
    {j k : ι} (hjk : j ≠ k)
    {σⱼ : StandardSequence P j} {σₖ : StandardSequence P k}
    {Vⱼ : X j → ℝ} {Vₖ : X k → ℝ}
    (hgrid : WakkerRoadmap.CertificateChecklist.PairwiseGridNormalizationWitness σⱼ σₖ Vⱼ Vₖ)
    (base : Profile X) (n m : ℕ) :
    gridIndexSumScore j k Vⱼ Vₖ (concreteGrid base j k σⱼ.α σₖ.α n m)
      = (n : ℝ) + (m : ℝ) := by
  rw [gridIndexSumScore_concreteGrid hjk, hgrid.1 n, hgrid.2 m]

/-! ## §B.  The additive score of a grid profile, and the order ingredients -/

/-- **The additive score of a grid profile under a representation (PROVED).**

`∑ᵢ V i (g n m i) = V j (vⱼ n) + V k (vₖ m) + (background sum off `{j,k}`)`: split the
sum at `j` then `k`; the two updates set those coordinates, the rest is the background.
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem score_concreteGrid
    (R : AdditiveRep P) {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) (n m : ℕ) :
    (∑ i, R.V i (concreteGrid base j k vⱼ vₖ n m i))
      = R.V j (vⱼ n) + R.V k (vₖ m)
        + ∑ i ∈ (Finset.univ.erase j).erase k, R.V i (base i) := by
  unfold concreteGrid
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (show k ∈ Finset.univ.erase j from
        Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩)]
  have hjv : (Function.update (Function.update base j (vⱼ n)) k (vₖ m)) j = vⱼ n := by
    rw [Function.update_of_ne hjk, Function.update_self]
  have hkv : (Function.update (Function.update base j (vⱼ n)) k (vₖ m)) k = vₖ m := by
    rw [Function.update_self]
  rw [hjv, hkv]
  have hrest : (∑ i ∈ (Finset.univ.erase j).erase k,
        R.V i (Function.update (Function.update base j (vⱼ n)) k (vₖ m) i))
      = ∑ i ∈ (Finset.univ.erase j).erase k, R.V i (base i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hij : i ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    rw [Function.update_of_ne hik, Function.update_of_ne hij]
  rw [hrest]; ring

/-- **Grid step strict monotonicity (the order-direction primitive).**

One step up either grid axis is *strictly* preferred: `g (n+1) m ≻ g n m` and
`g n (m+1) ≻ g n m`.  This fixes the direction *and* non-degeneracy of the
representation (more grid index = strictly better), which the weak form cannot (total
indifference satisfies the weak form but falsifies order-tracking). -/
def GridStepStrictMono (P : ProductPref X)
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) : Prop :=
  (∀ n m, P.strict (concreteGrid base j k vⱼ vₖ (n + 1) m)
                   (concreteGrid base j k vⱼ vₖ n m)) ∧
  (∀ n m, P.strict (concreteGrid base j k vⱼ vₖ n (m + 1))
                   (concreteGrid base j k vⱼ vₖ n m))

/-- **Soundness gate (PROVED): grid strict monotonicity under a rep with strictly
increasing grid steps.**

Under an additive representation, `g (n+1) m ≻ g n m` iff the score strictly increases,
i.e. iff `Vⱼ (vⱼ n) < Vⱼ (vⱼ (n+1))` (other coordinates cancel); likewise for `k`.  So
a grid whose `j`- and `k`-steps are utility-*strictly*-increasing is strictly monotone.
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridStepStrictMono_of_additiveRep
    (R : AdditiveRep P) {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (hjmono : ∀ n, R.V j (vⱼ n) < R.V j (vⱼ (n + 1)))
    (hkmono : ∀ m, R.V k (vₖ m) < R.V k (vₖ (m + 1))) :
    GridStepStrictMono P base j k vⱼ vₖ := by
  refine ⟨?_, ?_⟩
  · intro n m
    refine ⟨?_, ?_⟩
    · rw [R.represents, score_concreteGrid R hjk base vⱼ vₖ (n + 1) m,
          score_concreteGrid R hjk base vⱼ vₖ n m]
      have := hjmono n; linarith
    · rw [R.represents, score_concreteGrid R hjk base vⱼ vₖ (n + 1) m,
          score_concreteGrid R hjk base vⱼ vₖ n m]
      have := hjmono n; intro hle; linarith
  · intro n m
    refine ⟨?_, ?_⟩
    · rw [R.represents, score_concreteGrid R hjk base vⱼ vₖ n (m + 1),
          score_concreteGrid R hjk base vⱼ vₖ n m]
      have := hkmono m; linarith
    · rw [R.represents, score_concreteGrid R hjk base vⱼ vₖ n (m + 1),
          score_concreteGrid R hjk base vⱼ vₖ n m]
      have := hkmono m; intro hle; linarith

/-- **Soundness gate (PROVED): the concrete diagonal step under a rep.**

Under an additive representation, `g (n+1) m ∼ g n (m+1)` iff the scores are equal,
i.e. iff `Vⱼ (vⱼ (n+1)) + Vₖ (vₖ m) = Vⱼ (vⱼ n) + Vₖ (vₖ (m+1))` — the grid's own
equal-spacing calibration.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem concreteDiagonalStep_of_additiveRep_grid
    (R : AdditiveRep P) {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (hstep : ∀ n m,
      R.V j (vⱼ (n + 1)) + R.V k (vₖ m) = R.V j (vⱼ n) + R.V k (vₖ (m + 1))) :
    ConcreteDiagonalStep P base j k vⱼ vₖ := by
  intro n m
  rw [indiff_iff_score R, score_concreteGrid R hjk base vⱼ vₖ (n + 1) m,
      score_concreteGrid R hjk base vⱼ vₖ n (m + 1)]
  have := hstep n m; linarith

/-! ## §C.  The G4.a construction -/

/-- **G4.a construction (general form): the grid-additive slice representation
(PROVED).**

From {an index-sum score `S` with `S (g n m) = n + m`, the concrete diagonal step (G1,
equal-index-sum indifference), and strict grid monotonicity} the order-tracking
representation `GridAdditiveSliceRep` holds.

Order-tracking reduces to the `j`-axis at `m = 0` via the equal-sum collapse
`g n m ∼ g (n+m) 0` (G1).  There strict monotone padding gives
`weakPref (g a 0) (g b 0) ↔ b ≤ a`, and `S (g n m) = n + m` turns the index-sum order
into the `S`-comparison `GridAdditiveSliceRep` demands.  Audit `[propext, Quot.sound]`. -/
theorem gridAdditiveSliceRep_of_data
    [ProductPref.IsWeakOrder P]
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (S : Profile X → ℝ)
    (hSnorm : ∀ n m, S (concreteGrid base j k vⱼ vₖ n m) = (n : ℝ) + (m : ℝ))
    (hdiag : ConcreteDiagonalStep P base j k vⱼ vₖ)
    (hmono : GridStepStrictMono P base j k vⱼ vₖ) :
    GridAdditiveSliceRep P base j k vⱼ vₖ S := by
  obtain ⟨hmonoJ, hmonoK⟩ := hmono
  have hrefl : ∀ p : Profile X, P.weakPref p p :=
    fun p => (IsWeakOrder.complete p p).elim id id
  have hstrict_trans : ∀ x y z : Profile X, P.strict x y → P.strict y z → P.strict x z := by
    rintro x y z ⟨hxy, hnyx⟩ ⟨hyz, hnzy⟩
    exact ⟨IsWeakOrder.transitive _ _ _ hxy hyz,
           fun hzx => hnzy (IsWeakOrder.transitive _ _ _ hzx hxy)⟩
  -- equal-index-sum indifference (the G1 content)
  have heq : ∀ n m n' m' : ℕ, n + m = n' + m' →
      P.indiff (concreteGrid base j k vⱼ vₖ n m) (concreteGrid base j k vⱼ vₖ n' m') :=
    fun n m n' m' h => concreteGrid_indiff_of_eqSum P base j k vⱼ vₖ hdiag h
  -- strict `j`-axis padding at `m = 0`
  have hjstrict : ∀ e a : ℕ,
      P.strict (concreteGrid base j k vⱼ vₖ (a + e + 1) 0)
               (concreteGrid base j k vⱼ vₖ a 0) := by
    intro e
    induction e with
    | zero => intro a; simpa using hmonoJ a 0
    | succ e ih =>
      intro a
      have h1 := ih (a + 1)
      have h2 : P.strict (concreteGrid base j k vⱼ vₖ (a + 1) 0)
                         (concreteGrid base j k vⱼ vₖ a 0) := hmonoJ a 0
      have he : a + (e + 1) + 1 = (a + 1) + e + 1 := by omega
      rw [he]
      exact hstrict_trans _ _ _ h1 h2
  -- weak `j`-axis padding at `m = 0`
  have hjweak : ∀ a b : ℕ, a ≤ b →
      P.weakPref (concreteGrid base j k vⱼ vₖ b 0) (concreteGrid base j k vⱼ vₖ a 0) := by
    intro a b hab
    rcases Nat.lt_or_ge a b with h | h
    · have he : a + (b - a - 1) + 1 = b := by omega
      have hs := hjstrict (b - a - 1) a
      rw [he] at hs
      exact hs.1
    · have hab' : a = b := le_antisymm hab h
      subst hab'; exact hrefl _
  -- collapse any grid profile to the `j`-axis at `0`
  have hcollapse : ∀ n m : ℕ,
      P.indiff (concreteGrid base j k vⱼ vₖ n m)
               (concreteGrid base j k vⱼ vₖ (n + m) 0) :=
    fun n m => heq n m (n + m) 0 (by omega)
  -- the core order equivalence
  have hcore : ∀ n m n' m' : ℕ,
      P.weakPref (concreteGrid base j k vⱼ vₖ n m) (concreteGrid base j k vⱼ vₖ n' m')
        ↔ n' + m' ≤ n + m := by
    intro n m n' m'
    have hL := hcollapse n m
    have hR := hcollapse n' m'
    constructor
    · intro hpref
      have hax : P.weakPref (concreteGrid base j k vⱼ vₖ (n + m) 0)
                            (concreteGrid base j k vⱼ vₖ (n' + m') 0) :=
        IsWeakOrder.transitive _ _ _ (IsWeakOrder.transitive _ _ _ hL.2 hpref) hR.1
      by_contra hlt
      push_neg at hlt
      have he : (n + m) + (n' + m' - (n + m) - 1) + 1 = n' + m' := by omega
      have hs := hjstrict (n' + m' - (n + m) - 1) (n + m)
      rw [he] at hs
      exact hs.2 hax
    · intro hle
      have hax : P.weakPref (concreteGrid base j k vⱼ vₖ (n + m) 0)
                            (concreteGrid base j k vⱼ vₖ (n' + m') 0) :=
        hjweak (n' + m') (n + m) hle
      exact IsWeakOrder.transitive _ _ _ (IsWeakOrder.transitive _ _ _ hL.1 hax) hR.2
  -- assemble `GridAdditiveSliceRep`
  refine ⟨?_, ?_⟩
  · intro n m n' m'
    rw [hSnorm n m, hSnorm n' m', hcore n m n' m']
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  · intro n m; exact hSnorm n m

/-- **G4.a construction (slice form): `GridAdditiveSliceRep` with `S = Vⱼ + Vₖ`
(PROVED).**

Specializes `gridAdditiveSliceRep_of_data` to `S = gridIndexSumScore`, using the
normalization witness for property (ii).  This is the §IV.5 Step-4 calibration output
on the grid, from {normalization witness + concrete diagonal step (G1) + strict
monotonicity}.  Audit `[propext, Quot.sound]`. -/
theorem gridAdditiveSliceRep_of_normalization_diagonal_monotone
    [ProductPref.IsWeakOrder P] {j k : ι} (hjk : j ≠ k)
    {σⱼ : StandardSequence P j} {σₖ : StandardSequence P k}
    {Vⱼ : X j → ℝ} {Vₖ : X k → ℝ}
    (hgrid : WakkerRoadmap.CertificateChecklist.PairwiseGridNormalizationWitness σⱼ σₖ Vⱼ Vₖ)
    (base : Profile X)
    (hdiag : ConcreteDiagonalStep P base j k σⱼ.α σₖ.α)
    (hmono : GridStepStrictMono P base j k σⱼ.α σₖ.α) :
    GridAdditiveSliceRep P base j k σⱼ.α σₖ.α (gridIndexSumScore j k Vⱼ Vₖ) :=
  gridAdditiveSliceRep_of_data base j k σⱼ.α σₖ.α (gridIndexSumScore j k Vⱼ Vₖ)
    (gridIndexSumScore_eq_indexSum hjk hgrid base) hdiag hmono

/-- **Soundness capstone (PROVED): a representation supplies the slice rep.**

Under an additive representation with a strictly-increasing, equal-spaced calibrated
grid (and the normalization witness), all three construction ingredients hold
(`gridStepStrictMono_of_additiveRep`, `concreteDiagonalStep_of_additiveRep_grid`), so
the grid-additive slice representation follows.  Confirms the construction hides
nothing false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridAdditiveSliceRep_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k : ι} (hjk : j ≠ k)
    {σⱼ : StandardSequence P j} {σₖ : StandardSequence P k}
    {Vⱼ : X j → ℝ} {Vₖ : X k → ℝ}
    (hgrid : WakkerRoadmap.CertificateChecklist.PairwiseGridNormalizationWitness σⱼ σₖ Vⱼ Vₖ)
    (base : Profile X)
    (hjmono : ∀ n, R.V j (σⱼ.α n) < R.V j (σⱼ.α (n + 1)))
    (hkmono : ∀ m, R.V k (σₖ.α m) < R.V k (σₖ.α (m + 1)))
    (hspace : ∀ n m,
      R.V j (σⱼ.α (n + 1)) + R.V k (σₖ.α m) = R.V j (σⱼ.α n) + R.V k (σₖ.α (m + 1))) :
    GridAdditiveSliceRep P base j k σⱼ.α σₖ.α (gridIndexSumScore j k Vⱼ Vₖ) :=
  gridAdditiveSliceRep_of_normalization_diagonal_monotone hjk hgrid base
    (concreteDiagonalStep_of_additiveRep_grid R hjk base σⱼ.α σₖ.α hspace)
    (gridStepStrictMono_of_additiveRep R hjk base σⱼ.α σₖ.α hjmono hkmono)

end ProductPref
end WakkerInfra

/-! ## G4.a audit

* §A: `gridIndexSumScore`, `gridIndexSumScore_eq_indexSum` — the score `S = Vⱼ + Vₖ`
  and its index-sum value on grid profiles (property ii, free).
* §B: `score_concreteGrid`; `GridStepStrictMono` + `gridStepStrictMono_of_additiveRep`;
  `concreteDiagonalStep_of_additiveRep_grid` — the order primitives and their
  soundness gates.
* §C: `gridAdditiveSliceRep_of_data` (general), then
  `gridAdditiveSliceRep_of_normalization_diagonal_monotone` (slice form) — **the G4.a
  construction of `S` and `GridAdditiveSliceRep`**; `gridAdditiveSliceRep_of_additiveRep`
  the soundness capstone.

**Honest scope.**  G4.a constructs `S` and the grid representation from the §IV.5
Step-4 data: the normalization witness (theorem-backed, injective grids), the concrete
diagonal step (G1, reduced to the cross-pair / block crux), and strict monotonicity
(necessary under a rep; the weak form is a documented no-go).  Link-B's first brick is
complete modulo the same G1 crux. -/

#print axioms WakkerInfra.ProductPref.gridIndexSumScore_eq_indexSum
#print axioms WakkerInfra.ProductPref.score_concreteGrid
#print axioms WakkerInfra.ProductPref.gridStepStrictMono_of_additiveRep
#print axioms WakkerInfra.ProductPref.concreteDiagonalStep_of_additiveRep_grid
#print axioms WakkerInfra.ProductPref.gridAdditiveSliceRep_of_data
#print axioms WakkerInfra.ProductPref.gridAdditiveSliceRep_of_normalization_diagonal_monotone
#print axioms WakkerInfra.ProductPref.gridAdditiveSliceRep_of_additiveRep
