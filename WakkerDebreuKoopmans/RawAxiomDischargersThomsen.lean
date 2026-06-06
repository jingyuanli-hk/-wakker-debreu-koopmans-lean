/-
Copyright (c) 2026 Wakker–Debreu–Koopmans project.
SPDX-License-Identifier: Apache-2.0

# Step-4 discharge — Residual A scaffolding (Thomsen / equal-spacing via a third coordinate)

This file begins the discharge of the last `_from_raw_axioms` axiom,
`sharedPivotStep4TradeoffFamilyOnDataCertificate_from_raw_axioms`
(`RawAxiomDischargers.lean`).  See `STEP4_DISCHARGE_ROADMAP.md` for the full plan.

The Step-4 family reduces to constructing, per non-pivot slice `(j₀, k)`, a
grid-normalized additive slice representation.  Engine-C
(`RawAxiomDischargersHexagon.lean`) already reduces the discrete-grid core to the
single residual `KGridEqualSpacing` (equivalently `DiagonalLayerPropagation`),
with the reference layer (`m = 0`) supplied for free from the standard
sequence's `spaced` field.

This file provides the **lower-risk Residual-A scaffolding** (roadmap §2, A0/A2):

* `exists_third_coordinate` — from `3 ≤ Fintype.card ι` and `j₀ ≠ k`, a third
  coordinate `l ∉ {j₀, k}` exists (the cardinality fact that the genuine
  Thomsen-via-third-coordinate keystone, roadmap A1, will consume).
* The mechanical **A2 assembly**: `KGridEqualSpacing` + the reference exchange at
  layer 0 ⟹ `ConcreteDiagonalStep` ⟹ equal-index-sum grid indifference.  All
  fully theorem-backed from existing engine-C lemmas; no new axioms.

The genuine remaining keystone (roadmap A1,
`kGridEqualSpacing_of_thirdCoordinate`) is documented at the end as the precise
open target; it is **not** asserted here (no `sorry`, no `axiom`).

Like `RawAxiomDischargersHexagon`, this file is **not** in the umbrella import.
-/
import WakkerDebreuKoopmans.RawAxiomDischargersHexagon
import WakkerDebreuKoopmans.OptionB_CoordinateIndependence

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace RawAxiomDischargersThomsen

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

open WakkerInfra
open Function
open RawAxiomDischargersHexagon

variable {X : ι → Type v}

/-! ## §A0.b  Third-coordinate existence

The genuine §IV.6 Thomsen-via-third-coordinate argument (roadmap A1) needs a
coordinate `l` distinct from both `j₀` and `k`.  Under the project's standing
`3 ≤ Fintype.card ι` regime this is immediate. -/

/-- **A third coordinate exists.**  Under `3 ≤ Fintype.card ι`, for any two
coordinates `j₀, k` there is an `l` distinct from both.  Pure cardinality; this
is the first essential use of the `card ≥ 3` regime in the calibration core. -/
theorem exists_third_coordinate {j₀ k : ι}
    (hcard : 3 ≤ Fintype.card ι) :
    ∃ l : ι, l ≠ j₀ ∧ l ≠ k := by
  classical
  by_contra h
  push_neg at h
  -- h : ∀ l, l = j₀ → l = k  (after push_neg the negation of `l ≠ j₀ ∧ l ≠ k`)
  have hcover : ∀ l : ι, l = j₀ ∨ l = k := by
    intro l
    by_cases hlj : l = j₀
    · exact Or.inl hlj
    · exact Or.inr (h l hlj)
  have hsub : (Finset.univ : Finset ι) ⊆ {j₀, k} := by
    intro l _
    rcases hcover l with h1 | h1 <;> simp [h1]
  have hle : Fintype.card ι ≤ 2 := by
    have hcard_le : (Finset.univ : Finset ι).card ≤ ({j₀, k} : Finset ι).card :=
      Finset.card_le_card hsub
    have hpair : ({j₀, k} : Finset ι).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    rw [Finset.card_univ] at hcard_le
    exact le_trans hcard_le hpair
  omega

/-! ## §A2  Mechanical assembly: `KGridEqualSpacing` ⟹ diagonal step ⟹ equal-sum indifference

Engine-C already proves `KGridEqualSpacing ⟹ DiagonalLayerPropagation`
(`diagonalLayerPropagation_of_kGridEqualSpacing`) and `referenceLayer +
propagation ⟹ ConcreteDiagonalStep` (`concreteDiagonalStep_of_spaced_and_propagation`).
These wrappers compose them into the form the Step-4 construction consumes, so
that once the keystone (roadmap A1) supplies `KGridEqualSpacing`, the grid
diagonal content follows with no further hexagon work. -/

/-- **`ConcreteDiagonalStep` from `KGridEqualSpacing` + reference exchange at layer 0.**

With the `k`-grid arranged so the reference exchange `(σ.s, σ.r)` sits at layer 0
(`vₖ 0 = σ.s`, `vₖ 1 = σ.r`), the base layer of the diagonal step is supplied by
`σ.spaced` (engine-C §9) and `KGridEqualSpacing` propagates it to every layer.
This is the full A2 chain, theorem-backed from engine-C. -/
theorem concreteDiagonalStep_of_kGridEqualSpacing_and_referenceLayer
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j) (vₖ : ℕ → X σ.k)
    (hs0 : vₖ 0 = σ.s) (hr1 : vₖ 1 = σ.r)
    (hspace : KGridEqualSpacing P σ.base j σ.k σ.α vₖ) :
    ConcreteDiagonalStep P σ.base j σ.k σ.α vₖ :=
  concreteDiagonalStep_of_spaced_and_propagation P σ vₖ hs0 hr1
    (diagonalLayerPropagation_of_kGridEqualSpacing P σ.base j σ.k σ.α vₖ hspace)

/-- **Equal-index-sum grid indifference from `KGridEqualSpacing` + reference layer.**

The §IV.5 calibration's diagonal output on the concrete rectangle: any two grid
profiles with equal index sum are indifferent, assuming only the keystone
`KGridEqualSpacing` (roadmap A1) and the layer-0 reference exchange.  Composes
`concreteDiagonalStep_of_kGridEqualSpacing_and_referenceLayer` with engine-C's
`concreteGrid_indiff_of_eqSum`. -/
theorem concreteGrid_indiff_of_eqSum_of_kGridEqualSpacing
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j) (vₖ : ℕ → X σ.k)
    (hs0 : vₖ 0 = σ.s) (hr1 : vₖ 1 = σ.r)
    (hspace : KGridEqualSpacing P σ.base j σ.k σ.α vₖ)
    {n m n' m' : ℕ} (hsum : n + m = n' + m') :
    P.indiff (concreteGrid σ.base j σ.k σ.α vₖ n m)
             (concreteGrid σ.base j σ.k σ.α vₖ n' m') :=
  concreteGrid_indiff_of_eqSum P σ.base j σ.k σ.α vₖ
    (concreteDiagonalStep_of_kGridEqualSpacing_and_referenceLayer P σ vₖ hs0 hr1 hspace)
    hsum

/-! ## §A1 (open keystone) — `kGridEqualSpacing_of_thirdCoordinate`

The single genuine remaining residual of Residual A (roadmap §2, A1).  Stated
here as documentation only — **not** asserted (no `sorry`, no `axiom`).

### The recognized residual: `DoubleCancellation` (the Thomsen condition)

`OptionB_CoordinateIndependence.lean` already names the literature-standard
residual: `WakkerInfra.ProductPref.DoubleCancellation P j₀ k` (the additive-
conjoint double-cancellation / Thomsen condition).  Its docstring records the
classical fact that for `n = 2` it is genuinely extra, while for **n ≥ 3** it is
derivable from coordinate independence via a third coordinate (KLST Vol. 1,
Thm. 6.2).  That n ≥ 3 derivation is the genuine open keystone.

### What is theorem-backed here

`standardThomsen_of_doubleCancellation` below proves the *forward* bridge:
`DoubleCancellation P j₀ k` specializes directly to engine-C's grid Thomsen
`RawAxiomDischargersHexagon.StandardThomsen` on the concrete standard-sequence
rectangle.  This connects the recognized structural residual to the grid
machinery.

### What remains (and why it is not `DoubleCancellation` alone)

Index-algebra analysis (see roadmap §2) shows `StandardThomsen` /
`DoubleCancellation` **alone** does not close `KGridEqualSpacing`: a single
Thomsen application cannot bridge the `k`-grid steps `(βm, β(m+1))` to
`(β(m+1), β(m+2))` because the two standard-sequence grids `σⱼ₀.α` and `σₖ.α` are
built against *their own* auxiliary coordinates, not against each other.  The
genuine remaining content is the **mutual calibration** of the two grids (Wakker
§IV.5 affine renormalization), i.e. constructing `ConcreteDiagonalStep` /
`GridAdditiveSliceRep` directly.  The two honest routes to it:

* **(A1-Thomsen)** prove `DoubleCancellation P j₀ k` from coordinate
  independence + a third coordinate (`exists_third_coordinate`), then combine
  with the `σⱼ₀.α`/`σₖ.α` standard-sequence spacings to calibrate the grids; or
* **(A1-rep)** construct the grid-additive representation directly via the
  off-grid extension (roadmap Residual B) and read off the diagonal step from
  `concreteDiagonalStep_of_rep`.

Target shape (conditional on the calibrated diagonal step):

```
theorem kGridEqualSpacing_of_thirdCoordinate
    (P : ProductPref X) [ProductPref.IsWeakOrder P] [ProductPref.TradeoffConsistency P]
    {j₀ k l : ι} (hlj₀ : l ≠ j₀) (hlk : l ≠ k) (hj₀k : j₀ ≠ k)
    (σⱼ₀ : ProductPref.StandardSequence P j₀) (σₖ : ProductPref.StandardSequence P k)
    (hDC : WakkerInfra.ProductPref.DoubleCancellation P j₀ k)
    (... σⱼ₀.α / σₖ.α spacing-alignment via l ...) :
    KGridEqualSpacing P σⱼ₀.base j₀ k σⱼ₀.α σₖ.α
```

`exists_third_coordinate` supplies `l`; `singleCoordIndiff_baseIndependent`,
`updateIndiff_baseIndependent`, `jIndiff_trans` (in
`RawAxiomDischargersHexagon`) plus raw `TradeoffConsistency` are the toolkit. -/

/-- **`DoubleCancellation` specializes to engine-C's grid Thomsen (forward
bridge).**

The literature double-cancellation / Thomsen condition on the `{j₀,k}` slice,
instantiated at the standard-sequence grid points, is exactly engine-C's
`StandardThomsen` on the concrete rectangle.  Sound and direct: `DoubleCancellation`
quantifies over all coordinate values, so the grid values `vⱼ i`, `vₖ l` are a
special case.  This ties the recognized n ≥ 3 residual to the grid calibration
machinery. -/
theorem standardThomsen_of_doubleCancellation
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (hDC : WakkerInfra.ProductPref.DoubleCancellation P j k) :
    StandardThomsen P base j k vⱼ vₖ := by
  intro i₁ i₂ i₃ l₁ l₂ l₃ h1 h2
  exact hDC base (vⱼ i₁) (vⱼ i₂) (vⱼ i₃) (vₖ l₁) (vₖ l₂) (vₖ l₃) h1 h2

end RawAxiomDischargersThomsen
end CertificateChecklist
end WakkerRoadmap

/-! ## Audit

The scaffolding lemmas must depend only on the foundational axioms
`[propext, Classical.choice, Quot.sound]` (plus, transitively, the engine-C
`TradeoffConsistency`-backed primitives) — no `_from_raw_axioms`, no `sorryAx`. -/

#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersThomsen.exists_third_coordinate
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersThomsen.concreteDiagonalStep_of_kGridEqualSpacing_and_referenceLayer
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersThomsen.concreteGrid_indiff_of_eqSum_of_kGridEqualSpacing
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersThomsen.standardThomsen_of_doubleCancellation
