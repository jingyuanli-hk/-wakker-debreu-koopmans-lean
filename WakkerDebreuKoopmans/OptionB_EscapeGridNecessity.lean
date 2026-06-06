/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-density + WP-B1: the escape-grid / density residual is necessary

This file executes the honest, machine-checkable content of work packages
**WP-density** and **WP-B1** of `OptionB_UnconditionalConstructionRoadmap.md`,
following the discipline that governed §5/WP-CI: **establish necessity
(soundness) of a residual rather than fabricate a discharge that the repository's
own no-go theorems refute.**

## The negative result (already in the repo — do not fight it)

`M2Frontier.lean` proves, for the additive-real `Bool`-model, that **even with a
genuine additive representation**:

* `additiveRealBool_strictStandardSequence_not_dense` — every *strict* standard
  sequence is a utility-arithmetic progression, hence its grid is **not dense**;
* `additiveRealBool_archimedean_tradeoff_solvability_insufficient_for_selectedRefinedDenseGrid`
  — {`IsWeakOrder`, `RestrictedSolvability`, `TradeoffConsistency`, `Archimedean`}
  do **not** imply even a single dense strict standard sequence.

So **WP-density ("construct one dense standard sequence") is impossible**, and the
per-`aPrev` **two-sided** escape grid of WP-B1 is **not** a free consequence of the
structural + Archimedean + topology axioms.  A single strict standard sequence
escapes a reference on **one side only** (its utility runs to `−∞`, not `+∞`).
Density / two-sided escape genuinely needs a refinement/bisection *family* of
sequences with steps of both signs — the §IV.2.6 standard-sequence content that
the no-go theorems certify is irreducible.

## What is therefore the honest WP-density/WP-B1 deliverable

1. **Necessity / soundness of the escape residual** (this file): *given* an
   additive representation, a strict standard sequence's grid escapes any
   reference *below*, and a positive-step sequence escapes it *above*; together
   (sequences of both step signs) they two-sidedly escape.  This confirms the
   escape-grid residual is a **true consequence** of having a representation —
   so carrying it as a structural residual hides nothing false (the analogue of
   WP-CI's `doubleCancellation_of_additiveRep`).

2. **Reduction to between-points coverage** (already in `M2Frontier.lean`): the
   density residual reduces, via
   `selectedRefinedDenseGridCertificate_real_of_betweenPointsCertificate`, to the
   `SelectedRefinedGridBetweenPointsCertificate` (a refinement family hitting
   every interval).  That refinement-family existence is the genuine §IV.2.6
   residual; this file records that it is the right (necessary) target.

This file imports only `M2Frontier` (for the cofinality lemmas and the no-go
model) and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.M2Frontier

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBEscapeGridNecessity

open WakkerInfra
open WakkerInfra.ProductPref
open WakkerDebreuKoopmans (AdditiveRep)

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-! ## §A.  Score of a grid point along a pivot standard sequence -/

/-- The additive score of a pivot-grid point splits as the pivot utility at the
grid value plus a fixed remainder. -/
lemma score_gridPoint (R : AdditiveRep P) {j₀ : ι}
    (σ : ProductPref.StandardSequence P j₀) (n : ℕ) :
    (∑ i, R.V i (Function.update σ.base j₀ (σ.α n) i))
      = R.V j₀ (σ.α n) + ∑ i ∈ Finset.univ.erase j₀, R.V i (σ.base i) :=
  AdditiveRep.sum_update_eq R.V σ.base j₀ (σ.α n)

/-! ## §B.  Necessity of one-sided escape (the genuine residual, proved sound) -/

/-- **Lower escape is necessary.**

Given an additive representation `R`, a *strict* standard sequence `σ` on the
pivot `j₀`, and **any** reference profile `b`, some grid point escapes `b` below:
`¬ P.weakPref (grid n) b`.  (The strict sequence's pivot utility runs to `−∞`, so
its score eventually drops below `∑V(b)`.)

This is the soundness witness for the lower half of the WP-B1 escape grid: the
residual is a genuine consequence of possessing a representation. -/
theorem lowerEscape_necessary (R : AdditiveRep P) {j₀ : ι}
    (σ : ProductPref.StandardSequence P j₀) (hσ : σ.IsStrict)
    (b : Profile X) :
    ∃ n : ℕ, ¬ P.weakPref (Function.update σ.base j₀ (σ.α n)) b := by
  set Δ : ℝ := R.V σ.k σ.r - R.V σ.k σ.s with hΔdef
  have hΔneg : Δ < 0 :=
    additiveRep_standardSequence_step_negative_of_strict R σ hσ
  set rest : ℝ := ∑ i ∈ Finset.univ.erase j₀, R.V i (σ.base i) with hrest
  set Sb : ℝ := ∑ i, R.V i (b i) with hSb
  -- Choose N so that V_{j₀}(σ.α N) + rest < Sb.
  have hposNeg : 0 < -Δ := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((R.V j₀ (σ.α 0) + rest - Sb) / (-Δ))
  have hN' : R.V j₀ (σ.α 0) + rest - Sb < (N : ℝ) * (-Δ) :=
    (div_lt_iff₀ hposNeg).mp hN
  refine ⟨N, ?_⟩
  -- ¬ weakPref (grid N) b  ↔  ¬ (Sb ≤ score (grid N))  ↔  score (grid N) < Sb.
  rw [R.represents]
  intro hle  -- hle : ∑ V (b) ≤ ∑ V (grid N), i.e. Sb ≤ score(grid N)
  rw [score_gridPoint R σ N] at hle
  have harith : R.V j₀ (σ.α N) = R.V j₀ (σ.α 0) + (N : ℝ) * Δ :=
    additiveRep_standardSequence_Vj_arithmetic R σ N
  rw [harith] at hle
  -- hle : Sb ≤ (V(α0) + N·Δ) + rest, contradicting hN'.
  nlinarith [hN', hΔneg]

/-- **Upper escape is necessary (positive-step sequence).**

Dual of `lowerEscape_necessary`: a standard sequence whose pivot utility step is
*positive* escapes any reference `b` above: `¬ P.weakPref b (grid n)`.  In
Wakker's framework the positive-step sequence is the reverse-exchange companion
of a strict sequence; here the positive step is an explicit algebraic input, so
the lemma stays representation-level and topology-free. -/
theorem upperEscape_necessary (R : AdditiveRep P) {j₀ : ι}
    (σ : ProductPref.StandardSequence P j₀)
    (hΔpos : 0 < R.V σ.k σ.r - R.V σ.k σ.s)
    (b : Profile X) :
    ∃ n : ℕ, ¬ P.weakPref b (Function.update σ.base j₀ (σ.α n)) := by
  set Δ : ℝ := R.V σ.k σ.r - R.V σ.k σ.s with hΔdef
  set rest : ℝ := ∑ i ∈ Finset.univ.erase j₀, R.V i (σ.base i) with hrest
  set Sb : ℝ := ∑ i, R.V i (b i) with hSb
  obtain ⟨N, hN⟩ := exists_nat_gt ((Sb - R.V j₀ (σ.α 0) - rest) / Δ)
  have hN' : Sb - R.V j₀ (σ.α 0) - rest < (N : ℝ) * Δ :=
    (div_lt_iff₀ hΔpos).mp hN
  refine ⟨N, ?_⟩
  rw [R.represents]
  intro hle  -- hle : ∑ V (grid N) ≤ ∑ V (b), i.e. score(grid N) ≤ Sb
  rw [score_gridPoint R σ N] at hle
  have harith : R.V j₀ (σ.α N) = R.V j₀ (σ.α 0) + (N : ℝ) * Δ :=
    additiveRep_standardSequence_Vj_arithmetic R σ N
  rw [harith] at hle
  nlinarith [hN', hΔpos]

/-- **Two-sided escape is necessary, given sequences of both step signs.**

Combining `lowerEscape_necessary` (a strict sequence) and `upperEscape_necessary`
(a positive-step sequence on the *same* base), the reference `b` is escaped on
both sides.  This is the full soundness witness for the WP-B1 two-sided escape
grid — it confirms the residual is a genuine consequence of the representation,
and it makes precise *why* a single sequence is insufficient (one needs both step
signs, hence a refinement family, exactly as the no-go theorems show). -/
theorem twoSidedEscape_necessary (R : AdditiveRep P) {j₀ : ι}
    (σdown σup : ProductPref.StandardSequence P j₀)
    (hσdown : σdown.IsStrict)
    (hσup_pos : 0 < R.V σup.k σup.r - R.V σup.k σup.s)
    (hbase : σdown.base = σup.base)
    (b : Profile X) :
    (∃ n : ℕ, ¬ P.weakPref (Function.update σdown.base j₀ (σdown.α n)) b) ∧
    (∃ n : ℕ, ¬ P.weakPref b (Function.update σup.base j₀ (σup.α n))) :=
  ⟨lowerEscape_necessary R σdown hσdown b,
   upperEscape_necessary R σup hσup_pos b⟩

/-! ## §C.  The density residual is necessary and reduces to between-points coverage

`M2Frontier.selectedRefinedDenseGridCertificate_real_of_betweenPointsCertificate`
already proves: a `SelectedRefinedGridBetweenPointsCertificate` (a chosen strict
standard sequence hitting every real open interval) yields a
`SelectedRefinedDenseGridCertificate` (a dense strict standard-sequence grid).

By the no-go `additiveRealBool_not_selectedRefinedDenseGridCertificate_*`, the
between-points coverage is **not** free from the structural axioms: it is the
genuine §IV.2.6 refinement-family residual.  We record the reduction direction as
the WP-density target. -/

/-- **WP-density target reduction (re-export).**  Dense selected grid from
between-points coverage — the proved implication; the residual is the coverage. -/
theorem selectedRefinedDenseGrid_of_betweenPoints
    {P : ProductPref (fun _ : ι => ℝ)} (j : ι)
    (hBetween : WakkerRoadmap.CertificateChecklist.SelectedRefinedGridBetweenPointsCertificate (P := P) j) :
    WakkerRoadmap.CertificateChecklist.SelectedRefinedDenseGridCertificate P j :=
  WakkerRoadmap.CertificateChecklist.selectedRefinedDenseGridCertificate_real_of_betweenPointsCertificate
    j hBetween

end OptionBEscapeGridNecessity
end CertificateChecklist
end WakkerRoadmap

/-! ## WP-density / WP-B1 audit

The escape-necessity theorems are sorry-free and foundational-only.  They are the
soundness witnesses for the irreducible §IV.2.6 escape-grid / density residual;
they do **not** (and provably cannot) discharge it. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridNecessity.lowerEscape_necessary
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridNecessity.upperEscape_necessary
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridNecessity.twoSidedEscape_necessary
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEscapeGridNecessity.selectedRefinedDenseGrid_of_betweenPoints
