/-
Copyright (c) 2026 Wakker–Debreu–Koopmans project.
SPDX-License-Identifier: Apache-2.0

# Raw-axiom dischargers — typed skeletons (Phase 8 frontier)

This file lays down **honest typed skeletons** for the five C1 closure
inputs identified in `C1FromStage4.lean`, each as a candidate theorem
from the raw `Essential + RestrictedSolvability + TradeoffConsistency +
Archimedean` axioms.

The five frontier obligations are no longer all primitive `axiom`s.
After successive thinning, the file now exposes a smaller list of
named raw-axiom seams (the `_from_raw_axioms` declarations clustered
around lines 1900–2530), and obligations 1, 2, 3 are theorem-backed
forms that route through those smaller seams.  Obligations 4 and 5 are
documented as overstrong on arbitrary `V`; the end-to-end thin-frontier
route bypasses them by using `Stage4MatchedAllPairsAdditivityData`-
specialized chain and coverage seams.

After Phase 3 (topology architectural decision) and Phase 4 (compatibility
cleanups), the file contains **12 primitive axioms** plus
**1 axiom in `RawAxiomDischargersTopology`**, totaling **13 across the
project** (down from 19 at the start of the multi-session work).  The
three end-to-end consumers all build cleanly under
`[propext, Classical.choice, Quot.sound]` plus the named smaller seams.

`#print axioms` audits surface the exact unresolved Wakker (1989/1991)
§/lemma obligations.  See the `RawAxiomDischargersAttackPlan.md`
companion document for the per-axiom tier classification and sequenced
attack on the residuals.

## Why this file is NOT in the umbrella import

The umbrella `WakkerDebreuKoopmans.lean` deliberately does **not**
import this module.  Each of the surviving `axiom`s in this file is a
genuine research-grade obligation (Wakker IV.2 standard sequences, IV.5
affine renormalization, IV.6 cross-coordinate transport).  Importing
this file into the umbrella would silently inject those axioms into
every downstream `#print axioms` audit and pollute the
`[propext, Classical.choice, Quot.sound]` invariant maintained by the
C1 ladder.  Treat this file as a **scratch surface for the frontier**,
to be built independently:

```powershell
Set-Location "C:\Users\ORM\lean\research"
lake build WakkerDebreuKoopmans.RawAxiomDischargers
```

## Wakker §/lemma map

Each of the five frontier objects carries a docstring tagging the Wakker
(1989, *Additive Representations of Preferences*, Kluwer) section and
lemma that constitutes the open obligation.  Future sessions should
continue replacing primitive `axiom`s with `theorem ... := by <proof>`
under the same typed signatures.

| # | Object                                                  | Wakker chunk                                                         | Status |
|---|---------------------------------------------------------|----------------------------------------------------------------------|--------|
| 1 | `PairwiseFiniteCutCoverageCertificate σj σk`            | IV.2.7 (standard-sequence existence) + IV.3 (Archimedean termination)| theorem |
| 2 | `SharedPivotAllPairsStep4MachineryCertificate P j₀`     | IV.5 (affine renormalization onto a common pivot grid)               | theorem |
| 3 | `NonPivotPairAdditivityCertificate P V j₀`              | IV.6 cross-pair (Thomsen-condition transport across {j,k}, j,k≠j₀)  | theorem |
| 4 | `WakkerStep5StrictMonotonicityResidualAtPivot P V j₀`   | IV.6 strict-monotonicity for non-pivot-touching indifferences        | axiom (overstrong on `V`) |
| 5 | `WakkerStep5CoordinateImageCoverageResidualAtPivot V j₀`| IV.2.7 (existence of pivot bracketing value, Archimedean Step-5)     | axiom (overstrong on `V`) |
-/
import WakkerDebreuKoopmans.Certificates
import WakkerDebreuKoopmans.Closure
import WakkerDebreuKoopmans.C1FromStage4
import WakkerDebreuKoopmans.RawAxiomDischargersTopology
import WakkerDebreuKoopmans.RawAxiomDischargersStandardSequence
import WakkerDebreuKoopmans.RawAxiomDischargersHexagon
import WakkerDebreuKoopmans.RawAxiomDischargersIVT

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

open scoped BigOperators
open Function Finset
open Classical

namespace WakkerRoadmap

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

open WakkerInfra
open WakkerDebreuKoopmans (AdditiveRep)

namespace CertificateChecklist
namespace RawAxiomDischargers

/-! ## 1. `PairwiseFiniteCutCoverageCertificate` from raw axioms

**Wakker reference:** §IV.2.7 (`Standard Sequences`, existence of finite
brackets on every slice target) combined with §IV.3 (Archimedean
termination of the standard sequence on each coordinate).

**Obligation contents.**  Given two standard sequences `σⱼ` on
coordinate `j` and `σₖ` on coordinate `k`, for *every* base/target pair
agreeing off `{j, k}`, exhibit finite indices `(n_lo, m_lo, n_hi, m_hi)`
such that the target sits inside the corresponding `σⱼ × σₖ` rectangle
under `≽`.

**Why this is hard.**  The existence of the four indices requires:

* (Wakker IV.2.7) construction of the standard sequence itself — i.e.
  the inductive recursion that, on each step, invokes `RestrictedSolvability`
  to extract the next grid point matching the previous tradeoff;
* (Wakker IV.3) Archimedean termination: every target is eventually
  *strictly* above (resp. below) some grid point in finitely many steps;
* (Wakker IV.5 corollary, lite form) the *joint* bracket on the product
  pair `σⱼ × σₖ`, which uses `TradeoffConsistency` to align the two
  one-coordinate brackets into a single rectangle.

A non-trivial Lean proof builds a recursive bracket extractor calling
`Archimedean.lt_to_eventually_grid` (or its standard-sequence form) on
each coordinate, then closes the rectangle with the tradeoff-consistency
lemma `tradeoffConsistency_rectangle_close`. -/

/- **Open obligation 1.**  Existence of the finite-cut coverage certificate
for any pair of standard sequences, from the raw axioms.

The actual `theorem` lives near the bottom of the file, since its proof
routes through smaller wrappers defined later.  This anchor placeholder
preserves the historical entry point and pin-points the
`#print axioms` audit target. -/
section ObligationOneFrontier
end ObligationOneFrontier

/-- **Partial discharge of obligation 1 (explicit base-transport fragment).**

The finite-cut coverage target is already theorem-backed from the raw
Archimedean axioms in the active coordinates together with the explicit
residual bridge `PairwiseArchimedeanBaseTransportCertificate σj σk`.
Supplying that bridge therefore discharges the obligation with no new
axioms.

This pin-points the real residual in obligation 1: not the assembly of the
four cut indices itself, but the transport from the standard-sequence bases
to arbitrary slice bases. -/
theorem pairwiseFiniteCutCoverageCertificate_from_raw_axioms_of_baseTransport
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (htransport : PairwiseArchimedeanBaseTransportCertificate σj σk) :
    PairwiseFiniteCutCoverageCertificate σj σk := by
  exact pairwiseFiniteCutCoverageCertificate_of_archimedean_and_baseTransport
    (archimedean j) (archimedean k) htransport

/-- **Partial discharge of obligation 1 (surjective-grid fragment).**

If both standard-sequence coordinate maps are surjective and `j ≠ k`, then
finite-cut coverage is immediate: choose the indices that hit the target
coordinates exactly, collapsing the cut rectangle to a single grid point.

This is much stronger than the raw Wakker hypotheses, but it supplies a clean
theorem-backed discharge of the frontier obligation on an important special
regime. -/
theorem pairwiseFiniteCutCoverageCertificate_from_raw_axioms_of_surjectiveStandardSequences
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseFiniteCutCoverageCertificate σj σk := by
  exact pairwiseFiniteCutCoverageCertificate_of_surjectiveStandardSequences
    P hjk σj σk hsurj_j hsurj_k

/-- **Partial discharge of obligation 1 (grid-reachability + surjective second
coordinate).**

The current strongest theorem-backed structural route to finite-cut coverage
uses raw Archimedean in both coordinates, the explicit residual
`PairwiseGridReachabilityCertificate σj σk`, and surjectivity of the second
coordinate grid. -/
theorem pairwiseFiniteCutCoverageCertificate_from_raw_axioms_of_gridReachability_and_surjectiveSecondCoord
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hreach : PairwiseGridReachabilityCertificate σj σk)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseFiniteCutCoverageCertificate σj σk := by
  exact
    pairwiseFiniteCutCoverageCertificate_of_archimedean_and_gridReachability_and_surjectiveSecondCoord
      P hjk σj σk (archimedean j) (archimedean k) hreach hsurj_k

/-- **Partial discharge of obligation 1 (grid-reachability + surjective first
coordinate).**

Symmetric companion to the previous theorem: the same structural route works
if surjectivity is available on the first coordinate grid instead. -/
theorem pairwiseFiniteCutCoverageCertificate_from_raw_axioms_of_gridReachability_and_surjectiveFirstCoord
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hreach : PairwiseGridReachabilityCertificate σj σk)
    (hsurj_j : Function.Surjective σj.α) :
    PairwiseFiniteCutCoverageCertificate σj σk := by
  exact
    pairwiseFiniteCutCoverageCertificate_of_archimedean_and_gridReachability_and_surjectiveFirstCoord
      P hjk σj σk (archimedean j) (archimedean k) hreach hsurj_j

/-- **Partial discharge of obligation 1 (exact cut-construction fragment).**

An exact `PairwiseCutConstructionCertificate` is stronger than finite-cut
coverage, so it discharges the obligation immediately by collapsing the
rectangle to a single exact grid witness. -/
theorem pairwiseFiniteCutCoverageCertificate_from_raw_axioms_of_pairwiseCutConstructionCertificate
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hcut : PairwiseCutConstructionCertificate σj σk Vj Vk) :
    PairwiseFiniteCutCoverageCertificate σj σk := by
  exact pairwiseFiniteCutCoverageCertificate_of_pairwiseCutConstructionCertificate hcut

/-! ## 2. `SharedPivotAllPairsStep4MachineryCertificate` from raw axioms

**Wakker reference:** §IV.5 — *Step 4 of the additive-representation
construction* — affine renormalization onto a common pivot grid.

**Obligation contents.**  For a fixed pivot `j₀ : ι`, produce a single
standard sequence `σⱼ₀` on the pivot together with, for every non-pivot
coordinate `k ≠ j₀`, a standard sequence `σₖ` and a witness of
`PairwiseStep4TradeoffMachineryCertificate P j₀ k σⱼ₀ σₖ` (the Wakker
Step-4 Thomsen-condition / tradeoff-consistency package).

**Why this is hard.**  Each per-pair `σⱼ₀^{(k)}` produced by the
single-pair Step-4 construction is *intrinsically tied to k*.  Forcing
them to coincide across all `k` requires the joint Thomsen-condition
cascade (Wakker IV.5.3–IV.5.7): one fixes a reference grid on `j₀`
and proves that the per-pair scales obtained for two distinct `k₁, k₂`
agree on the pivot.  This is the substantive content of Wakker IV.5
and is precisely what the existing C1 wrapper assumes as data. -/

/- **Open obligation 2.**  Shared-pivot all-pairs Step-4 machinery for any
chosen pivot `j₀`, from the raw axioms.

The actual `theorem` lives near the bottom of the file, since its proof
routes through smaller wrappers defined later. -/
section ObligationTwoFrontier
end ObligationTwoFrontier

/-- **Partial discharge of obligation 2 (one-coordinate degenerate fragment).**

When `Fintype.card ι = 1`, there are no non-pivot coordinates at all, so the
`∀ k ≠ j₀, ...` part of the shared-pivot Step-4 machinery certificate is
vacuous.  In that regime, the only non-vacuous datum is a pivot-side
standard sequence with injective grid map.

This theorem isolates the genuinely multi-coordinate content of obligation 2:
once the coordinate universe collapses to a singleton, no cross-pair Thomsen
or renormalization argument remains. -/
theorem sharedPivotAllPairsStep4MachineryCertificate_from_raw_axioms_of_card_eq_one
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hcard : Fintype.card ι = 1)
    (σj₀ : ProductPref.StandardSequence P j₀)
    (hinj : Function.Injective σj₀.α) :
    SharedPivotAllPairsStep4MachineryCertificate P j₀ := by
  refine ⟨σj₀, hinj, ?_⟩
  intro k hk
  exfalso
  have hj₀_notin : j₀ ∉ ({k} : Finset ι) := by
    simp [Ne.symm hk]
  have hcard2 : ({j₀, k} : Finset ι).card = 2 := by
    rw [Finset.card_insert_of_notMem hj₀_notin, Finset.card_singleton]
  have hge2 : 2 ≤ Fintype.card ι := by
    calc
      2 = ({j₀, k} : Finset ι).card := hcard2.symm
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **Partial discharge of obligation 2 (shared-pivot hexagon family).**

Suppose a single pivot standard sequence `σⱼ₀` is fixed, and for every
non-pivot coordinate `k ≠ j₀` we have an injective standard sequence `σk`
together with the theorem-backed
`PairwiseHexagonStandardSequenceCertificate P j₀ k σⱼ₀ σk`.  Then the shared-
pivot Step-4 machinery follows by converting each per-pair hexagon payload to
`PairwiseStep4TradeoffMachineryCertificate` and packaging the common pivot
sequence once.

This isolates the truly remaining content of obligation 2: building a *shared
pivot family* of pairwise hexagon certificates from the raw axioms. -/
theorem sharedPivotAllPairsStep4MachineryCertificate_from_raw_axioms_of_sharedPivotHexagonFamily
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (σⱼ₀ : ProductPref.StandardSequence P j₀)
    (hinj_j₀ : Function.Injective σⱼ₀.α)
    (hhex : ∀ k : ι, k ≠ j₀ →
      ∃ (σk : ProductPref.StandardSequence P k),
        Function.Injective σk.α ∧
        PairwiseHexagonStandardSequenceCertificate P j₀ k σⱼ₀ σk) :
    SharedPivotAllPairsStep4MachineryCertificate P j₀ := by
  refine ⟨σⱼ₀, hinj_j₀, ?_⟩
  intro k hk
  obtain ⟨σk, hinj_k, hhex_k⟩ := hhex k hk
  refine ⟨σk, hinj_k, ?_⟩
  exact
    pairwiseStep4TradeoffMachineryCertificate_of_pairwiseHexagonStandardSequenceCertificate
      P j₀ k σⱼ₀ σk hhex_k

/-- **Partial discharge of obligation 2 (shared-pivot magnitude/bracketing
family).**

This lowers the previous shared-pivot hexagon-family fragment one step: a
family of theorem-backed `PairwiseMagnitudeBracketingHexagonCertificate`s at a
common pivot upgrades to the shared-pivot Step-4 machinery by first turning
each pair into a hexagon/standard-sequence certificate and then invoking the
shared-pivot hexagon-family wrapper. -/
theorem sharedPivotAllPairsStep4MachineryCertificate_from_raw_axioms_of_sharedPivotMagnitudeBracketingFamily
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (σⱼ₀ : ProductPref.StandardSequence P j₀)
    (hinj_j₀ : Function.Injective σⱼ₀.α)
    (hmbh : ∀ k : ι, k ≠ j₀ →
      ∃ (σk : ProductPref.StandardSequence P k),
        Function.Injective σk.α ∧
        PairwiseMagnitudeBracketingHexagonCertificate P j₀ k σⱼ₀ σk) :
    SharedPivotAllPairsStep4MachineryCertificate P j₀ := by
  apply sharedPivotAllPairsStep4MachineryCertificate_from_raw_axioms_of_sharedPivotHexagonFamily
    P _essential _solvability _archimedean j₀ σⱼ₀ hinj_j₀
  intro k hk
  obtain ⟨σk, hinj_k, hmbh_k⟩ := hmbh k hk
  refine ⟨σk, hinj_k, ?_⟩
  exact
    pairwiseHexagonStandardSequenceCertificate_of_pairwiseMagnitudeBracketingHexagonCertificate
      P hk.symm σⱼ₀ σk hmbh_k

/-! ## 3. `NonPivotPairAdditivityCertificate` from raw axioms (`hCross`)

**Wakker reference:** §IV.6 — cross-pair additivity for two non-pivot
coordinates `j ≠ j₀`, `k ≠ j₀`, `j ≠ k`.

**Obligation contents.**  Given a global utility family `V` whose
pivot slices are matched by `PairwiseSliceRepresentationCertificate`,
deduce that the `{j, k}`-restricted additive representation holds.

**Why this is hard.**  The pivot-slice data supplies additivity only on
pairs `{j₀, k}`.  Transferring it to a `{j, k}`-slice with both
coordinates non-pivot requires routing through the pivot: use
`TradeoffConsistency` together with two `{j₀, j}`- and `{j₀, k}`-pair
additivities to derive the desired `{j, k}` equivalence.  This is the
genuine Thomsen-condition application (Wakker IV.6 hexagon argument). -/

/- **Open obligation 3.**  Cross-pair (non-pivot) additivity residue from
the raw axioms, supplied to any matching `V`.

The actual `theorem` lives near the bottom of the file, since its proof
routes through smaller wrappers defined later. -/
section ObligationThreeFrontier
end ObligationThreeFrontier

/-- **Partial discharge of obligation 3 (all-pairs restriction).**

The non-pivot cross-pair residue is a direct restriction of the global
all-pairs additivity certificate: just specialize the latter to pairs
`(j, k)` with `j ≠ j₀`, `k ≠ j₀`. -/
theorem nonPivotPairAdditivityCertificate_from_raw_axioms_of_allPairsAdditivityCertificate
    {X : ι → Type v} (P : ProductPref X) (V : (i : ι) → X i → ℝ) (j₀ : ι)
    (hpair : AllPairsAdditivityCertificate P V) :
    NonPivotPairAdditivityCertificate P V j₀ := by
  intro j k _hj _hk hjk x y hagree
  exact hpair j k hjk x y hagree

/-- **Partial discharge of obligation 3 (global-gluing fragment).**

Any full `GlobalGluingCertificate P V` already restricts to every two-
coordinate slice, so the non-pivot cross-pair residue becomes immediate.
This theorem isolates that once a genuine global additive representation is
available, the Wakker IV.6 hexagon transport is no longer needed as a
separate input. -/
theorem nonPivotPairAdditivityCertificate_from_raw_axioms_of_globalGluingCertificate
    {X : ι → Type v} (P : ProductPref X) (V : (i : ι) → X i → ℝ) (j₀ : ι)
    (hglobal : GlobalGluingCertificate P V) :
    NonPivotPairAdditivityCertificate P V j₀ := by
  intro j k _hj _hk hjk x y hagree
  exact (allPairsAdditivityCertificate_of_globalGluingCertificate P V hglobal)
    j k hjk x y hagree

/-- **Partial discharge of obligation 3 (low-cardinality vacuous fragment).**

When `Fintype.card ι ≤ 2`, the cross-pair non-pivot additivity certificate
is **vacuously true**: any triple `(j, k, j₀)` with `j ≠ j₀`, `k ≠ j₀`,
`j ≠ k` would force three pairwise distinct elements of `ι`, contradicting
the cardinality bound.  Hence the universal statement holds trivially.

This is a real (theorem, not axiom) reduction of obligation 3 in the
degenerate small-coordinate case, with **no** axioms beyond
`[propext, Classical.choice, Quot.sound]`.  The genuine Wakker IV.6
hexagon content lives entirely in the residual `card ι ≥ 3` regime,
which is what the axiom `nonPivotPairAdditivityCertificate_from_raw_axioms`
continues to assert. -/
theorem nonPivotPairAdditivityCertificate_of_card_le_two
    {X : ι → Type v} (P : ProductPref X) (V : (i : ι) → X i → ℝ) (j₀ : ι)
    (hcard : Fintype.card ι ≤ 2) :
    NonPivotPairAdditivityCertificate P V j₀ := by
  intro j k hj hk hjk x y _hagree
  exfalso
  -- The three indices `j₀`, `j`, `k` are pairwise distinct, hence form a
  -- three-element `Finset`, which forces `Fintype.card ι ≥ 3`.
  have hcard3 : ({j₀, j, k} : Finset ι).card = 3 := by
    have hj₀_notin : j₀ ∉ ({j, k} : Finset ι) := by
      simp [Ne.symm hj, Ne.symm hk]
    have hj_notin : j ∉ ({k} : Finset ι) := by simp [hjk]
    rw [Finset.card_insert_of_notMem hj₀_notin,
        Finset.card_insert_of_notMem hj_notin, Finset.card_singleton]
  have hge3 : 3 ≤ Fintype.card ι := by
    calc 3 = ({j₀, j, k} : Finset ι).card := hcard3.symm
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **Raw-axiom-form discharge of obligation 3 in low cardinality.**

This keeps the full raw-axiom-facing parameter list of
`nonPivotPairAdditivityCertificate_from_raw_axioms`, but proves the target
without using any of those raw hypotheses when `Fintype.card ι ≤ 2`.  In that
regime there simply are no two distinct non-pivot coordinates, so the
non-pivot-pair additivity residue is vacuous. -/
theorem nonPivotPairAdditivityCertificate_from_raw_axioms_of_card_le_two
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) (V : (i : ι) → X i → ℝ)
    (_hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k))
    (hcard : Fintype.card ι ≤ 2) :
    NonPivotPairAdditivityCertificate P V j₀ := by
  exact nonPivotPairAdditivityCertificate_of_card_le_two P V j₀ hcard

/-! ## 4. `WakkerStep5StrictMonotonicityResidualAtPivot` from raw axioms
(`hResStrict`)

**Wakker reference:** §IV.6 — strict-monotonicity / sum equality for
indifferent profiles that do not agree off any pivot-touching pair.

**Obligation contents.**  For any two indifferent profiles `x ∼ y`
neither of which agrees with the other off a `{j₀, k}` pair, the
additive sums under `V` coincide:
`∑ V i (x i) = ∑ V i (y i)`.

**Why this is hard.**  Such profiles differ on at least three
coordinates simultaneously; the pair-additivity surface delivers
equality of sums only for pair-aligned indifferences.  Closing the gap
requires iterating the Thomsen-condition transport across an arbitrary
finite path of coordinate swaps (Wakker IV.6 chain lemma), which is the
deep cross-coordinate content beyond pair-additivity. -/

/- **Open obligation 4 — RETIRED (Phase 14).**

This was a primitive `axiom`
`wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms`: a
strict-monotonicity sum-equality residue from the raw axioms for an
**arbitrary** `V`.

It was **overstrong** — universally quantified over an arbitrary externally
chosen `V` that the raw axioms `Essential + RestrictedSolvability +
TradeoffConsistency + Archimedean` cannot constrain (see
`RawAxiomDischargersSpec.md` §4A).  It is **never honestly provable** at this
signature.

It is now deleted.  Its sole consumer was the original end-to-end skeleton
`additiveRep_nonempty_from_raw_axioms`, which (Phase 14) now delegates to
`additiveRep_nonempty_from_thin_frontier`.  That thin route discharges the
Stage-5 strictness content through the canonical-`V`-specialized seam
(`Stage4MatchedAllPairsAdditivityData` + the pivot-retargeting bracket axiom 17
+ the all-pairs-driven strictness theorem), which is the honest residual.

The certificate-body partial discharges below
(`wakkerStep5StrictMonotonicityResidualAtPivot_of_strictMonotonicityCertificate`,
`_of_globalGluingCertificate`, `_of_card_eq_two`) never referenced this axiom
and remain in place. -/

/-- **Partial discharge of obligation 4 (global-certificate restriction).**

The pivot-indexed residue is weaker than the global strict-monotonicity
certificate: the latter proves sum equality for *all* indifferent profiles,
while the residue asks only for those profiles that avoid every pivot-touching
pair.  So the residual follows by direct specialization. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_of_strictMonotonicityCertificate
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ) (j₀ : ι)
    (hpair : AllPairsAdditivityCertificate P V)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hstrict : WakkerStep5StrictMonotonicityCertificate P V hpair hsolv) :
    WakkerStep5StrictMonotonicityResidualAtPivot P V j₀ := by
  intro x y hxy _hres
  exact hstrict x y hxy

/-- **Partial discharge of obligation 4 (global-gluing fragment).**

Under a full `GlobalGluingCertificate P V`, indifference immediately forces
equality of the global additive sums, so the pivot-indexed residual is
discharged without using any pivot-specific combinatorics. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_of_globalGluingCertificate
    {X : ι → Type v} (P : ProductPref X) (V : (i : ι) → X i → ℝ) (j₀ : ι)
    (hglobal : GlobalGluingCertificate P V) :
    WakkerStep5StrictMonotonicityResidualAtPivot P V j₀ := by
  intro x y hxy _hres
  obtain ⟨hxy, hyx⟩ := hxy
  have hle1 : (∑ i, V i (y i)) ≤ ∑ i, V i (x i) := (hglobal x y).mp hxy
  have hle2 : (∑ i, V i (x i)) ≤ ∑ i, V i (y i) := (hglobal y x).mp hyx
  exact le_antisymm hle2 hle1

/-- **Partial discharge of obligation 4 (low-cardinality vacuous fragment).**

When `Fintype.card ι = 2`, the strict-monotonicity sum-equality residue
at any pivot `j₀` is **vacuously true**.  Indeed, the unique
non-pivot coordinate `k ≠ j₀` exhausts `ι` together with `j₀`, so
`({j₀, k} : Set ι) = Set.univ` and hence `Profile.agreeOff {j₀, k} x y`
holds for any `x y`.  The hypothesis
`∀ k ≠ j₀, ¬ Profile.agreeOff ({j₀, k} : Set ι) x y` is therefore
unsatisfiable and the implication closes by contradiction.

This is a real (theorem, not axiom) reduction of obligation 4 in the
two-coordinate degenerate case, with **no** axioms beyond
`[propext, Classical.choice, Quot.sound]`.  The genuine Wakker IV.6
chain content lives in the residual `card ι ≥ 3` regime, which is
what the axiom `wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms`
continues to assert. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_of_card_eq_two
    {X : ι → Type v} (P : ProductPref X) (V : (i : ι) → X i → ℝ) (j₀ : ι)
    (hcard : Fintype.card ι = 2) :
    WakkerStep5StrictMonotonicityResidualAtPivot P V j₀ := by
  intro x y _hxy hres
  exfalso
  -- Extract the unique non-pivot coordinate `k ≠ j₀`.
  have hk_ex : ∃ k : ι, k ≠ j₀ := by
    by_contra hno
    push_neg at hno
    -- If every `i` equals `j₀`, then `Finset.univ = {j₀}`, so card = 1.
    have huniv : (Finset.univ : Finset ι) = {j₀} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro a _
      exact hno a
    have hcard1 : Fintype.card ι = 1 := by
      simp [Fintype.card, huniv]
    omega
  obtain ⟨k, hk⟩ := hk_ex
  -- The hypothesis `¬ Profile.agreeOff ({j₀, k}) x y` fails, because
  -- every `i : ι` lies in `{j₀, k}` (else `{j₀, k, i}` would have card 3,
  -- contradicting `Fintype.card ι = 2`).
  apply hres k hk
  intro i hi
  exfalso
  apply hi
  -- Show `i = j₀ ∨ i = k` by ruling out three distinct elements.
  have hmem : i = j₀ ∨ i = k := by
    by_contra hne
    push_neg at hne
    obtain ⟨hij, hik⟩ := hne
    -- The three indices `j₀`, `k`, `i` are pairwise distinct.
    have hjk_ne : j₀ ≠ k := fun h => hk h.symm
    have hij' : j₀ ≠ i := fun h => hij h.symm
    have hik' : k ≠ i := fun h => hik h.symm
    have hcard3 : ({j₀, k, i} : Finset ι).card = 3 := by
      have hj₀_notin : j₀ ∉ ({k, i} : Finset ι) := by
        simp [hjk_ne, hij']
      have hk_notin : k ∉ ({i} : Finset ι) := by
        simp [hik']
      rw [Finset.card_insert_of_notMem hj₀_notin,
          Finset.card_insert_of_notMem hk_notin, Finset.card_singleton]
    have hge3 : 3 ≤ Fintype.card ι := by
      calc 3 = ({j₀, k, i} : Finset ι).card := hcard3.symm
        _ ≤ Fintype.card ι := Finset.card_le_univ _
    omega
  -- Conclude `i ∈ ({j₀, k} : Set ι)`.
  rcases hmem with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

/-- **Raw-axiom-form discharge of obligation 4 in the two-coordinate case.**

This keeps the full raw-axiom-facing parameter list of
`wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms`, but proves the
target without using the raw hypotheses when `Fintype.card ι = 2`.  The
residual case is impossible: for the unique non-pivot `k`, every profile pair
agrees off `{j₀, k}` because that pair is all of `ι`. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_card_eq_two
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) (V : (i : ι) → X i → ℝ)
    (hcard : Fintype.card ι = 2) :
    WakkerStep5StrictMonotonicityResidualAtPivot P V j₀ := by
  exact wakkerStep5StrictMonotonicityResidualAtPivot_of_card_eq_two P V j₀ hcard

/-! ## 5. `WakkerStep5CoordinateImageCoverageResidualAtPivot` from raw axioms
(`hResCov`)

**Wakker reference:** §IV.2.7 (existence of pivot bracketing value) +
§IV.6 (Step-5 coverage of the value space at the pivot).

**Obligation contents.**  For any profiles `x, y` with
`∑ V (y) ≤ ∑ V (x)` and a fixed pivot `j₀`, exhibit `c : X j₀` such
that the update `x ↦ Function.update x j₀ c` brackets `y` from above:
`x ≽ update x j₀ c ≽ y`.

**Why this is hard.**  This is the *constructive* existence of a
pivot value realizing a given additive gap.  It requires both:

* (Wakker IV.2.7) `RestrictedSolvability` to solve a one-coordinate
  indifference equation at the pivot;
* (Wakker IV.6) coverage: the image `V j₀ '' (X j₀)` must include the
  required gap value, which is precisely the Step-5 coordinate-image
  coverage content for the pivot coordinate. -/

/- **Open obligation 5 — RETIRED (Phase 14).**
Per-pivot coordinate-image coverage residue from the raw axioms, for any `V`.

This was a primitive `axiom`
`wakkerStep5CoordinateImageCoverageResidualAtPivot_from_raw_axioms`.  Like
axiom 4 it was **overstrong** — universally quantified over an arbitrary `V`
the raw axioms cannot constrain — and **never honestly provable** at this
signature (see `RawAxiomDischargersSpec.md` §5A).

It is now deleted.  Its sole consumer was the original end-to-end skeleton
`additiveRep_nonempty_from_raw_axioms`, which (Phase 14) delegates to
`additiveRep_nonempty_from_thin_frontier`.  That thin route discharges the
Stage-5 coverage content through the canonical-`V`-specialized axiom 19
(`allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms`),
which IS the honest residual.

The certificate-body partial discharges below
(`..._of_coordinateImageCoverageCertificate`, `..._of_globalGluingCertificate`)
never referenced this axiom and remain. -/

/-- **Partial discharge of obligation 5 (global-certificate restriction).**

The per-pivot coverage residue is exactly the fixed-pivot specialization of
the global coordinate-image coverage certificate, so it follows immediately by
applying that certificate at the chosen pivot `j₀`. -/
theorem wakkerStep5CoordinateImageCoverageResidualAtPivot_of_coordinateImageCoverageCertificate
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ) (j₀ : ι)
    (hpair : AllPairsAdditivityCertificate P V)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hcov : WakkerStep5CoordinateImageCoverageCertificate P V hpair hsolv) :
    WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀ := by
  intro x y hle
  exact hcov x y j₀ hle

/-- **Partial discharge of obligation 5 (global-gluing fragment).**

Under a full `GlobalGluingCertificate P V`, the per-pivot coverage residue is
immediate: choose `c := x j₀`, so `Function.update x j₀ c = x`, and use the
global gluing equivalence to read off both `x ≽ x` and `x ≽ y` from the
relevant additive inequalities. -/
theorem wakkerStep5CoordinateImageCoverageResidualAtPivot_of_globalGluingCertificate
    {X : ι → Type v} (P : ProductPref X) (V : (i : ι) → X i → ℝ) (j₀ : ι)
    (hglobal : GlobalGluingCertificate P V) :
    WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀ := by
  intro x y hle
  let c : X j₀ := x j₀
  have hself : Function.update x j₀ c = x := by
    funext i
    by_cases hij : i = j₀
    · subst hij
      simp [c]
    · simp [c, Function.update_of_ne hij]
  refine ⟨c, ?_, ?_⟩
  · rw [hself]
    exact (hglobal x x).mpr (le_rfl)
  · rw [hself]
    exact (hglobal x y).mpr hle

/-! ## Thin-frontier scaffold

The five broad `_from_raw_axioms` axioms above mirror the historical C1 input
surface, but the spec document `RawAxiomDischargersSpec.md` identifies a
sharper frontier below them.  The definitions and wrapper theorems in this
section do **not** claim any new mathematics; they simply name the thinner
packages explicitly and show how they feed the already theorem-backed closure
ladder.

The main design choice is:

* obligations 1–3 are thinned by factoring through the actual package already
  consumed by the theorem-backed wrappers (`PairwiseArchimedeanBaseTransport`,
  shared-pivot magnitude/bracketing families, and pivot-hexagon transport);
* obligations 4–5 are thinned by making the dependence on
  `AllPairsAdditivityCertificate P V` explicit, rather than asserting the
  residuals for an arbitrary unrelated `V`. -/

/-- Bundled shared-pivot family of pairwise hexagon certificates.

This is the thin package directly consumed by the theorem-backed wrapper that
assembles `SharedPivotAllPairsStep4MachineryCertificate P j₀`. -/
def SharedPivotHexagonFamilyCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∃ (σⱼ₀ : ProductPref.StandardSequence P j₀),
    Function.Injective σⱼ₀.α ∧
    ∀ k : ι, k ≠ j₀ →
      ∃ (σk : ProductPref.StandardSequence P k),
        Function.Injective σk.α ∧
        PairwiseHexagonStandardSequenceCertificate P j₀ k σⱼ₀ σk

/-- Bundled shared-pivot family of pairwise magnitude/bracketing certificates.

This is the next thinner package below the broad shared-pivot Step-4 frontier:
it asks only for a common pivot sequence plus the expanded pairwise
magnitude/bracketing payload on each `(j₀, k)` slice. -/
def SharedPivotMagnitudeBracketingFamilyCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∃ (σⱼ₀ : ProductPref.StandardSequence P j₀),
    Function.Injective σⱼ₀.α ∧
    ∀ k : ι, k ≠ j₀ →
      ∃ (σk : ProductPref.StandardSequence P k),
        Function.Injective σk.α ∧
        PairwiseMagnitudeBracketingHexagonCertificate P j₀ k σⱼ₀ σk

/-- Bundled shared-pivot family of honest finite-cut Step-4 packages, together
with the explicit pairwise transport into the hexagon layer.

This is the downstream bridge layer for
`PairwiseMagnitudeFiniteCutHexagonCertificate`: each non-pivot slice carries
the honest finite-cut package, and the remaining per-pair seam is named
separately as `PairwiseFiniteCutHexagonTransportCertificate` rather than being
silently folded back into the stronger exact-bracketing frontier. -/
def SharedPivotMagnitudeFiniteCutTransportFamilyCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∃ (σⱼ₀ : ProductPref.StandardSequence P j₀),
    Function.Injective σⱼ₀.α ∧
    ∀ k : ι, k ≠ j₀ →
      ∃ (σk : ProductPref.StandardSequence P k),
        Function.Injective σk.α ∧
        PairwiseMagnitudeFiniteCutHexagonCertificate P j₀ k σⱼ₀ σk ∧
        PairwiseFiniteCutHexagonTransportCertificate P j₀ k σⱼ₀ σk

/-- Explicit shared-pivot standard-sequence data underlying the honest finite-
cut family frontier.

This isolates the sequence-level coherence obligation in the shared-pivot route:
one common pivot sequence together with one non-pivot sequence for each
`k ≠ j₀`, all with injective coordinate maps.  The theorem-backed pairwise
payloads are added separately below. -/
structure SharedPivotStandardSequenceFamilyData {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) where
  σⱼ₀ : ProductPref.StandardSequence P j₀
  hinj_j₀ : Function.Injective σⱼ₀.α
  σk : ∀ k : ι, k ≠ j₀ → ProductPref.StandardSequence P k
  hinj_k : ∀ k : ι, ∀ hk : k ≠ j₀, Function.Injective (σk k hk).α

/-- Pivot-side fragment of the shared-pivot sequence-data frontier.

This isolates the first half of
`SharedPivotStandardSequenceFamilyData`: choose one pivot standard sequence and
record injectivity of its grid map.  The non-pivot family is packaged
separately. -/
structure SharedPivotPivotStandardSequenceData {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) where
  σⱼ₀ : ProductPref.StandardSequence P j₀
  hinj_j₀ : Function.Injective σⱼ₀.α

/-- Strict-preference seed pair on the pivot coordinate.

This isolates the part of the pivot seed package produced directly by
`Essential P j₀`: a base profile together with two pivot values witnessing a
strict first step.  No auxiliary coordinate or reference exchange is needed
yet. -/
structure SharedPivotPivotStrictPreferenceSeedPairData {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) where
  base : Profile X
  a0 : X j₀
  a1 : X j₀
  hweak : P.weakPref (Function.update base j₀ a0) (Function.update base j₀ a1)
  hnotweak : ¬ P.weakPref (Function.update base j₀ a1) (Function.update base j₀ a0)

/-- The strict pivot seed pair is already theorem-backed from essentiality of
the pivot coordinate. -/
noncomputable def sharedPivotPivotStrictPreferenceSeedPairData_of_essential
    {X : ι → Type v} (P : ProductPref X)
    (essential : ∀ i, ProductPref.Essential P i)
    (j₀ : ι) :
    SharedPivotPivotStrictPreferenceSeedPairData P j₀ := by
  classical
  exact Classical.choice <| by
    rcases essential j₀ with ⟨base, a0, a1, hweak, hnotweak⟩
    exact ⟨⟨base, a0, a1, hweak, hnotweak⟩⟩

/-- Pivot seed profile data stripped of the strictness proof payload.

The downstream seed-comparison seams only use the actual profiles built from
`base`, `a0`, and `a1`; they do not inspect the strictness witnesses carried by
`SharedPivotPivotStrictPreferenceSeedPairData`.  This structure names that
smaller data package explicitly. -/
structure SharedPivotPivotSeedProfileData {X : ι → Type v} (j₀ : ι) where
  base : Profile X
  a0 : X j₀
  a1 : X j₀

/-- Forget the strictness proof payload from a strict pivot seed pair. -/
def sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀) :
    SharedPivotPivotSeedProfileData (X := X) j₀ := by
  exact
    { base := hpair.base
      a0 := hpair.a0
      a1 := hpair.a1 }

/-- The seed-profile component is already theorem-backed from essentiality of
the pivot coordinate. -/
noncomputable def sharedPivotPivotSeedProfileData_of_essential
    {X : ι → Type v} (P : ProductPref X)
    (essential : ∀ i, ProductPref.Essential P i)
    (j₀ : ι) :
    SharedPivotPivotSeedProfileData (X := X) j₀ := by
  exact
    sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair P j₀
      (sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀)

/-- Pivot-level choice of a non-pivot coordinate.

This is the actual structural content below the pair-attached coordinate
wrapper: pick only an auxiliary coordinate `k ≠ j₀`, with no dependence on the
strictness witnesses used upstream to choose the pivot seed pair. -/
structure SharedPivotPivotReferenceCoordinateAtPivotData (j₀ : ι) where
  k : ι
  hk : k ≠ j₀

/-- Pair-attached wrapper reusing a pivot-level non-pivot coordinate choice. -/
structure SharedPivotPivotReferenceCoordinateOnStrictPreferenceSeedPairData
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀) where
  k : ι
  hk : k ≠ j₀

/-- Reattach a pivot-level coordinate choice to any fixed strict pivot seed
pair. -/
def sharedPivotPivotReferenceCoordinateOnStrictPreferenceSeedPairData_of_referenceCoordinateAtPivotData
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (hcoord : SharedPivotPivotReferenceCoordinateAtPivotData j₀) :
    SharedPivotPivotReferenceCoordinateOnStrictPreferenceSeedPairData P j₀ hpair := by
  exact
    { k := hcoord.k
      hk := hcoord.hk }

/-- Distinct reference values on a fixed chosen non-pivot coordinate. -/
structure SharedPivotPivotDistinctReferenceValuesOnReferenceCoordinateData
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (hcoord : SharedPivotPivotReferenceCoordinateOnStrictPreferenceSeedPairData P j₀ hpair) where
  r : X hcoord.k
  s : X hcoord.k
  hrs : r ≠ s

/-- Once the non-pivot coordinate is chosen, essentiality of that coordinate
already yields distinct reference values on it. -/
noncomputable def sharedPivotPivotDistinctReferenceValuesOnReferenceCoordinateData_of_essential
    {X : ι → Type v} (P : ProductPref X)
    (essential : ∀ i, ProductPref.Essential P i)
    (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (hcoord : SharedPivotPivotReferenceCoordinateOnStrictPreferenceSeedPairData P j₀ hpair) :
    SharedPivotPivotDistinctReferenceValuesOnReferenceCoordinateData P j₀ hpair hcoord := by
  classical
  exact Classical.choice <| by
    rcases essential hcoord.k with ⟨base, r, s, hweak, hnotweak⟩
    refine ⟨⟨r, s, ?_⟩⟩
    intro hrs
    subst hrs
    exact hnotweak hweak

/-- Auxiliary coordinate and reference exchange chosen relative to a fixed
strict pivot seed pair. -/
structure SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀) where
  k : ι
  hk : k ≠ j₀
  r : X k
  s : X k
  hrs : r ≠ s

/-- Pivot-level reference exchange data stripped of the strict-pair
provenance.

The downstream seed-comparison seams only need the actual reference exchange
`(k, r, s)` with `k ≠ j₀`; they do not inspect how that exchange was attached
to a particular strict pivot seed pair. -/
structure SharedPivotPivotReferenceExchangeAtPivotData {X : ι → Type v}
    (j₀ : ι) where
  k : ι
  hk : k ≠ j₀
  r : X k
  s : X k
  hrs : r ≠ s

/-- Once the non-pivot coordinate is chosen, essentiality of that coordinate
already yields a pivot-level reference exchange. -/
noncomputable def sharedPivotPivotReferenceExchangeAtPivotData_of_coordinateWitness_and_essential
    {X : ι → Type v} (P : ProductPref X)
    (essential : ∀ i, ProductPref.Essential P i)
    (j₀ : ι)
    (hcoord : SharedPivotPivotReferenceCoordinateAtPivotData j₀) :
    SharedPivotPivotReferenceExchangeAtPivotData (X := X) j₀ := by
  classical
  exact Classical.choice <| by
    rcases essential hcoord.k with ⟨base, r, s, hweak, hnotweak⟩
    exact
      ⟨{ k := hcoord.k
         hk := hcoord.hk
         r := r
         s := s
         hrs := by
           intro hrs
           subst hrs
           exact hnotweak hweak }⟩

/-- Forget the strict-pair provenance of a pair-attached reference exchange. -/
def sharedPivotPivotReferenceExchangeAtPivotData_of_referenceExchangeOnStrictPreferenceSeedPairData
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (href : SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair) :
    SharedPivotPivotReferenceExchangeAtPivotData (X := X) j₀ := by
  exact
    { k := href.k
      hk := href.hk
      r := href.r
      s := href.s
      hrs := href.hrs }

/-- Reattach pivot-level reference-exchange data to any fixed strict pivot
seed pair. -/
def sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_of_referenceExchangeAtPivotData
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (href : SharedPivotPivotReferenceExchangeAtPivotData (X := X) j₀) :
    SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair := by
  exact
    { k := href.k
      hk := href.hk
      r := href.r
      s := href.s
      hrs := href.hrs }

/-- Reassemble the full reference-exchange package from a non-pivot coordinate
choice and theorem-backed distinct reference values on that coordinate. -/
def sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_of_coordinateWitness_and_distinctReferenceValues
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (hcoord : SharedPivotPivotReferenceCoordinateOnStrictPreferenceSeedPairData P j₀ hpair)
    (hvals : SharedPivotPivotDistinctReferenceValuesOnReferenceCoordinateData P j₀ hpair hcoord) :
    SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair := by
  exact
    { k := hcoord.k
      hk := hcoord.hk
      r := hvals.r
      s := hvals.s
      hrs := hvals.hrs }

/-- The full reference-exchange package is theorem-backed once the non-pivot
coordinate has been chosen. -/
noncomputable def sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_of_coordinateWitness_and_essential
    {X : ι → Type v} (P : ProductPref X)
    (essential : ∀ i, ProductPref.Essential P i)
    (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (hcoord : SharedPivotPivotReferenceCoordinateOnStrictPreferenceSeedPairData P j₀ hpair) :
    SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair := by
  exact
    sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_of_coordinateWitness_and_distinctReferenceValues
      P j₀ hpair hcoord
      (sharedPivotPivotDistinctReferenceValuesOnReferenceCoordinateData_of_essential
        P essential j₀ hpair hcoord)

/-- The first profile in the descending seed indifference relation attached to
a fixed strict pair and reference exchange. -/
def sharedPivotPivotDescendingSeedInitialProfile_of_seedProfileAndReferenceExchange
  {X : ι → Type v} (j₀ : ι)
  (hseed : SharedPivotPivotSeedProfileData (X := X) j₀)
  (href : SharedPivotPivotReferenceExchangeAtPivotData (X := X) j₀) :
    Profile X :=
  Function.update (Function.update hseed.base j₀ hseed.a0) href.k href.r

/-- The second profile in the descending seed indifference relation attached
to fixed seed-profile and reference-exchange data. -/
def sharedPivotPivotDescendingSeedSuccessorProfile_of_seedProfileAndReferenceExchange
  {X : ι → Type v} (j₀ : ι)
  (hseed : SharedPivotPivotSeedProfileData (X := X) j₀)
  (href : SharedPivotPivotReferenceExchangeAtPivotData (X := X) j₀) :
    Profile X :=
  Function.update (Function.update hseed.base j₀ hseed.a1) href.k href.s

/-- The first profile in the descending seed indifference relation attached to
a fixed strict pair and reference exchange. -/
def sharedPivotPivotDescendingSeedInitialProfile
  {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
  (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
  (href : SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair) :
    Profile X :=
  sharedPivotPivotDescendingSeedInitialProfile_of_seedProfileAndReferenceExchange j₀
    (sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair P j₀ hpair)
    (sharedPivotPivotReferenceExchangeAtPivotData_of_referenceExchangeOnStrictPreferenceSeedPairData
      P j₀ hpair href)

/-- The second profile in the descending seed indifference relation attached
to a fixed strict pair and reference exchange. -/
def sharedPivotPivotDescendingSeedSuccessorProfile
  {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
  (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
  (href : SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair) :
    Profile X :=
  sharedPivotPivotDescendingSeedSuccessorProfile_of_seedProfileAndReferenceExchange j₀
    (sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair P j₀ hpair)
    (sharedPivotPivotReferenceExchangeAtPivotData_of_referenceExchangeOnStrictPreferenceSeedPairData
      P j₀ hpair href)

/-- Forward weak-preference half of the descending seed comparison on the
minimal seed-profile/reference-exchange data.  In the generic API,
`ProductPref.weakPref` is primitive, so this is the honest endpoint of the
decomposition once the irrelevant strict-pair provenance has been stripped
away. -/
def SharedPivotPivotDescendingSeedWeakPreferenceForwardOnSeedProfileAndReferenceExchangeCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hseed : SharedPivotPivotSeedProfileData (X := X) j₀)
    (href : SharedPivotPivotReferenceExchangeAtPivotData (X := X) j₀) :
    Prop :=
  P.weakPref
    (sharedPivotPivotDescendingSeedInitialProfile_of_seedProfileAndReferenceExchange j₀ hseed href)
    (sharedPivotPivotDescendingSeedSuccessorProfile_of_seedProfileAndReferenceExchange j₀ hseed href)

/-- Backward weak-preference half of the descending seed comparison on the
minimal seed-profile/reference-exchange data. -/
def SharedPivotPivotDescendingSeedWeakPreferenceBackwardOnSeedProfileAndReferenceExchangeCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hseed : SharedPivotPivotSeedProfileData (X := X) j₀)
    (href : SharedPivotPivotReferenceExchangeAtPivotData (X := X) j₀) :
    Prop :=
  P.weakPref
    (sharedPivotPivotDescendingSeedSuccessorProfile_of_seedProfileAndReferenceExchange j₀ hseed href)
    (sharedPivotPivotDescendingSeedInitialProfile_of_seedProfileAndReferenceExchange j₀ hseed href)

/-- Forward weak-preference half of the descending seed indifference. -/
def SharedPivotPivotDescendingSeedWeakPreferenceForwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (href : SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair) :
    Prop :=
  P.weakPref
    (sharedPivotPivotDescendingSeedInitialProfile P j₀ hpair href)
    (sharedPivotPivotDescendingSeedSuccessorProfile P j₀ hpair href)

/-- Backward weak-preference half of the descending seed indifference. -/
def SharedPivotPivotDescendingSeedWeakPreferenceBackwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (href : SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair) :
    Prop :=
  P.weakPref
    (sharedPivotPivotDescendingSeedSuccessorProfile P j₀ hpair href)
    (sharedPivotPivotDescendingSeedInitialProfile P j₀ hpair href)

/-- Descending seed indifference for a fixed strict pivot seed pair and fixed
reference exchange. -/
def SharedPivotPivotDescendingSeedIndifferenceOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (href : SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair) :
    Prop :=
  P.indiff
    (sharedPivotPivotDescendingSeedInitialProfile P j₀ hpair href)
    (sharedPivotPivotDescendingSeedSuccessorProfile P j₀ hpair href)

/-- Reattach the forward weak-preference seam from minimal seed-profile /
reference-exchange data to a fixed strict pair and pair-attached reference
exchange. -/
theorem sharedPivotPivotDescendingSeedWeakPreferenceForwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_of_seedProfileAndReferenceExchange
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (href : SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair)
    (hforward :
      SharedPivotPivotDescendingSeedWeakPreferenceForwardOnSeedProfileAndReferenceExchangeCertificate
        P j₀
        (sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair P j₀ hpair)
        (sharedPivotPivotReferenceExchangeAtPivotData_of_referenceExchangeOnStrictPreferenceSeedPairData
          P j₀ hpair href)) :
    SharedPivotPivotDescendingSeedWeakPreferenceForwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
      P j₀ hpair href := by
  simpa [SharedPivotPivotDescendingSeedWeakPreferenceForwardOnSeedProfileAndReferenceExchangeCertificate,
    SharedPivotPivotDescendingSeedWeakPreferenceForwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate,
    sharedPivotPivotDescendingSeedInitialProfile_of_seedProfileAndReferenceExchange,
    sharedPivotPivotDescendingSeedSuccessorProfile_of_seedProfileAndReferenceExchange,
    sharedPivotPivotDescendingSeedInitialProfile,
    sharedPivotPivotDescendingSeedSuccessorProfile,
    sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair,
    sharedPivotPivotReferenceExchangeAtPivotData_of_referenceExchangeOnStrictPreferenceSeedPairData] using hforward

/-- Reattach the backward weak-preference seam from minimal seed-profile /
reference-exchange data to a fixed strict pair and pair-attached reference
exchange. -/
theorem sharedPivotPivotDescendingSeedWeakPreferenceBackwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_of_seedProfileAndReferenceExchange
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (href : SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair)
    (hbackward :
      SharedPivotPivotDescendingSeedWeakPreferenceBackwardOnSeedProfileAndReferenceExchangeCertificate
        P j₀
        (sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair P j₀ hpair)
        (sharedPivotPivotReferenceExchangeAtPivotData_of_referenceExchangeOnStrictPreferenceSeedPairData
          P j₀ hpair href)) :
    SharedPivotPivotDescendingSeedWeakPreferenceBackwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
      P j₀ hpair href := by
  simpa [SharedPivotPivotDescendingSeedWeakPreferenceBackwardOnSeedProfileAndReferenceExchangeCertificate,
    SharedPivotPivotDescendingSeedWeakPreferenceBackwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate,
    sharedPivotPivotDescendingSeedInitialProfile_of_seedProfileAndReferenceExchange,
    sharedPivotPivotDescendingSeedSuccessorProfile_of_seedProfileAndReferenceExchange,
    sharedPivotPivotDescendingSeedInitialProfile,
    sharedPivotPivotDescendingSeedSuccessorProfile,
    sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair,
    sharedPivotPivotReferenceExchangeAtPivotData_of_referenceExchangeOnStrictPreferenceSeedPairData] using hbackward

/-- Reassemble the descending seed indifference from its two one-sided
weak-preference halves. -/
theorem sharedPivotPivotDescendingSeedIndifferenceOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_of_forward_and_backward
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (href : SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair)
    (hforward :
      SharedPivotPivotDescendingSeedWeakPreferenceForwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
        P j₀ hpair href)
    (hbackward :
      SharedPivotPivotDescendingSeedWeakPreferenceBackwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
        P j₀ hpair href) :
    SharedPivotPivotDescendingSeedIndifferenceOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
      P j₀ hpair href := by
  exact ⟨hforward, hbackward⟩

/-- Seed data for theorem-backed construction of the shared pivot sequence.

This is the exact generic input consumed by
`TradeoffMeasurement.extend_to_standard_sequence`, together with the strict
first-step data needed to remember that the resulting pivot sequence starts in
the intended preference direction.  It does **not** yet include the recursive
one-step extension witness or injectivity of the resulting grid. -/
structure SharedPivotPivotStandardSequenceSeedData {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) where
  k : ι
  hk : k ≠ j₀
  base : Profile X
  a0 : X j₀
  a1 : X j₀
  r : X k
  s : X k
  hrs : r ≠ s
  h01 : P.indiff
    (Function.update (Function.update base j₀ a0) k r)
    (Function.update (Function.update base j₀ a1) k s)
  hweak : P.weakPref (Function.update base j₀ a0) (Function.update base j₀ a1)
  hnotweak : ¬ P.weakPref (Function.update base j₀ a1) (Function.update base j₀ a0)

/-- Reassemble the full pivot seed package from a strict seed pair, a chosen
reference exchange on that pair, and the descending seed indifference on the
same data. -/
def sharedPivotPivotStandardSequenceSeedData_of_strictPreferenceSeedPair_referenceExchange_and_descendingSeedIndifference
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀)
    (href : SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair)
    (hindiff :
      SharedPivotPivotDescendingSeedIndifferenceOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
        P j₀ hpair href) :
    SharedPivotPivotStandardSequenceSeedData P j₀ := by
  have h01 :
      P.indiff
        (Function.update (Function.update hpair.base j₀ hpair.a0) href.k href.r)
        (Function.update (Function.update hpair.base j₀ hpair.a1) href.k href.s) := by
    simpa [SharedPivotPivotDescendingSeedIndifferenceOnStrictPreferenceSeedPairAndReferenceExchangeCertificate,
      sharedPivotPivotDescendingSeedInitialProfile, sharedPivotPivotDescendingSeedSuccessorProfile] using hindiff
  exact
    { k := href.k
      hk := href.hk
      base := hpair.base
      a0 := hpair.a0
      a1 := hpair.a1
      r := href.r
      s := href.s
      hrs := href.hrs
      h01 := h01
      hweak := hpair.hweak
      hnotweak := hpair.hnotweak }

/-- One-step extension witness on fixed pivot-seed data.

With the auxiliary coordinate, base profile, reference exchange, and first two
pivot points fixed, this is exactly the recursive successor interface consumed
by `TradeoffMeasurement.extend_to_standard_sequence`. -/
def sharedPivotPivotSeedProfileData_of_standardSequenceSeedData
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀) :
    SharedPivotPivotSeedProfileData (X := X) j₀ := by
  exact
    { base := hseed.base
      a0 := hseed.a0
      a1 := hseed.a1 }

/-- Forget the extra first-step witnesses and retain only the pivot-level
reference exchange carried by a fixed pivot seed package. -/
def sharedPivotPivotReferenceExchangeAtPivotData_of_standardSequenceSeedData
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀) :
    SharedPivotPivotReferenceExchangeAtPivotData (X := X) j₀ := by
  exact
    { k := hseed.k
      hk := hseed.hk
      r := hseed.r
      s := hseed.s
      hrs := hseed.hrs }

/-- One-step extensibility on the smaller seed-profile / reference-exchange
context.

The recursive constructor `extend_to_standard_sequence` does not inspect the
first-step witnesses `h01`, `hweak`, or `hnotweak`; it only needs the base
profile and the reference exchange `(k, r, s)`.  This definition names that
smaller seam explicitly. -/
def SharedPivotPivotOneStepExtensibleOnSeedProfileAndReferenceExchangeCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hseed : SharedPivotPivotSeedProfileData (X := X) j₀)
    (href : SharedPivotPivotReferenceExchangeAtPivotData (X := X) j₀) :
    Prop :=
  ProductPref.OneStepExtensible P j₀ hseed.base href.k href.r href.s

def SharedPivotPivotStandardSequenceExtensionOnSeedCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀) : Prop :=
  ProductPref.OneStepExtensible P j₀ hseed.base hseed.k hseed.r hseed.s

/-- Reattach the smaller seed-profile / reference-exchange extension seam to
any fixed pivot seed data. -/
theorem sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_of_seedProfileAndReferenceExchange
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀)
    (hext :
      SharedPivotPivotOneStepExtensibleOnSeedProfileAndReferenceExchangeCertificate
        P j₀
        (sharedPivotPivotSeedProfileData_of_standardSequenceSeedData P j₀ hseed)
        (sharedPivotPivotReferenceExchangeAtPivotData_of_standardSequenceSeedData P j₀ hseed)) :
    SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀ hseed := by
  simpa [SharedPivotPivotOneStepExtensibleOnSeedProfileAndReferenceExchangeCertificate,
    SharedPivotPivotStandardSequenceExtensionOnSeedCertificate,
    sharedPivotPivotSeedProfileData_of_standardSequenceSeedData,
    sharedPivotPivotReferenceExchangeAtPivotData_of_standardSequenceSeedData] using hext

/-- The theorem-backed pivot standard sequence constructed from fixed seed data
and its one-step extension witness. -/
noncomputable def sharedPivotPivotStandardSequence_of_seedData_and_extension
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀)
    (hext : SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀ hseed) :
    ProductPref.StandardSequence P j₀ := by
  classical
  exact
    Classical.choose
      (WakkerRoadmap.TradeoffMeasurement.extend_to_standard_sequence
        P solvability j₀ hseed.k hseed.hk hseed.base hseed.a0 hseed.a1
        hseed.r hseed.s hseed.hrs hseed.h01 hext)

/-- **Constructor spec for the theorem-backed pivot sequence.**

`sharedPivotPivotStandardSequence_of_seedData_and_extension` is
`Classical.choose` of the existential produced by
`extend_to_standard_sequence`; this lemma is the corresponding
`Classical.choose_spec`, recording that the constructed sequence has the
intended base profile and first two grid points. -/
theorem sharedPivotPivotStandardSequence_of_seedData_and_extension_spec
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀)
    (hext : SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀ hseed) :
    (sharedPivotPivotStandardSequence_of_seedData_and_extension
        P solvability j₀ hseed hext).base = hseed.base ∧
      (sharedPivotPivotStandardSequence_of_seedData_and_extension
        P solvability j₀ hseed hext).α 0 = hseed.a0 ∧
      (sharedPivotPivotStandardSequence_of_seedData_and_extension
        P solvability j₀ hseed hext).α 1 = hseed.a1 := by
  classical
  exact Classical.choose_spec
    (WakkerRoadmap.TradeoffMeasurement.extend_to_standard_sequence
      P solvability j₀ hseed.k hseed.hk hseed.base hseed.a0 hseed.a1
      hseed.r hseed.s hseed.hrs hseed.h01 hext)

/-- **Step-0 strictness of the theorem-backed pivot sequence (from the seed).**

The seed package carries `hweak`/`hnotweak`, which is exactly strict preference
between the base-`a0` and base-`a1` profiles.  Via the constructor spec, this is
precisely `σ.IsStrict` for the constructed pivot sequence — i.e. step-0
strictness is *available from the raw seed* (ultimately from `Essential`), not an
extra assumption. -/
theorem sharedPivotPivotStandardSequence_isStrict_of_seedData
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀)
    (hext : SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀ hseed) :
    (sharedPivotPivotStandardSequence_of_seedData_and_extension
      P solvability j₀ hseed hext).IsStrict := by
  obtain ⟨hbase, h0, h1⟩ :=
    sharedPivotPivotStandardSequence_of_seedData_and_extension_spec
      P solvability j₀ hseed hext
  show P.strict
    (Function.update
      (sharedPivotPivotStandardSequence_of_seedData_and_extension
        P solvability j₀ hseed hext).base j₀
      ((sharedPivotPivotStandardSequence_of_seedData_and_extension
        P solvability j₀ hseed hext).α 0))
    (Function.update
      (sharedPivotPivotStandardSequence_of_seedData_and_extension
        P solvability j₀ hseed hext).base j₀
      ((sharedPivotPivotStandardSequence_of_seedData_and_extension
        P solvability j₀ hseed hext).α 1))
  rw [hbase, h0, h1]
  exact ⟨hseed.hweak, hseed.hnotweak⟩

/-- Injectivity of the theorem-backed pivot grid constructed from fixed seed
data and one-step extension witness. -/
def SharedPivotPivotGridInjectiveOnSeedDataCertificate
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀)
    (hext : SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀ hseed) :
    Prop :=
  Function.Injective
    (sharedPivotPivotStandardSequence_of_seedData_and_extension
      P solvability j₀ hseed hext).α

/-- Reassemble the pivot-side shared standard-sequence data from the theorem-
backed constructor layer plus injectivity of the resulting grid. -/
noncomputable def sharedPivotPivotStandardSequenceData_of_seedData_extension_and_gridInjective
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀)
    (hext : SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀ hseed)
    (hinj : SharedPivotPivotGridInjectiveOnSeedDataCertificate
      P solvability j₀ hseed hext) :
    SharedPivotPivotStandardSequenceData P j₀ := by
  refine
    { σⱼ₀ :=
        sharedPivotPivotStandardSequence_of_seedData_and_extension
          P solvability j₀ hseed hext
      hinj_j₀ := hinj }

/-- Non-pivot family fragment of the shared-pivot sequence-data frontier, with
the pivot payload forgotten.

For each `k ≠ j₀`, choose a standard sequence on `k` and record injectivity of
its grid map.  This is the actual residual content below the full shared-pivot
sequence-data package; no field of the pivot-side data is used here. -/
def SharedPivotNonpivotStandardSequenceFamilyCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ k : ι, ∀ hk : k ≠ j₀,
    ∃ σk : ProductPref.StandardSequence P k, Function.Injective σk.α

/-- **Partial discharge of axiom 13 in `card ι = 1` cardinality.**

When `Fintype.card ι = 1`, the inner `∀ k ≠ j₀` is vacuous: the only
coordinate is `j₀` itself, so no `k ≠ j₀` exists.

This is a real theorem-backed reduction in the degenerate case;
the genuine Wakker §III.4 + §IV.2.6 standard-sequence existence and
injectivity content lives entirely in the residual `card ι ≥ 2` regime. -/
theorem sharedPivotNonpivotStandardSequenceFamilyCertificate_of_card_eq_one
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hcard : Fintype.card ι = 1) :
    SharedPivotNonpivotStandardSequenceFamilyCertificate P j₀ := by
  intro k hk
  exfalso
  -- card = 1 forces ι = {j₀}, so k ≠ j₀ is impossible.
  have h2 : 2 ≤ Fintype.card ι := by
    calc 2 = ({j₀, k} : Finset ι).card := by
            rw [Finset.card_insert_of_notMem
                  (by simpa using Ne.symm hk),
                Finset.card_singleton]
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **Raw-axiom-form discharge of axiom 13 in `card ι = 1` cardinality.** -/
theorem sharedPivotNonpivotStandardSequenceFamilyCertificate_from_raw_axioms_of_card_eq_one
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hcard : Fintype.card ι = 1) :
    SharedPivotNonpivotStandardSequenceFamilyCertificate P j₀ :=
  sharedPivotNonpivotStandardSequenceFamilyCertificate_of_card_eq_one P j₀ hcard

/-- Reattached non-pivot family fragment of the shared-pivot sequence-data
frontier, with the pivot sequence already fixed.

For each `k ≠ j₀`, choose a standard sequence on `k` and record injectivity of
its grid map.  Together with `SharedPivotPivotStandardSequenceData`, this is
exactly the remaining content of `SharedPivotStandardSequenceFamilyData`.
The proposition body does not inspect `hpivot`; the parameter is retained only
so the package slots directly into the final reassembly wrapper. -/
def SharedPivotNonpivotStandardSequenceFamilyOnPivotDataCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpivot : SharedPivotPivotStandardSequenceData P j₀) : Prop :=
  SharedPivotNonpivotStandardSequenceFamilyCertificate P j₀

/-- Reattach the smaller pivot-free non-pivot family seam to any fixed pivot
sequence data. -/
theorem sharedPivotNonpivotStandardSequenceFamilyOnPivotDataCertificate_of_nonpivotFamily
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpivot : SharedPivotPivotStandardSequenceData P j₀)
    (hfamily : SharedPivotNonpivotStandardSequenceFamilyCertificate P j₀) :
    SharedPivotNonpivotStandardSequenceFamilyOnPivotDataCertificate P j₀ hpivot :=
  hfamily

/-- Reassemble the full shared-pivot sequence data from its pivot-side and
non-pivot-side fragments. -/
noncomputable def sharedPivotStandardSequenceFamilyData_of_pivotData_and_nonpivotFamily
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hpivot : SharedPivotPivotStandardSequenceData P j₀)
    (hfamily :
      SharedPivotNonpivotStandardSequenceFamilyOnPivotDataCertificate P j₀ hpivot) :
    SharedPivotStandardSequenceFamilyData P j₀ := by
  classical
  refine
    { σⱼ₀ := hpivot.σⱼ₀
      hinj_j₀ := hpivot.hinj_j₀
      σk := ?_
      hinj_k := ?_ }
  · intro k hk
    exact Classical.choose (hfamily k hk)
  · intro k hk
    exact Classical.choose_spec (hfamily k hk)

/-- Honest per-pair finite-cut Step-4 packages on fixed shared-pivot sequence
data.

This is the first smaller raw-facing obligation below
`SharedPivotMagnitudeFiniteCutTransportFamilyCertificate`: once the common
sequence family has been chosen, each non-pivot slice should carry the honest
`PairwiseMagnitudeFiniteCutHexagonCertificate`. -/
def SharedPivotMagnitudeFiniteCutFamilyOnDataCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) : Prop :=
  ∀ k : ι, ∀ hk : k ≠ j₀,
    PairwiseMagnitudeFiniteCutHexagonCertificate P j₀ k hdata.σⱼ₀ (hdata.σk k hk)

/-- Explicit per-pair transport into the hexagon layer on fixed shared-pivot
sequence data.

This is the second smaller raw-facing obligation below
`SharedPivotMagnitudeFiniteCutTransportFamilyCertificate`: for the same chosen
shared-pivot sequence family, each non-pivot slice must supply the residual
`PairwiseFiniteCutHexagonTransportCertificate`. -/
def SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) : Prop :=
  ∀ k : ι, ∀ hk : k ≠ j₀,
    PairwiseFiniteCutHexagonTransportCertificate P j₀ k hdata.σⱼ₀ (hdata.σk k hk)

/-- **Surjective-grid regression discharge of the finite-cut hexagon transport
family.**

If the shared pivot grid and every chosen non-pivot grid are surjective, the
per-slice finite-cut hexagon transport seam is theorem-backed via
`pairwiseFiniteCutHexagonTransportCertificate_of_surjectiveStandardSequences`.
This keeps the degenerate regression path available at the family level, so the
honest finite-cut hexagon thinning closes outright in the surjective regime. -/
theorem sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_of_surjectiveGrids
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j₀ : ι) (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hsurj_j₀ : Function.Surjective hdata.σⱼ₀.α)
    (hsurj_k : ∀ (k : ι) (hk : k ≠ j₀), Function.Surjective (hdata.σk k hk).α) :
    SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  exact
    pairwiseFiniteCutHexagonTransportCertificate_of_surjectiveStandardSequences
      P (Ne.symm hk) hdata.σⱼ₀ (hdata.σk k hk) hsurj_j₀ (hsurj_k k hk)

/-- Stronger direct hexagon-family target on fixed shared-pivot sequence data.

If this is available, then the transport family is immediate: each transport
implication can simply ignore its finite-cut input and return the already known
hexagon payload on that slice. -/
def SharedPivotHexagonFamilyOnDataCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) : Prop :=
  ∀ k : ι, ∀ hk : k ≠ j₀,
    PairwiseHexagonStandardSequenceCertificate P j₀ k hdata.σⱼ₀ (hdata.σk k hk)

/-- **Partial discharge of axiom 14 in `card ι = 1` cardinality.**

The hexagon family is a per-non-pivot-slice claim, vacuous when
`Fintype.card ι = 1`. -/
theorem sharedPivotHexagonFamilyOnDataCertificate_of_card_eq_one
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hcard : Fintype.card ι = 1) :
    SharedPivotHexagonFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  exfalso
  have h2 : 2 ≤ Fintype.card ι := by
    calc 2 = ({j₀, k} : Finset ι).card := by
            rw [Finset.card_insert_of_notMem
                  (by simpa using Ne.symm hk),
                Finset.card_singleton]
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **Thinning of axiom 14 to a per-slice magnitude-bracketing family.**

The heavy direct hexagon family on the canonical shared-pivot data follows
from a per-slice `PairwiseMagnitudeBracketingHexagonCertificate` on the same
grids, via the existing per-pair reduction
`pairwiseHexagonStandardSequenceCertificate_of_pairwiseMagnitudeBracketingHexagonCertificate`.

Per the spec (§S1), the magnitude-bracketing payload is the easier residual —
obtainable from the Step-4 tradeoff machinery plus a finite-cut interpolation
route — so this replaces the heaviest single seam (the affine-renormalization
hexagon payload) with the lighter bracketing content on each non-pivot slice. -/
theorem sharedPivotHexagonFamilyOnDataCertificate_of_magnitudeBracketingFamily
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hmbh : ∀ (k : ι) (hk : k ≠ j₀),
      PairwiseMagnitudeBracketingHexagonCertificate P j₀ k hdata.σⱼ₀ (hdata.σk k hk)) :
    SharedPivotHexagonFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  exact
    pairwiseHexagonStandardSequenceCertificate_of_pairwiseMagnitudeBracketingHexagonCertificate
      P hk.symm hdata.σⱼ₀ (hdata.σk k hk) (hmbh k hk)

/-- The stronger direct hexagon-family target on fixed data implies the named
finite-cut transport family on that data. -/
theorem sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_of_hexagonFamilyOnDataCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hhex : SharedPivotHexagonFamilyOnDataCertificate P j₀ hdata) :
    SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀ hdata := by
  intro k hk _hfinite
  exact hhex k hk

/-- **Per-slice Step-4 certificate from a grid-normalized slice representation.**

If a utility pair `(Vj, Vk)` is grid-normalized on the two standard-sequence
grids (`Vj (σj.α n) = n`, `Vk (σk.α n) = n`) **and** order-calibrates the
`{j,k}`-slice (`PairwiseSliceRepresentationCertificate`), then the Step-4
tradeoff-machinery certificate holds: it simply returns that pair (the assembly
input is unused).

This is the honest "representation ⟹ Step-4" direction: it exhibits that the
§IV.5 Step-4 core is exactly *possessing a grid-normalized slice representation*
— the irreducible content engine C characterized (Phase 36,
`RawAxiomDischargersHexagon.GridAdditiveSliceRep`).  The converse (constructing
such a representation from the raw axioms) is the genuine §IV.5 residual. -/
theorem pairwiseStep4TradeoffMachineryCertificate_of_gridNormalized_representation
    {X : ι → Type v} (P : ProductPref X) {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (Vj : X j → ℝ) (Vk : X k → ℝ)
    (hnorm : PairwiseGridNormalizationWitness σj σk Vj Vk)
    (hrepr : PairwiseSliceRepresentationCertificate P j k Vj Vk) :
    PairwiseStep4TradeoffMachineryCertificate P j k σj σk :=
  fun _ => ⟨Vj, Vk, hnorm, hrepr⟩

/-- Shared-pivot Step-4 tradeoff-machinery family on fixed shared-pivot data.

This is the first theorem-backed component below the honest finite-cut family
on data: for each non-pivot slice, supply the Step-4 order-calibrated core on
the already chosen shared-pivot grids. -/
def SharedPivotStep4TradeoffFamilyOnDataCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) : Prop :=
  ∀ k : ι, ∀ hk : k ≠ j₀,
    PairwiseStep4TradeoffMachineryCertificate P j₀ k hdata.σⱼ₀ (hdata.σk k hk)

/-- The direct hexagon-family target on fixed shared-pivot data already
contains the Step-4 order-calibrated core on each slice. -/
theorem sharedPivotStep4TradeoffFamilyOnDataCertificate_of_hexagonFamilyOnDataCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hhex : SharedPivotHexagonFamilyOnDataCertificate P j₀ hdata) :
    SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  exact
    pairwiseStep4TradeoffMachineryCertificate_of_pairwiseHexagonStandardSequenceCertificate
      P j₀ k hdata.σⱼ₀ (hdata.σk k hk) (hhex k hk)

/-- **Shared-pivot Step-4 family from a per-slice grid-normalized representation
family.**

The family version of `pairwiseStep4TradeoffMachineryCertificate_of_gridNormalized_representation`:
if every non-pivot slice carries a grid-normalized slice representation on the
chosen shared-pivot grids, the entire shared-pivot Step-4 tradeoff family
follows.  This connects the live §IV.5 Step-4 seam
(`SharedPivotStep4TradeoffFamilyOnDataCertificate`, the heaviest residual) to
engine C's characterized irreducible core: the family is exactly a per-slice
family of grid-additive slice representations (Phase 36
`RawAxiomDischargersHexagon.GridAdditiveSliceRep`).  The genuine §IV.5 residual is
constructing those representations; everything downstream is theorem-backed. -/
theorem sharedPivotStep4TradeoffFamilyOnDataCertificate_of_representationFamily
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hrep : ∀ (k : ι) (hk : k ≠ j₀),
      ∃ Vⱼ₀ : X j₀ → ℝ, ∃ Vk : X k → ℝ,
        PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) Vⱼ₀ Vk ∧
        PairwiseSliceRepresentationCertificate P j₀ k Vⱼ₀ Vk) :
    SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  obtain ⟨Vⱼ₀, Vk, hnorm, hrepr⟩ := hrep k hk
  exact pairwiseStep4TradeoffMachineryCertificate_of_gridNormalized_representation
    P hdata.σⱼ₀ (hdata.σk k hk) Vⱼ₀ Vk hnorm hrepr

/-- **Shared-pivot grid-additive representation family — the single §IV.5
representation residual.**

The named §IV.5 representation-level residual on fixed shared-pivot data: a
**common pivot utility** `V₀ : X j₀ → ℝ` together with, for every non-pivot slice,
a coordinate utility `Vk` such that `(V₀, Vk)` is grid-normalized on the chosen
shared-pivot grids and represents the `{j₀, k}`-slice.

Crucially the *same* `V₀` works for every slice — this is the Wakker §IV.5
common-pivot / common-scale content (the hard part), the representation-level form
of engine C's `GridAdditiveSliceRep` (Phase 36) assembled across all slices on a
shared pivot. -/
def SharedPivotGridAdditiveRepresentationFamily {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) : Prop :=
  ∃ V₀ : X j₀ → ℝ,
    ∀ (k : ι) (hk : k ≠ j₀),
      ∃ Vk : X k → ℝ,
        PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) V₀ Vk ∧
        PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk

/-- **The Step-4 family from the shared-pivot grid-additive representation
family.**

The single representation residual discharges obligation 14 (the heaviest §IV.5
seam): project the common-pivot representation family to the per-slice
representation family consumed by
`sharedPivotStep4TradeoffFamilyOnDataCertificate_of_representationFamily`.  Unlike
that per-slice form, this uses **one** `V₀` for all slices — the genuine §IV.5
common-pivot content. -/
theorem sharedPivotStep4TradeoffFamilyOnDataCertificate_of_gridAdditiveRepresentationFamily
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hrep : SharedPivotGridAdditiveRepresentationFamily P j₀ hdata) :
    SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata := by
  obtain ⟨V₀, hslices⟩ := hrep
  refine sharedPivotStep4TradeoffFamilyOnDataCertificate_of_representationFamily
    P j₀ hdata ?_
  intro k hk
  obtain ⟨Vk, hnorm, hrepr⟩ := hslices k hk
  exact ⟨V₀, Vk, hnorm, hrepr⟩

/-- **The pivot-slice matches for A1 from the shared-pivot grid-additive
representation family.**

The *same* representation family also supplies the `hMatch` family that A1
(`allPairsAdditivityCertificate_of_pivotSliceMatched_V`) consumes: a global
utility `V` whose pivot slices `(V j₀, V k)` represent each `{j₀, k}`-slice.  So
the single representation residual feeds **both** the Step-4 core (above) and the
A1 pivot-slice matches — it is the one §IV.5 representation object the whole
pivot-side assembly needs.

The global `V` is assembled from `V₀` at `j₀` and the per-slice `Vk` elsewhere
(choosing representatives); on each pivot slice the representation holds by
construction. -/
theorem pivotSliceMatch_of_gridAdditiveRepresentationFamily
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hrep : SharedPivotGridAdditiveRepresentationFamily P j₀ hdata) :
    ∃ V : (i : ι) → X i → ℝ,
      ∀ (k : ι), k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k) := by
  classical
  obtain ⟨V₀, hslices⟩ := hrep
  -- Choose a representing `Vk` per non-pivot slice; assemble the global `V`.
  refine ⟨fun i => if h : i = j₀ then h ▸ V₀ else
    (if hk : i ≠ j₀ then (hslices i hk).choose else fun _ => 0), ?_⟩
  intro k hk
  have hVj₀ : (fun i => if h : i = j₀ then h ▸ V₀ else
      (if hk : i ≠ j₀ then (hslices i hk).choose else fun _ => 0)) j₀ = V₀ := by
    simp
  have hVk : (fun i => if h : i = j₀ then h ▸ V₀ else
      (if hk : i ≠ j₀ then (hslices i hk).choose else fun _ => 0)) k
      = (hslices k hk).choose := by
    simp only []
    rw [dif_neg hk, dif_pos hk]
  rw [hVj₀, hVk]
  exact ((hslices k hk).choose_spec).2

/-- **The Step-4 order-calibrated core already yields the full hexagon family.**

The per-slice hexagon certificate `PairwiseHexagonStandardSequenceCertificate`
is, by definition, `AssemblyInput → ∃ Vj Vk, gridNorm ∧ sliceInterp ∧
hexagonProp`, where `hexagonProp = PairwiseOrderCalibrationCertificate`.  The
Step-4 machinery certificate supplies `∃ Vj Vk, gridNorm ∧ orderCalib` on the
*same* utilities, and the **slice-interpolation** conjunct is independent of the
chosen utilities and already present in the assembly input (theorem-backed from
`RestrictedSolvability`).  So the Step-4 family alone reconstructs the full
hexagon family — the slice-interpolation half is not extra primitive content.

This is the reverse of
`sharedPivotStep4TradeoffFamilyOnDataCertificate_of_hexagonFamilyOnDataCertificate`,
showing the two families are inter-derivable; the genuine residual is therefore
the strictly-leaner Step-4 order-calibration core, not the bundled hexagon. -/
theorem sharedPivotHexagonFamilyOnDataCertificate_of_step4TradeoffFamily
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (htradeoff : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata) :
    SharedPivotHexagonFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  exact
    pairwiseOrderCalibrationTheoremCertificate_of_pairwiseStep4TradeoffMachineryCertificate
      P j₀ k hdata.σⱼ₀ (hdata.σk k hk) (htradeoff k hk)

/-- Shared-pivot finite-cut interpolation family on fixed shared-pivot data.

This is the second theorem-backed component below the honest finite-cut family
on data: for each non-pivot slice, supply the finite-cut/interpolation theorem
certificate on the same chosen shared-pivot grids. -/
def SharedPivotFiniteCutInterpolationFamilyOnDataCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) : Prop :=
  ∀ k : ι, ∀ hk : k ≠ j₀,
    PairwiseFiniteCutInterpolationTheoremCertificate P j₀ k hdata.σⱼ₀ (hdata.σk k hk)

/-- Shared-pivot **interpolation/extension** family on fixed shared-pivot data.

This is the genuinely residual half of
`SharedPivotFiniteCutInterpolationFamilyOnDataCertificate` once the finite-cut
**coverage** half is supplied separately (it is theorem-backed from the
base-transport obligation 6 on each slice).  For each non-pivot slice `(j₀, k)`
it asks only for the per-slice
`PairwiseInterpolationExtensionCertificate` — Wakker's continuity/interpolation
step that fills a finite cut with an indifferent slice-shaped witness.

This is strictly weaker than axiom 15: it drops the coverage conjunct, which is
exactly the content the base-transport obligation 6 already supplies. -/
def SharedPivotInterpolationExtensionFamilyOnDataCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) : Prop :=
  ∀ k : ι, ∀ hk : k ≠ j₀,
    PairwiseInterpolationExtensionCertificate P j₀ k hdata.σⱼ₀ (hdata.σk k hk)

/-- **Reduction of axiom 15 to base-transport coverage + the interpolation
seam.**

The per-slice finite-cut *interpolation theorem* certificate is, by definition,
`∀ Vj Vk, gridNorm → orderCalib → (finite-cut coverage ∧ interpolation
extension)`.  Neither the coverage nor the interpolation-extension conjunct
depends on the utility inputs `Vj, Vk`, so the whole family follows from:

* the per-slice **finite-cut coverage** — theorem-backed from the base-transport
  obligation 6 via
  `pairwiseFiniteCutCoverageCertificate_of_archimedean_and_baseTransport`; and
* the per-slice **interpolation/extension** family seam
  (`SharedPivotInterpolationExtensionFamilyOnDataCertificate`).

This realizes spec §2F: the coverage content of the finite-cut family is *not* a
new primitive; it reuses the pairwise obligation-6 infrastructure, leaving only
the interpolation/extension family as the genuine residual seam. -/
theorem sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_of_coverage_and_interpolationExtension
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (j₀ : ι) (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hcover : ∀ k : ι, ∀ hk : k ≠ j₀,
      PairwiseFiniteCutCoverageCertificate hdata.σⱼ₀ (hdata.σk k hk))
    (hinterp : SharedPivotInterpolationExtensionFamilyOnDataCertificate P j₀ hdata) :
    SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀ hdata := by
  intro k hk _Vj _Vk _hgrid _hcal
  exact ⟨hcover k hk, hinterp k hk⟩

/-- **Partial discharge of the interpolation-extension family seam in
`card ι = 1`.**

The interpolation-extension family is a per-non-pivot-slice claim, vacuous when
`Fintype.card ι = 1` (no `k ≠ j₀` exists).  Mirrors the `card_eq_one` discharge
of the full finite-cut interpolation family. -/
theorem sharedPivotInterpolationExtensionFamilyOnDataCertificate_of_card_eq_one
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hcard : Fintype.card ι = 1) :
    SharedPivotInterpolationExtensionFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  exfalso
  have h2 : 2 ≤ Fintype.card ι := by
    calc 2 = ({j₀, k} : Finset ι).card := by
            rw [Finset.card_insert_of_notMem
                  (by simpa using Ne.symm hk),
                Finset.card_singleton]
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **Surjective-regime discharge of the interpolation-extension family seam.**

When every chosen shared-pivot grid is surjective, the per-slice
interpolation/extension certificate is theorem-backed via
`pairwiseInterpolationExtensionCertificate_of_surjectiveStandardSequences`
(take `z := target`), so the whole seam follows without any primitive raw
content. -/
theorem sharedPivotInterpolationExtensionFamilyOnDataCertificate_of_surjectiveGrids
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) :
    SharedPivotInterpolationExtensionFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  exact
    pairwiseInterpolationExtensionCertificate_of_surjectiveStandardSequences
      P hdata.σⱼ₀ (hdata.σk k hk)

/-- **Partial discharge of axiom 15 in `card ι = 1` cardinality.**

The finite-cut interpolation family is a per-non-pivot-slice claim,
vacuous when `Fintype.card ι = 1`. -/
theorem sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_of_card_eq_one
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hcard : Fintype.card ι = 1) :
    SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  exfalso
  have h2 : 2 ≤ Fintype.card ι := by
    calc 2 = ({j₀, k} : Finset ι).card := by
            rw [Finset.card_insert_of_notMem
                  (by simpa using Ne.symm hk),
                Finset.card_singleton]
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **Surjective-regime discharge of the finite-cut interpolation family.**

When every chosen shared-pivot grid is surjective, the per-slice finite-cut
interpolation theorem certificate is theorem-backed via
`pairwiseFiniteCutInterpolationTheoremCertificate_of_surjectiveStandardSequences`,
so the whole family follows without any primitive raw seam.  This is the
finite-cut interpolation analogue of
`sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_of_surjectiveGrids`,
and together they close the spec §S2.3 honest finite-cut family outright in the
surjective-grid regime. -/
theorem sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_of_surjectiveGrids
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hsurj_j₀ : Function.Surjective hdata.σⱼ₀.α)
    (hsurj_k : ∀ (k : ι) (hk : k ≠ j₀), Function.Surjective (hdata.σk k hk).α) :
    SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  exact
    pairwiseFiniteCutInterpolationTheoremCertificate_of_surjectiveStandardSequences
      P (Ne.symm hk) hdata.σⱼ₀ (hdata.σk k hk) hsurj_j₀ (hsurj_k k hk)

/-- Reassemble the honest finite-cut family on fixed shared-pivot data from
the Step-4 tradeoff family and the finite-cut interpolation family. -/
theorem sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_of_step4Tradeoff_and_finiteCutInterpolation
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j₀ : ι) (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (htradeoff : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata)
    (hcut : SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀ hdata) :
    SharedPivotMagnitudeFiniteCutFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  exact
    pairwiseMagnitudeFiniteCutHexagonCertificate_of_pairwiseStep4TradeoffMachineryCertificate_and_finiteCutInterpolation
      P hk.symm hdata.σⱼ₀ (hdata.σk k hk) (hcut k hk) (htradeoff k hk)

/-- **Honest finite-cut thinning of axiom 14.**

The direct hexagon family on the canonical shared-pivot data follows from the
*three honest finite-cut components* on each non-pivot slice, with no recourse
to the exact-grid `PairwiseArchimedeanBracketingTheoremCertificate` overask:

* the Step-4 order-calibrated tradeoff core (`SharedPivotStep4TradeoffFamilyOnDataCertificate`);
* the finite-cut/interpolation theorem family (`SharedPivotFiniteCutInterpolationFamilyOnDataCertificate`);
* the residual per-slice finite-cut hexagon transport seam
  (`SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate`).

The first two assemble into the weaker
`PairwiseMagnitudeFiniteCutHexagonCertificate` on each slice (avoiding the
exact-grid bracketing claim known to be too strong in the non-surjective
one-sided case); the transport seam then lifts that honest finite-cut package
to the full `PairwiseHexagonStandardSequenceCertificate`.

This is the preferred (spec §S1) decomposition of the hexagon family: it
isolates the genuine residual as exactly the finite-cut transport seam, rather
than carrying the heavy affine-renormalization bracketing payload. -/
theorem sharedPivotHexagonFamilyOnDataCertificate_of_step4Tradeoff_finiteCutInterpolation_and_transport
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j₀ : ι) (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (htradeoff : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata)
    (hcut : SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀ hdata)
    (htransport :
      SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀ hdata) :
    SharedPivotHexagonFamilyOnDataCertificate P j₀ hdata := by
  intro k hk
  have hfinite :
      PairwiseMagnitudeFiniteCutHexagonCertificate P j₀ k hdata.σⱼ₀ (hdata.σk k hk) :=
    pairwiseMagnitudeFiniteCutHexagonCertificate_of_pairwiseStep4TradeoffMachineryCertificate_and_finiteCutInterpolation
      P hk.symm hdata.σⱼ₀ (hdata.σk k hk) (hcut k hk) (htradeoff k hk)
  exact
    pairwiseHexagonStandardSequenceCertificate_of_pairwiseMagnitudeFiniteCutHexagonCertificate_and_transport
      P hdata.σⱼ₀ (hdata.σk k hk) hfinite (htransport k hk)

/-- **Surjective-regime closure of the honest finite-cut hexagon family.**

In the surjective-grid regime the residual transport seam is no longer needed:
combining the surjective-grid transport discharge
(`sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_of_surjectiveGrids`)
with the three-component honest finite-cut thinning collapses the hexagon
family to *just two* honest inputs — the Step-4 order-calibrated tradeoff core
and the finite-cut/interpolation family — plus surjectivity of every chosen
grid.  This closes the spec §S1 finite-cut hexagon thinning outright whenever
the standard-sequence grids are surjective, leaving the genuine residual
confined to the non-surjective one-sided case. -/
theorem sharedPivotHexagonFamilyOnDataCertificate_of_step4Tradeoff_finiteCutInterpolation_and_surjectiveGrids
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j₀ : ι) (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (htradeoff : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata)
    (hcut : SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀ hdata)
    (hsurj_j₀ : Function.Surjective hdata.σⱼ₀.α)
    (hsurj_k : ∀ (k : ι) (hk : k ≠ j₀), Function.Surjective (hdata.σk k hk).α) :
    SharedPivotHexagonFamilyOnDataCertificate P j₀ hdata :=
  sharedPivotHexagonFamilyOnDataCertificate_of_step4Tradeoff_finiteCutInterpolation_and_transport
    P j₀ hdata htradeoff hcut
    (sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_of_surjectiveGrids
      P j₀ hdata hsurj_j₀ hsurj_k)

/-- **Surjective-regime closure of the hexagon family from the Step-4 core
alone.**

Now that the finite-cut/interpolation family is itself theorem-backed in the
surjective-grid regime
(`sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_of_surjectiveGrids`),
the surjective-regime hexagon family collapses to *just one* honest input — the
Step-4 order-calibrated tradeoff core — plus surjectivity of every chosen grid.
Both the finite-cut interpolation half and the transport seam are discharged
internally from surjectivity, isolating the genuine remaining content as
exactly the per-slice Step-4 tradeoff machinery (the order-calibration core that
no surjectivity argument supplies). -/
theorem sharedPivotHexagonFamilyOnDataCertificate_of_step4Tradeoff_and_surjectiveGrids
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j₀ : ι) (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (htradeoff : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata)
    (hsurj_j₀ : Function.Surjective hdata.σⱼ₀.α)
    (hsurj_k : ∀ (k : ι) (hk : k ≠ j₀), Function.Surjective (hdata.σk k hk).α) :
    SharedPivotHexagonFamilyOnDataCertificate P j₀ hdata :=
  sharedPivotHexagonFamilyOnDataCertificate_of_step4Tradeoff_finiteCutInterpolation_and_surjectiveGrids
    P j₀ hdata htradeoff
    (sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_of_surjectiveGrids
      P j₀ hdata hsurj_j₀ hsurj_k)
    hsurj_j₀ hsurj_k

/-- Reassemble the bundled shared-pivot finite-cut bridge family from its
three smaller components: shared sequence data, honest finite-cut slice
packages, and explicit per-pair transport. -/
theorem sharedPivotMagnitudeFiniteCutTransportFamilyCertificate_of_data_and_components
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hfinite : SharedPivotMagnitudeFiniteCutFamilyOnDataCertificate P j₀ hdata)
    (htransport :
      SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀ hdata) :
    SharedPivotMagnitudeFiniteCutTransportFamilyCertificate P j₀ := by
  refine ⟨hdata.σⱼ₀, hdata.hinj_j₀, ?_⟩
  intro k hk
  exact ⟨hdata.σk k hk, hdata.hinj_k k hk, hfinite k hk, htransport k hk⟩

/-- Pivot-hexagon transport package.

For any two non-pivot coordinates `j, k`, if the pivot slices `(j₀, j)` and
`(j₀, k)` are already represented by the fixed family `V`, then the `{j, k}`
slice is represented as well.  This is the thin transport-shaped frontier below
`NonPivotPairAdditivityCertificate P V j₀`. -/
def PivotHexagonTransportCertificate {X : ι → Type v}
    (P : ProductPref X) (V : (i : ι) → X i → ℝ) (j₀ : ι) : Prop :=
  ∀ j k : ι, j ≠ j₀ → k ≠ j₀ → j ≠ k →
    PairwiseSliceRepresentationCertificate P j₀ j (V j₀) (V j) →
    PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k) →
    PairwiseSliceRepresentationCertificate P j k (V j) (V k)

/-- Local two-pivot-slice transport package.

This removes the unnecessary ambient family `V` from
`PivotHexagonTransportCertificate`: each application only uses a common pivot
utility `V₀` together with two slice utilities `Vj`, `Vk` certifying the pivot
slices `(j₀, j)` and `(j₀, k)`.  The broader ambient-`V` wrapper is recovered
below by reattaching these three functions to a chosen family `V`. -/
def TwoPivotSliceTransportCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ j k : ι, j ≠ j₀ → k ≠ j₀ → j ≠ k →
    ∀ {V₀ : X j₀ → ℝ} {Vj : X j → ℝ} {Vk : X k → ℝ},
      PairwiseSliceRepresentationCertificate P j₀ j V₀ Vj →
      PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk →
      PairwiseSliceRepresentationCertificate P j k Vj Vk

/-- **Forward half of the two-pivot-slice transport seam.**

The `→` direction of the output slice representation: from the two pivot slices
with a common pivot utility, conclude that on the `{j, k}`-slice
`weakPref x y` *implies* the additive-score inequality `Vⱼ(y)+Vₖ(y) ≤
Vⱼ(x)+Vₖ(x)`.  Strictly weaker than the full biconditional transport. -/
def TwoPivotSliceTransportForwardCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ j k : ι, j ≠ j₀ → k ≠ j₀ → j ≠ k →
    ∀ {V₀ : X j₀ → ℝ} {Vj : X j → ℝ} {Vk : X k → ℝ},
      PairwiseSliceRepresentationCertificate P j₀ j V₀ Vj →
      PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk →
      ∀ x y : Profile X, Profile.agreeOff ({j, k} : Set ι) x y →
        P.weakPref x y → Vj (y j) + Vk (y k) ≤ Vj (x j) + Vk (x k)

/-- **Backward half of the two-pivot-slice transport seam.**

The `←` direction of the output slice representation: the additive-score
inequality *implies* `weakPref x y` on the `{j, k}`-slice.  Strictly weaker than
the full biconditional transport. -/
def TwoPivotSliceTransportBackwardCertificate {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ j k : ι, j ≠ j₀ → k ≠ j₀ → j ≠ k →
    ∀ {V₀ : X j₀ → ℝ} {Vj : X j → ℝ} {Vk : X k → ℝ},
      PairwiseSliceRepresentationCertificate P j₀ j V₀ Vj →
      PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk →
      ∀ x y : Profile X, Profile.agreeOff ({j, k} : Set ι) x y →
        Vj (y j) + Vk (y k) ≤ Vj (x j) + Vk (x k) → P.weakPref x y

/-- **Conjunctive two-pivot-slice transport from its forward and backward
halves (theorem-backed assembly).**

`PairwiseSliceRepresentationCertificate` is the biconditional `weakPref ↔
score-inequality`, so the full transport seam follows from the two strictly
weaker directional half-seams. -/
theorem twoPivotSliceTransportCertificate_of_forward_and_backward
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hfwd : TwoPivotSliceTransportForwardCertificate P j₀)
    (hbwd : TwoPivotSliceTransportBackwardCertificate P j₀) :
    TwoPivotSliceTransportCertificate P j₀ := by
  intro j k hj hk hjk V₀ Vj Vk hslice_j hslice_k x y hxy
  exact ⟨hfwd j k hj hk hjk hslice_j hslice_k x y hxy,
         hbwd j k hj hk hjk hslice_j hslice_k x y hxy⟩

/-- Reattach the local two-pivot-slice transport seam to an ambient matched
utility family `V`. -/
theorem pivotHexagonTransportCertificate_of_twoPivotSliceTransportCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (htransport : TwoPivotSliceTransportCertificate P j₀)
    (V : (i : ι) → X i → ℝ) :
    PivotHexagonTransportCertificate P V j₀ := by
  intro j k hj hk hjk hslice_j hslice_k
  exact htransport j k hj hk hjk hslice_j hslice_k

/-- **Pivot coordinate-image coverage family (the §IV.6 transport residual).**

The certificate-family form of the §IV.6 pivot solvability residual isolated in
`RawAxiomDischargersHexagon.twoPivotSliceTransport` (Phase 38).  For every
non-pivot pair `(j, k)` and every pivot/`j`-slice utility pair `(V₀, Vj)`
certified on the `(j₀, j)`-slice, the pivot utility `V₀` can compensate any
`j`-coordinate utility difference: for any pivot anchor `p` and `j`-values
`a, b`, some pivot value `q` realizes `V₀ q = V₀ p + Vj a − Vj b`.

This is Wakker's pivot coordinate-image coverage / solvability content — exactly
what two-pivot transport consumes and no more.  It is the **same** coverage
family as the §IV.5 Step-5 residual (`WakkerStep5CoordinateImageCoverageResidualAtPivot`,
obligation 5) and the engine-C `PivotCompensatesJ` (Phase 38), unifying the three
coverage frontiers. -/
def TwoPivotSliceTransportCoverageResidual {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ j k : ι, j ≠ j₀ → k ≠ j₀ → j ≠ k →
    ∀ {V₀ : X j₀ → ℝ} {Vj : X j → ℝ} {Vk : X k → ℝ},
      PairwiseSliceRepresentationCertificate P j₀ j V₀ Vj →
      PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk →
      RawAxiomDischargersHexagon.PivotCompensatesJ (X := X) V₀ Vj

/-- **Two-pivot-slice transport from the pivot coverage residual (theorem-backed
via engine C).**

The full conjunctive transport seam (axiom 16) is **theorem-backed** from the
single pivot coordinate-image coverage residual, by routing each non-pivot pair
through the engine-C transport `RawAxiomDischargersHexagon.twoPivotSliceTransport`
(Phase 38).  This retires both directional half-axioms (16a/16b) in favor of the
one coverage residual — the same solvability content as obligations 3 and 5.

Audit: `[propext, Classical.choice, Quot.sound]` (no `_from_raw_axioms`
dependency; the engine-C transport is fully proved). -/
theorem twoPivotSliceTransportCertificate_of_coverageResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j₀ : ι)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀) :
    TwoPivotSliceTransportCertificate P j₀ := by
  intro j k hj hk hjk V₀ Vj Vk hslice_j hslice_k
  exact RawAxiomDischargersHexagon.twoPivotSliceTransport
    P (Ne.symm hj) (Ne.symm hk) hjk V₀ Vj Vk hslice_j hslice_k
    (hcov j k hj hk hjk hslice_j hslice_k)

/-- **Forward transport half from the pivot coverage residual.**

Projects the coverage-backed full transport onto its forward (`→`) direction,
theorem-backing axiom 16a from the single coverage residual. -/
theorem twoPivotSliceTransportForwardCertificate_of_coverageResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j₀ : ι)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀) :
    TwoPivotSliceTransportForwardCertificate P j₀ := by
  intro j k hj hk hjk V₀ Vj Vk hslice_j hslice_k x y hxy hpref
  exact (twoPivotSliceTransportCertificate_of_coverageResidual P j₀ hcov
    j k hj hk hjk hslice_j hslice_k x y hxy).mp hpref

/-- **Backward transport half from the pivot coverage residual.**

Projects the coverage-backed full transport onto its backward (`←`) direction,
theorem-backing axiom 16b from the single coverage residual. -/
theorem twoPivotSliceTransportBackwardCertificate_of_coverageResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j₀ : ι)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀) :
    TwoPivotSliceTransportBackwardCertificate P j₀ := by
  intro j k hj hk hjk V₀ Vj Vk hslice_j hslice_k x y hxy hscore
  exact (twoPivotSliceTransportCertificate_of_coverageResidual P j₀ hcov
    j k hj hk hjk hslice_j hslice_k x y hxy).mpr hscore

/-- **Partial discharge of axiom 16 in low cardinality.**

When `Fintype.card ι ≤ 2`, there cannot be three pairwise distinct
coordinates `j₀, j, k`, so the universally quantified body of
`TwoPivotSliceTransportCertificate` is **vacuous**.

This is a real (theorem, not axiom) reduction of axiom 16 in the
degenerate small-coordinate case, with **no** axioms beyond
`[propext, Classical.choice, Quot.sound]`.  The genuine Wakker IV.6
two-pivot Thomsen transport content lives entirely in the residual
`card ι ≥ 3` regime, which is what the axiom
`twoPivotSliceTransportCertificate_from_raw_axioms` continues to assert. -/
theorem twoPivotSliceTransportCertificate_of_card_le_two
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hcard : Fintype.card ι ≤ 2) :
    TwoPivotSliceTransportCertificate P j₀ := by
  intro j k hj hk hjk _V₀ _Vj _Vk _hslice_j _hslice_k
  exfalso
  -- The three indices `j₀`, `j`, `k` are pairwise distinct, hence form a
  -- three-element `Finset`, which forces `Fintype.card ι ≥ 3`.
  have hcard3 : ({j₀, j, k} : Finset ι).card = 3 := by
    have hj₀_notin : j₀ ∉ ({j, k} : Finset ι) := by
      simp [Ne.symm hj, Ne.symm hk]
    have hj_notin : j ∉ ({k} : Finset ι) := by simp [hjk]
    rw [Finset.card_insert_of_notMem hj₀_notin,
        Finset.card_insert_of_notMem hj_notin, Finset.card_singleton]
  have hge3 : 3 ≤ Fintype.card ι := by
    calc 3 = ({j₀, j, k} : Finset ι).card := hcard3.symm
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **Raw-axiom-form discharge of axiom 16 in low cardinality.**

Keeps the full raw-axiom-facing parameter list of
`twoPivotSliceTransportCertificate_from_raw_axioms`, but proves the target
without using any of those raw hypotheses when `Fintype.card ι ≤ 2`. -/
theorem twoPivotSliceTransportCertificate_from_raw_axioms_of_card_le_two
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hcard : Fintype.card ι ≤ 2) :
    TwoPivotSliceTransportCertificate P j₀ :=
  twoPivotSliceTransportCertificate_of_card_le_two P j₀ hcard

/-- **Partial discharge of the forward transport half-seam (16a) in low
cardinality.**  When `Fintype.card ι ≤ 2` there are no three pairwise distinct
coordinates `j₀, j, k`, so the forward seam is vacuous.  Mirrors the
`card_le_two` discharge of the full transport certificate. -/
theorem twoPivotSliceTransportForwardCertificate_of_card_le_two
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hcard : Fintype.card ι ≤ 2) :
    TwoPivotSliceTransportForwardCertificate P j₀ := by
  intro j k hj hk hjk _V₀ _Vj _Vk _hslice_j _hslice_k _x _y _hxy
  exfalso
  have hcard3 : ({j₀, j, k} : Finset ι).card = 3 := by
    have hj₀_notin : j₀ ∉ ({j, k} : Finset ι) := by
      simp [Ne.symm hj, Ne.symm hk]
    have hj_notin : j ∉ ({k} : Finset ι) := by simp [hjk]
    rw [Finset.card_insert_of_notMem hj₀_notin,
        Finset.card_insert_of_notMem hj_notin, Finset.card_singleton]
  have hge3 : 3 ≤ Fintype.card ι := by
    calc 3 = ({j₀, j, k} : Finset ι).card := hcard3.symm
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **Partial discharge of the backward transport half-seam (16b) in low
cardinality.**  Dual of the forward discharge: vacuous when
`Fintype.card ι ≤ 2`. -/
theorem twoPivotSliceTransportBackwardCertificate_of_card_le_two
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hcard : Fintype.card ι ≤ 2) :
    TwoPivotSliceTransportBackwardCertificate P j₀ := by
  intro j k hj hk hjk _V₀ _Vj _Vk _hslice_j _hslice_k _x _y _hxy
  exfalso
  have hcard3 : ({j₀, j, k} : Finset ι).card = 3 := by
    have hj₀_notin : j₀ ∉ ({j, k} : Finset ι) := by
      simp [Ne.symm hj, Ne.symm hk]
    have hj_notin : j ∉ ({k} : Finset ι) := by simp [hjk]
    rw [Finset.card_insert_of_notMem hj₀_notin,
        Finset.card_insert_of_notMem hj_notin, Finset.card_singleton]
  have hge3 : 3 ≤ Fintype.card ι := by
    calc 3 = ({j₀, j, k} : Finset ι).card := hcard3.symm
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- Consumer-shaped A1 output package.

This is the single tuple actually fixed downstream after the Stage-4 A1
assembly: a chosen pivot `j₀`, a chosen global utility family `V`, the pivot-
slice matches for that `V`, and the assembled all-pairs additive surface.
The Stage-5 thin frontiers below only need to hold on this chosen package, not
for an arbitrary ambient `V`. -/
structure Stage4MatchedAllPairsAdditivityData {X : ι → Type v}
    (P : ProductPref X) where
  j₀ : ι
  V : (i : ι) → X i → ℝ
  hMatch : ∀ k : ι, k ≠ j₀ →
    PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)
  hpair : AllPairsAdditivityCertificate P V

/-- Fix one A1 output package from Stage-4 data and a cross-pair residual. -/
noncomputable def stage4MatchedAllPairsAdditivityData_of_stage4Data_and_cross
    {X : ι → Type v} (P : ProductPref X)
    (hStage4 : WakkerStage4PivotSliceRepresentationData P)
    (hCross : ∀ j₀ : ι, ∀ (V : (i : ι) → X i → ℝ),
      (∀ k : ι, k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) →
      NonPivotPairAdditivityCertificate P V j₀) :
    Stage4MatchedAllPairsAdditivityData P := by
  classical
  let hA1 :=
    allPairsAdditivityCertificate_of_stage4PivotSliceRepresentationData
      hStage4 hCross
  exact
    { j₀ := Classical.choose hA1
      V := Classical.choose (Classical.choose_spec hA1)
      hMatch := (Classical.choose_spec (Classical.choose_spec hA1)).1
      hpair := (Classical.choose_spec (Classical.choose_spec hA1)).2 }

/-- Thin Stage-5 strictness frontier.

Rather than asserting `WakkerStep5StrictMonotonicityResidualAtPivot P V j₀` for
an arbitrary `V`, this certificate records only the residue for the single
chosen Stage-4-matched A1 package actually consumed downstream. -/
def AllPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate
    {X : ι → Type v}
    (P : ProductPref X)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  WakkerStep5StrictMonotonicityResidualAtPivot P hdata.V hdata.j₀

/-- One pivot-touching indifferent swap at a fixed pivot `j₀`.

This is the single-step relation suggested by the strictness-chain roadmap:
the two profiles agree off one pivot-touching pair `{j₀, k}` and are
indifferent under `P`.  All-pairs additivity then forces equality of their
global additive sums. -/
def PivotTouchingIndifferenceStep
    {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Profile X → Profile X → Prop :=
  fun x y =>
    ∃ k : ι, k ≠ j₀ ∧
      Profile.agreeOff ({j₀, k} : Set ι) x y ∧
      P.indiff x y

/-- One-step pivot-compensating bracketing surface below the full chain seam.

For a target profile `target`, a non-pivot coordinate `k`, and a desired value
`vk : X k`, require only a pair of pivot values `v, w : X j₀` such that the
two profiles on the `{j₀, k}`-slice with `k` fixed at `vk` bracket `target`.
Restricted solvability then turns this bracketing data into an actual
indifferent pivot-touching step. -/
def PivotCoordinateRetargetingBracketAtPivotCertificate
    {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ target : Profile X,
    ∀ k : ι, k ≠ j₀ →
      ∀ vk : X k,
        ∃ v w : X j₀,
          P.weakPref (Function.update (Function.update target k vk) j₀ v) target ∧
          P.weakPref target (Function.update (Function.update target k vk) j₀ w)

/-- One-step pivot-compensating retargeting surface below the full chain seam.

The desired output of a single local move: retarget one non-pivot coordinate
`k` to an arbitrary value `vk`, compensating only at the pivot `j₀`, while
staying indifferent to the original target profile. -/
def PivotCoordinateRetargetingAtPivotCertificate
    {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ target : Profile X,
    ∀ k : ι, k ≠ j₀ →
      ∀ vk : X k,
        ∃ z : Profile X,
          Profile.agreeOff ({j₀, k} : Set ι) z target ∧
          z k = vk ∧
          P.indiff z target

/-- **Pivot-grid two-sided escape residual (the §IV.5/§IV.2 reach content of
axiom 17).**

For every target profile, non-pivot coordinate `k`, and desired value `vk`,
there is a strict standard sequence on the pivot `j₀` **based at the perturbed
target** `update target k vk` whose grid escapes `target` in *both* directions:
some grid point is not weakly below `target`, and some grid point is not weakly
above it.

This is the genuine Archimedean reach content of axiom 17 at an arbitrary base
(the base-transport reach), isolated as a single named residual — exactly the
role `TwoPivotSliceTransportCoverageResidual` plays for §IV.6 (Phase 39).  The
two-directional escape is genuinely two facts: the additive-real counterexample
shows a one-sided ℕ-grid can fail the lower direction. -/
def PivotGridEscapesAtTarget
    {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ target : Profile X,
    ∀ k : ι, k ≠ j₀ →
      ∀ vk : X k,
        ∃ σ : ProductPref.StandardSequence P j₀,
          σ.IsStrict ∧
          σ.base = Function.update target k vk ∧
          (∃ n : ℕ, ¬ P.weakPref target (Function.update σ.base j₀ (σ.α n))) ∧
          (∃ n : ℕ, ¬ P.weakPref (Function.update σ.base j₀ (σ.α n)) target)

/-- **Axiom 17's bracket certificate from the pivot-grid escape residual
(theorem-backed via engine B).**

The pivot-coordinate-retargeting bracket (axiom 17) is **theorem-backed** from
the single two-sided escape residual `PivotGridEscapesAtTarget` plus the raw
Archimedean axiom on the pivot, by feeding the escape witnesses to engine B's
Archimedean reach lemmas (`archimedean_reach_above`/`archimedean_reach_below`,
`RawAxiomDischargersIVT.lean`).  Each escape direction yields one bracketing
pivot value at the perturbed-target base.  This retires axiom 17's two
directional half-axioms in favor of the single escape residual — the same move
Phase 39 made for §IV.6's 16a/16b.

Audit: `[propext, Classical.choice, Quot.sound]` — no `_from_raw_axioms`
dependency; engine B carries the reach content. -/
theorem pivotCoordinateRetargetingBracketAtPivotCertificate_of_pivotGridEscapes
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (harchim : ProductPref.Archimedean P j₀)
    (hesc : PivotGridEscapesAtTarget P j₀) :
    PivotCoordinateRetargetingBracketAtPivotCertificate P j₀ := by
  intro target k hk vk
  obtain ⟨σ, hσ, hbase, habove, hbelow⟩ := hesc target k hk vk
  obtain ⟨v, hv⟩ :=
    RawAxiomDischargersIVT.archimedean_reach_above P σ hσ harchim target habove
  obtain ⟨w, hw⟩ :=
    RawAxiomDischargersIVT.archimedean_reach_below P σ hσ harchim target hbelow
  rw [hbase] at hv hw
  exact ⟨v, w, hv, hw⟩

/-- **One-sided pivot-grid escape residual: descending grid seeded above the
target.**

The leaner residual below `PivotGridEscapesAtTarget`: for every target, non-pivot
`k`, value `vk`, there is a strict standard sequence on the pivot based at the
perturbed target `update target k vk` that is **weakly descending** and whose
first grid point is **not weakly below** the target (seeded at or above it).

Compared to `PivotGridEscapesAtTarget`, the *lower* escape direction is dropped:
for a weakly-descending Archimedean grid it is **automatic** (engine B's
`archimedean_weaklyDescending_escape_below`), so only the single upper seed
condition remains.  This mirrors how engine B reduced the IVT crossing to the
single seed-above condition (`archimedean_weaklyDescending_slice_crossing_of_seedAbove`). -/
def PivotGridDescendingSeededAboveAtTarget
    {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ target : Profile X,
    ∀ k : ι, k ≠ j₀ →
      ∀ vk : X k,
        ∃ σ : ProductPref.StandardSequence P j₀,
          σ.IsStrict ∧
          σ.base = Function.update target k vk ∧
          (∀ n, P.weakPref (Function.update σ.base j₀ (σ.α n))
                           (Function.update σ.base j₀ (σ.α (n + 1)))) ∧
          ¬ P.weakPref target (Function.update σ.base j₀ (σ.α 0))

/-- **Leaner B1 residual: a strict seeded-above pivot sequence with one
reference-exchange fact (the descending property dropped).**

For every target, non-pivot `k`, value `vk`: a strict standard sequence on the
pivot based at `update target k vk`, seeded strictly above the target, carrying
the single reverse-exchange comparison `coordPref σ.k σ.base σ.s σ.r`.  The
**descending** property of `PivotGridDescendingSeededAboveAtTarget` is *not* part
of this residual — under coordinate weak separability (the §III.4 structural
input carried in the topology bundle) it is derived from this one exchange
(Phase 72 `weaklyDescending_of_separable_and_exchange`). -/
def PivotStrictSeededAboveGridData
    {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ target : Profile X,
    ∀ k : ι, k ≠ j₀ →
      ∀ vk : X k,
        ∃ σ : ProductPref.StandardSequence P j₀,
          σ.IsStrict ∧
          σ.base = Function.update target k vk ∧
          P.coordPref σ.k σ.base σ.s σ.r ∧
          ¬ P.weakPref target (Function.update σ.base j₀ (σ.α 0))

/-- **B1 discharge: the descending-seeded escape residual from the leaner
strict-seeded-above residual + coordinate weak separability.**

The descending property of `PivotGridDescendingSeededAboveAtTarget` is supplied by
`RawAxiomDischargersIVT.weaklyDescending_of_separable_and_exchange` (Phase 72) from
coordinate weak separability of both the pivot `j₀` and the sequence's auxiliary
coordinate `σ.k` (the §III.4 structural input — Wakker §III.4 coordinate
independence) plus the single reverse-exchange fact carried in
`PivotStrictSeededAboveGridData`.  Strictness, base, and seed-above pass through.

This realizes roadmap item **B1**: the descending-seeded escape residual reduces
to the strict seeded-above standard-sequence existence (the genuine §IV.2
standard-sequence content) plus one reference-exchange comparison, with the
infinite descending family collapsed and theorem-backed from §III.4 separability. -/
theorem pivotGridDescendingSeededAboveAtTarget_of_strictSeededAboveData
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (hsep : ∀ i, RawAxiomDischargersIVT.CoordinateWeakSeparable P i)
    (hgrid : PivotStrictSeededAboveGridData P j₀) :
    PivotGridDescendingSeededAboveAtTarget P j₀ := by
  intro target k hk vk
  obtain ⟨σ, hσ, hbase, hexch, hseed⟩ := hgrid target k hk vk
  refine ⟨σ, hσ, hbase, ?_, hseed⟩
  exact RawAxiomDischargersIVT.weaklyDescending_of_separable_and_exchange P σ
    (hsep j₀) (hsep σ.k) hexch

/-- **Per-target seed data for the strict seeded-above pivot sequence (B1 §IV.2
residual core).**

For every target profile, non-pivot `k`, and value `vk`, the genuine §IV.2
standard-sequence *seed* at the perturbed base `update target k vk`:

* an auxiliary non-pivot coordinate `kk ≠ j₀` with a reference exchange
  `r ↦ s` (`hrs : r ≠ s`) and the seed indifference `h01` between the
  `(a0 at j₀, r at kk)` and `(a1 at j₀, s at kk)` profiles — exactly the input
  `extend_to_standard_sequence` consumes;
* the **strict first step** `a0 ≻ a1` at `j₀` over the perturbed base
  (`hweak` + `hnotweak`) — the §III.4/Essential strictness seed;
* the **seed-above** comparison `¬ weakPref target (a0 at j₀)` — the grid starts
  strictly above the target;
* the **reverse exchange** `coordPref kk base s r` carried for the descending
  reduction (Phase 72).

This is the honest remaining §IV.2 content of `PivotStrictSeededAboveGridData`:
the existence of a seeded standard-sequence *germ* at an arbitrary base.  The
infinite sequence, strictness propagation, and descending family are all
theorem-backed from this germ (plus the topology `OneStepExtensible` discharge
and §III.4 separability). -/
def PivotStrictSeededAboveSeedDataFamily
    {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ target : Profile X,
    ∀ k : ι, k ≠ j₀ →
      ∀ vk : X k,
        ∃ (kk : ι) (hkk : kk ≠ j₀) (a0 a1 : X j₀) (r s : X kk),
          r ≠ s ∧
          P.indiff
            (Function.update (Function.update (Function.update target k vk) j₀ a0) kk r)
            (Function.update (Function.update (Function.update target k vk) j₀ a1) kk s) ∧
          P.weakPref (Function.update (Function.update target k vk) j₀ a0)
                     (Function.update (Function.update target k vk) j₀ a1) ∧
          ¬ P.weakPref (Function.update (Function.update target k vk) j₀ a1)
                       (Function.update (Function.update target k vk) j₀ a0) ∧
          ¬ P.weakPref target
              (Function.update (Function.update target k vk) j₀ a0) ∧
          P.coordPref kk (Function.update target k vk) s r

/-- **B1 §IV.2 discharge: the strict seeded-above grid data from the per-target
seed germ + the topology one-step-extensibility (Phase 75).**

`PivotStrictSeededAboveGridData` is theorem-backed from the per-target seed germ
`PivotStrictSeededAboveSeedDataFamily` plus the topology bundle (which discharges
`OneStepExtensible` via `oneStepExtensible_of_wakkerCoordinateTopology_and_restrictedSolvability`,
the §III.4.2 IVT/connectedness content) and restricted solvability.

For each `(target, k, vk)` the germ supplies the seed; the topology bundle
discharges one-step extensibility at the perturbed base; the record-form builder
`standardSequenceBuild_of_seed_and_oneStepExtensible` produces a standard sequence
whose `base`, `α 0`, `α 1`, `k`, `r`, `s` are all definitionally the seed values;
strictness (`IsStrict`) is the seed strict first step; the seed-above and
reverse-exchange facts pass through verbatim.

This realizes the §IV.2 standard-sequence *existence* content of B1: the residual
is reduced to the per-target seed germ, with the recursive construction,
strictness, base/grid identities, and field transparency all theorem-backed.
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem pivotStrictSeededAboveGridData_of_seedDataFamily
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (hseed : PivotStrictSeededAboveSeedDataFamily P j₀) :
    PivotStrictSeededAboveGridData P j₀ := by
  intro target k hk vk
  obtain ⟨kk, hkk, a0, a1, r, s, hrs, h01, hweak, hnotweak, hseedAbove, hrev⟩ :=
    hseed target k hk vk
  -- The perturbed base.
  set base : Profile X := Function.update target k vk with hbasedef
  -- One-step extensibility at the perturbed base from the topology bundle.
  have hext : ProductPref.OneStepExtensible P j₀ base kk r s :=
    RawAxiomDischargersTopology.oneStepExtensible_of_wakkerCoordinateTopology_and_restrictedSolvability
      solvability htop (Ne.symm hkk) base r s hrs
  -- The record-form builder: σ.base ≡ base, σ.α 0 ≡ a0, σ.α 1 ≡ a1, σ.k ≡ kk,
  -- σ.r ≡ r, σ.s ≡ s — all definitional.
  let σ : ProductPref.StandardSequence P j₀ :=
    RawAxiomDischargersStandardSequence.standardSequenceBuild_of_seed_and_oneStepExtensible
      P j₀ kk hkk base a0 a1 r s hrs h01 hext
  refine ⟨σ, ?_, rfl, ?_, ?_⟩
  · -- Strictness: the seed strict first step at α 0 = a0, α 1 = a1.
    show P.strict (Function.update σ.base j₀ (σ.α 0))
                  (Function.update σ.base j₀ (σ.α 1))
    exact ⟨hweak, hnotweak⟩
  · -- Reverse exchange: coordPref σ.k σ.base σ.s σ.r ≡ coordPref kk base s r.
    exact hrev
  · -- Seeded above: ¬ weakPref target (update σ.base j₀ (σ.α 0)) ≡ … a0.
    exact hseedAbove

/-- **WP-T-clean B1 seed germ with the Archimedean one-step escape grid.**

Enriches `PivotStrictSeededAboveSeedDataFamily` so the standard-sequence
construction can route `OneStepExtensible` through the **escape-based** discharge
(`oneStepExtensible_of_wakkerCoordinateTopology_and_archimedeanEscape`, engines
A+B) instead of the bracket reach **axioms**.  For each `(target, k, vk)` it adds,
alongside the seed data `(kk, r, s, a0, a1, …)`, the per-prior-pivot Archimedean
escape grid that two-sidedly escapes the `r`-perturbed reference along `j₀` with
`kk` fixed at `s`.  This escape grid is the genuine Wakker §IV.2.6
standard-sequence content; carrying it makes the B1 discharge reach-axiom-free. -/
def PivotStrictSeededAboveSeedDataWithEscapeFamily
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ target : Profile X,
    ∀ k : ι, k ≠ j₀ →
      ∀ vk : X k,
        ∃ (kk : ι) (hkk : kk ≠ j₀) (a0 a1 : X j₀) (r s : X kk),
          r ≠ s ∧
          P.indiff
            (Function.update (Function.update (Function.update target k vk) j₀ a0) kk r)
            (Function.update (Function.update (Function.update target k vk) j₀ a1) kk s) ∧
          P.weakPref (Function.update (Function.update target k vk) j₀ a0)
                     (Function.update (Function.update target k vk) j₀ a1) ∧
          ¬ P.weakPref (Function.update (Function.update target k vk) j₀ a1)
                       (Function.update (Function.update target k vk) j₀ a0) ∧
          ¬ P.weakPref target
              (Function.update (Function.update target k vk) j₀ a0) ∧
          P.coordPref kk (Function.update target k vk) s r ∧
          -- The Archimedean one-step escape grid (genuine §IV.2.6 residual):
          (∀ aPrev : X j₀,
            ∃ σ' : ProductPref.StandardSequence P j₀,
              σ'.IsStrict ∧
              σ'.base = Function.update (Function.update target k vk) kk s ∧
              (∃ n : ℕ, ¬ P.weakPref
                (Function.update (Function.update (Function.update target k vk) j₀ aPrev) kk r)
                (Function.update σ'.base j₀ (σ'.α n))) ∧
              (∃ n : ℕ, ¬ P.weakPref
                (Function.update σ'.base j₀ (σ'.α n))
                (Function.update (Function.update (Function.update target k vk) j₀ aPrev) kk r)))

/-- **WP-T: reach-axiom-free B1 discharge.**

`PivotStrictSeededAboveGridData` from the enriched seed germ
`PivotStrictSeededAboveSeedDataWithEscapeFamily`, routing `OneStepExtensible`
through the engine-A∘B escape discharge
(`oneStepExtensible_of_wakkerCoordinateTopology_and_archimedeanEscape`) — so the
two `coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology`
**axioms are not used**.  The §III.4.2 IVT seams are gone; the residual is the
honest §IV.2.6 Archimedean escape grid carried in the germ.

Audit (verified below): `[propext, Classical.choice, Quot.sound]` — **no**
`coordinateOneStepBracket*` axiom. -/
theorem pivotStrictSeededAboveGridData_of_seedDataWithEscapeFamily
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hseed : PivotStrictSeededAboveSeedDataWithEscapeFamily P j₀) :
    PivotStrictSeededAboveGridData P j₀ := by
  intro target k hk vk
  obtain ⟨kk, hkk, a0, a1, r, s, hrs, h01, hweak, hnotweak, hseedAbove, hrev, hesc⟩ :=
    hseed target k hk vk
  set base : Profile X := Function.update target k vk with hbasedef
  -- One-step extensibility WITHOUT the bracket reach axioms: via Archimedean escape.
  have hext : ProductPref.OneStepExtensible P j₀ base kk r s :=
    RawAxiomDischargersTopology.oneStepExtensible_of_wakkerCoordinateTopology_and_archimedeanEscape
      htop (Ne.symm hkk) base r s (archimedean j₀) hesc
  let σ : ProductPref.StandardSequence P j₀ :=
    RawAxiomDischargersStandardSequence.standardSequenceBuild_of_seed_and_oneStepExtensible
      P j₀ kk hkk base a0 a1 r s hrs h01 hext
  refine ⟨σ, ?_, rfl, ?_, ?_⟩
  · show P.strict (Function.update σ.base j₀ (σ.α 0))
                  (Function.update σ.base j₀ (σ.α 1))
    exact ⟨hweak, hnotweak⟩
  · exact hrev
  · exact hseedAbove

/-- **B1 consolidated: the descending-seeded escape residual directly from the
per-target seed germ (Phases 72 + 75).**

The full B1 reduction in one step: `PivotGridDescendingSeededAboveAtTarget P j₀`
from
* the per-target standard-sequence **seed germ**
  `PivotStrictSeededAboveSeedDataFamily P j₀` (the bare §IV.2.7 seed existence at
  an arbitrary base),
* §III.4 coordinate weak separability (the A1 structural input — supplies the
  descending family, Phase 72),
* the topology bundle + restricted solvability (discharge `OneStepExtensible`,
  build the infinite sequence, Phase 75).

Composes `pivotStrictSeededAboveGridData_of_seedDataFamily` (Phase 75 — builds the
strict seeded-above sequence from the germ) with
`pivotGridDescendingSeededAboveAtTarget_of_strictSeededAboveData` (Phase 72 —
adds the descending family from separability + the germ's reverse exchange).  This
exhibits the entire descending-seeded escape residual as resting on exactly the
seed germ plus the structural/topological inputs.  Audit `[propext,
Classical.choice, Quot.sound]` + the §III.4.2 topology IVT seams. -/
theorem pivotGridDescendingSeededAboveAtTarget_of_seedDataFamily
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (hsep : ∀ i, RawAxiomDischargersIVT.CoordinateWeakSeparable P i)
    (j₀ : ι)
    (hseed : PivotStrictSeededAboveSeedDataFamily P j₀) :
    PivotGridDescendingSeededAboveAtTarget P j₀ :=
  pivotGridDescendingSeededAboveAtTarget_of_strictSeededAboveData
    P j₀ hsep
    (pivotStrictSeededAboveGridData_of_seedDataFamily
      P solvability htop j₀ hseed)

/-- **WP-T: reach-axiom-free consolidated B1 discharge.**

Identical to `pivotGridDescendingSeededAboveAtTarget_of_seedDataFamily` but routes
the standard-sequence construction through the engine-A∘B Archimedean escape
(`pivotStrictSeededAboveGridData_of_seedDataWithEscapeFamily`) instead of the
bracket reach axioms.  Consumes the enriched seed germ
`PivotStrictSeededAboveSeedDataWithEscapeFamily` (carrying the §IV.2.6 escape
grid).  Audit (verified below): `[propext, Classical.choice, Quot.sound]` — **no**
`coordinateOneStepBracket*` axiom. -/
theorem pivotGridDescendingSeededAboveAtTarget_of_seedDataWithEscapeFamily
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hsep : ∀ i, RawAxiomDischargersIVT.CoordinateWeakSeparable P i)
    (j₀ : ι)
    (hseed : PivotStrictSeededAboveSeedDataWithEscapeFamily P j₀) :
    PivotGridDescendingSeededAboveAtTarget P j₀ :=
  pivotGridDescendingSeededAboveAtTarget_of_strictSeededAboveData
    P j₀ hsep
    (pivotStrictSeededAboveGridData_of_seedDataWithEscapeFamily
      P solvability htop archimedean j₀ hseed)

/-- **Two-sided escape from the one-sided descending-seeded residual
(theorem-backed via engine B).**

`PivotGridEscapesAtTarget` follows from the leaner
`PivotGridDescendingSeededAboveAtTarget` plus the raw Archimedean axiom: the
upper escape is witnessed at `n = 0` (the seed-above condition), and the lower
escape is **automatic** from descent via
`archimedean_weaklyDescending_escape_below`.  This shrinks axiom 17's reach
residual to a single one-sided seed condition on a descending grid. -/
theorem pivotGridEscapesAtTarget_of_descendingSeededAbove
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (harchim : ProductPref.Archimedean P j₀)
    (hgrid : PivotGridDescendingSeededAboveAtTarget P j₀) :
    PivotGridEscapesAtTarget P j₀ := by
  intro target k hk vk
  obtain ⟨σ, hσ, hbase, hdesc, hseed⟩ := hgrid target k hk vk
  refine ⟨σ, hσ, hbase, ⟨0, hseed⟩, ?_⟩
  exact RawAxiomDischargersIVT.archimedean_weaklyDescending_escape_below
    P σ hσ harchim hdesc target

/-- **Axiom 17's bracket from the one-sided descending-seeded residual.**

Composes `pivotGridEscapesAtTarget_of_descendingSeededAbove` with
`pivotCoordinateRetargetingBracketAtPivotCertificate_of_pivotGridEscapes`: the
pivot-retargeting bracket is theorem-backed from the single one-sided
descending-seeded-above residual plus the raw Archimedean axiom.  This is the
leanest engine-B route for axiom 17 — only an upper seed condition on a
descending grid remains. -/
theorem pivotCoordinateRetargetingBracketAtPivotCertificate_of_descendingSeededAbove
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (harchim : ProductPref.Archimedean P j₀)
    (hgrid : PivotGridDescendingSeededAboveAtTarget P j₀) :
    PivotCoordinateRetargetingBracketAtPivotCertificate P j₀ :=
  pivotCoordinateRetargetingBracketAtPivotCertificate_of_pivotGridEscapes
    P j₀ harchim
    (pivotGridEscapesAtTarget_of_descendingSeededAbove P j₀ harchim hgrid)

/-- **One-sided pivot-grid escape residual: ascending grid seeded below the
target** (dual of `PivotGridDescendingSeededAboveAtTarget`).

For every target, non-pivot `k`, value `vk`, there is a strict standard sequence
on the pivot based at the perturbed target that is **weakly ascending** and whose
first grid point is **not weakly above** the target (seeded at or below it).

Here the *upper* escape direction is automatic for a weakly-ascending Archimedean
grid (engine B's `archimedean_weaklyAscending_escape_above`, Phase 45), so only
the single lower seed condition remains.  Symmetric companion to the descending
form. -/
def PivotGridAscendingSeededBelowAtTarget
    {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι) : Prop :=
  ∀ target : Profile X,
    ∀ k : ι, k ≠ j₀ →
      ∀ vk : X k,
        ∃ σ : ProductPref.StandardSequence P j₀,
          σ.IsStrict ∧
          σ.base = Function.update target k vk ∧
          (∀ n, P.weakPref (Function.update σ.base j₀ (σ.α (n + 1)))
                           (Function.update σ.base j₀ (σ.α n))) ∧
          ¬ P.weakPref (Function.update σ.base j₀ (σ.α 0)) target

/-- **Two-sided escape from the one-sided ascending-seeded residual
(theorem-backed via engine B).**

Dual of `pivotGridEscapesAtTarget_of_descendingSeededAbove`:
`PivotGridEscapesAtTarget` follows from the leaner
`PivotGridAscendingSeededBelowAtTarget` plus the raw Archimedean axiom: the lower
escape is witnessed at `n = 0` (the seed-below condition), and the upper escape is
**automatic** from ascent via `archimedean_weaklyAscending_escape_above`. -/
theorem pivotGridEscapesAtTarget_of_ascendingSeededBelow
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (harchim : ProductPref.Archimedean P j₀)
    (hgrid : PivotGridAscendingSeededBelowAtTarget P j₀) :
    PivotGridEscapesAtTarget P j₀ := by
  intro target k hk vk
  obtain ⟨σ, hσ, hbase, hasc, hseed⟩ := hgrid target k hk vk
  refine ⟨σ, hσ, hbase, ?_, ⟨0, hseed⟩⟩
  exact RawAxiomDischargersIVT.archimedean_weaklyAscending_escape_above
    P σ hσ harchim hasc target

/-- **Axiom 17's bracket from the one-sided ascending-seeded residual.**

Symmetric companion to
`pivotCoordinateRetargetingBracketAtPivotCertificate_of_descendingSeededAbove`:
the pivot-retargeting bracket is theorem-backed from the single one-sided
ascending-seeded-below residual plus the raw Archimedean axiom. -/
theorem pivotCoordinateRetargetingBracketAtPivotCertificate_of_ascendingSeededBelow
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (harchim : ProductPref.Archimedean P j₀)
    (hgrid : PivotGridAscendingSeededBelowAtTarget P j₀) :
    PivotCoordinateRetargetingBracketAtPivotCertificate P j₀ :=
  pivotCoordinateRetargetingBracketAtPivotCertificate_of_pivotGridEscapes
    P j₀ harchim
    (pivotGridEscapesAtTarget_of_ascendingSeededBelow P j₀ harchim hgrid)

/-- Thin strictness-chain frontier below the chosen-A1 strictness residue.

For an indifferent pair `x ∼ y` that does not already agree off a single
pivot-touching pair `{j₀, k}`, only require a finite chain of pivot-touching
indifferent swaps connecting `x` to `y`.  The actual sum-equality residue is
then recovered below from all-pairs additivity, one chain step at a time. -/
def AllPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate
    {X : ι → Type v}
    (P : ProductPref X)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  ∀ x y : Profile X,
    P.indiff x y →
    (∀ k : ι, k ≠ hdata.j₀ →
      ¬ Profile.agreeOff ({hdata.j₀, k} : Set ι) x y) →
    Relation.TransGen (PivotTouchingIndifferenceStep P hdata.j₀) x y

/-- Thin Stage-5 coverage frontier.

This is the coverage analogue of
`AllPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate`: the
residual family is only demanded for the same chosen Stage-4-matched A1
package. -/
def AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate
    {X : ι → Type v}
    (P : ProductPref X)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  ∀ j₀ : ι, WakkerStep5CoordinateImageCoverageResidualAtPivot P hdata.V j₀

/-- Indifference is transitive under a weak order. -/
lemma productPref_indiff_trans
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {x y z : Profile X}
    (hxy : P.indiff x y) (hyz : P.indiff y z) :
    P.indiff x z := by
  refine ⟨?_, ?_⟩
  · exact ProductPref.IsWeakOrder.transitive x y z hxy.1 hyz.1
  · exact ProductPref.IsWeakOrder.transitive z y x hyz.2 hxy.2

/-- The smaller bracketing seam plus restricted solvability already produce a
single pivot-compensated retargeting step. -/
theorem pivotCoordinateRetargetingAtPivotCertificate_of_bracketing_and_restrictedSolvability
    {X : ι → Type v}
    (P : ProductPref X) (j₀ : ι)
    (hbracket : PivotCoordinateRetargetingBracketAtPivotCertificate P j₀)
    (hsolv : ProductPref.RestrictedSolvability P) :
    PivotCoordinateRetargetingAtPivotCertificate P j₀ := by
  intro target k hk vk
  obtain ⟨v, w, hhi, hlo⟩ := hbracket target k hk vk
  have hslice :=
    pairwiseSliceInterpolationCertificate_of_restrictedSolvability
      P hsolv j₀ k
  obtain ⟨z, hzagree, hzk, hzindiff⟩ :=
    hslice.1 target target hk.symm vk v w
      (Profile.agreeOff_refl ({j₀, k} : Set ι) target)
      hhi hlo
  exact ⟨z, hzagree, hzk, hzindiff⟩

/-- **Full pivot retargeting interface from the descending-seeded escape residual
(end-to-end, theorem-backed).**

Composes the Phase-44 bracket discharge
(`pivotCoordinateRetargetingBracketAtPivotCertificate_of_descendingSeededAbove`)
with restricted-solvability interpolation: from the minimal one-sided
descending-seeded escape residual + the raw Archimedean axiom + restricted
solvability, the full one-step pivot-compensated retargeting interface follows.
This realizes the spec's obligation-4 ladder steps 1→3 from the single minimal
escape residual — no bracket axiom. -/
theorem pivotCoordinateRetargetingAtPivotCertificate_of_descendingSeededAbove
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (harchim : ProductPref.Archimedean P j₀)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hgrid : PivotGridDescendingSeededAboveAtTarget P j₀) :
    PivotCoordinateRetargetingAtPivotCertificate P j₀ :=
  pivotCoordinateRetargetingAtPivotCertificate_of_bracketing_and_restrictedSolvability
    P j₀
    (pivotCoordinateRetargetingBracketAtPivotCertificate_of_descendingSeededAbove
      P j₀ harchim hgrid)
    hsolv

/-- **Full pivot retargeting interface from the ascending-seeded escape residual
(end-to-end, theorem-backed).**

Symmetric companion using the ascending-seeded-below escape residual (Phase 45).
Either monotone direction of the minimal escape residual, plus restricted
solvability, yields the full retargeting interface. -/
theorem pivotCoordinateRetargetingAtPivotCertificate_of_ascendingSeededBelow
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (harchim : ProductPref.Archimedean P j₀)
    (hsolv : ProductPref.RestrictedSolvability P)
    (hgrid : PivotGridAscendingSeededBelowAtTarget P j₀) :
    PivotCoordinateRetargetingAtPivotCertificate P j₀ :=
  pivotCoordinateRetargetingAtPivotCertificate_of_bracketing_and_restrictedSolvability
    P j₀
    (pivotCoordinateRetargetingBracketAtPivotCertificate_of_ascendingSeededBelow
      P j₀ harchim hgrid)
    hsolv

/-- **Partial discharge of axiom 17 in `card ι = 1` cardinality.**

When `Fintype.card ι = 1`, the inner `∀ k : ι, k ≠ j₀` is vacuous since
the only coordinate is `j₀` itself.  So
`PivotCoordinateRetargetingBracketAtPivotCertificate P j₀` holds
trivially.

This is a real theorem-backed discharge in the degenerate case;
the genuine Wakker §IV.5 + §IV.2 retargeting content lives in the
`card ι ≥ 2` regime. -/
theorem pivotCoordinateRetargetingBracketAtPivotCertificate_of_card_eq_one
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hcard : Fintype.card ι = 1) :
    PivotCoordinateRetargetingBracketAtPivotCertificate P j₀ := by
  intro _target k hk _vk
  exfalso
  -- card = 1 + j₀ ∈ ι forces ι = {j₀}, so k ≠ j₀ is impossible.
  by_contra _
  have h2 : 2 ≤ Fintype.card ι := by
    calc 2 = ({j₀, k} : Finset ι).card := by
            rw [Finset.card_insert_of_notMem
                  (by simpa using Ne.symm hk),
                Finset.card_singleton]
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **Raw-axiom-form discharge of axiom 17 in `card ι = 1` cardinality.** -/
theorem pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_of_card_eq_one
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hcard : Fintype.card ι = 1) :
    PivotCoordinateRetargetingBracketAtPivotCertificate P j₀ :=
  pivotCoordinateRetargetingBracketAtPivotCertificate_of_card_eq_one P j₀ hcard

/-- The smaller one-coordinate retargeting surface already implies the full
pivot-touching chain frontier in the `card ι ≥ 3` regime used by the
end-to-end closure ladder. -/
theorem allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_of_pivotCoordinateRetargeting
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hretarget : PivotCoordinateRetargetingAtPivotCertificate P hdata.j₀) :
    AllPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate P hdata := by
  intro x y hxy _hnonpair
  classical
  let step : Profile X → Profile X → Prop := PivotTouchingIndifferenceStep P hdata.j₀
  have hbuild :
      ∀ S : Finset ι, hdata.j₀ ∉ S →
        ∃ t : Profile X,
          Relation.ReflTransGen step x t ∧
          P.indiff t x ∧
          (∀ i : ι, i ∈ S → t i = y i) ∧
          (∀ i : ι, i ≠ hdata.j₀ → i ∉ S → t i = x i) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _
      refine ⟨x, Relation.ReflTransGen.refl, productPref_indiff_refl P x, ?_, ?_⟩
      · intro i hi
        exact False.elim (Finset.notMem_empty i hi)
      · intro i _ _
        rfl
    · intro k S hkS ih hj₀_notin_insert
      have hj₀_notin_S : hdata.j₀ ∉ S := by
        intro hj₀_in
        exact hj₀_notin_insert (Finset.mem_insert_of_mem hj₀_in)
      have hk_pivot : k ≠ hdata.j₀ := by
        intro hkj₀
        exact hj₀_notin_insert (by simp [hkj₀])
      obtain ⟨t, htchain, htindiff, hvals, hrest⟩ := ih hj₀_notin_S
      obtain ⟨z, hzagree, hzk, hzindiff⟩ := hretarget t k hk_pivot (y k)
      have hstep_tz : step t z := by
        refine ⟨k, hk_pivot, Profile.agreeOff_symm hzagree, ?_⟩
        exact ⟨hzindiff.2, hzindiff.1⟩
      refine ⟨z, htchain.trans (Relation.ReflTransGen.single hstep_tz), ?_, ?_, ?_⟩
      · exact productPref_indiff_trans hzindiff htindiff
      · intro i hi_insert
        rcases Finset.mem_insert.mp hi_insert with rfl | hiS
        · exact hzk
        · have hik : i ≠ k := by
            intro hik
            subst hik
            exact hkS hiS
          have hij₀ : i ≠ hdata.j₀ := by
            intro hij₀
            subst hij₀
            exact hj₀_notin_S hiS
          have hizt : z i = t i := by
            exact hzagree i (by simp [hij₀, hik])
          exact hizt.trans (hvals i hiS)
      · intro i hij₀ hi_not_insert
        have hik : i ≠ k := by
          intro hik
          apply hi_not_insert
          simp [hik]
        have hi_not_S : i ∉ S := by
          intro hiS
          exact hi_not_insert (Finset.mem_insert_of_mem hiS)
        have hizt : z i = t i := by
          exact hzagree i (by simp [hij₀, hik])
        exact hizt.trans (hrest i hij₀ hi_not_S)
  obtain ⟨t, htchain, htindiff, hvals, _hrest⟩ :=
    hbuild (Finset.univ.erase hdata.j₀) (by simp)
  have ht_y : P.indiff t y :=
    productPref_indiff_trans htindiff hxy
  have haux : ∃ k : ι, k ≠ hdata.j₀ := by
    by_contra hno
    push_neg at hno
    have huniv : (Finset.univ : Finset ι) = {hdata.j₀} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro a _
      exact hno a
    have hcard1 : Fintype.card ι = 1 := by
      simp [Fintype.card, huniv]
    have hge3 : 3 ≤ Fintype.card ι := Fact.out
    omega
  obtain ⟨k, hk⟩ := haux
  have hfinal_agree : Profile.agreeOff ({hdata.j₀, k} : Set ι) t y := by
    intro i hi
    have hij₀ : i ≠ hdata.j₀ := by
      intro hij₀
      apply hi
      simp [hij₀]
    exact hvals i (by simp [Finset.mem_erase, hij₀])
  have hlast : PivotTouchingIndifferenceStep P hdata.j₀ t y := by
    exact ⟨k, hk, hfinal_agree, ht_y⟩
  exact Relation.TransGen.tail' htchain hlast

/-- The shared-pivot magnitude/bracketing family implies the thinner shared-
pivot hexagon family by forgetting the extra magnitude/bracketing fields after
turning each pairwise package into `PairwiseHexagonStandardSequenceCertificate`.
-/
theorem sharedPivotHexagonFamilyCertificate_of_sharedPivotMagnitudeBracketingFamilyCertificate
  {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (hmbh : SharedPivotMagnitudeBracketingFamilyCertificate P j₀) :
    SharedPivotHexagonFamilyCertificate P j₀ := by
  obtain ⟨σⱼ₀, hinj_j₀, hfamily⟩ := hmbh
  refine ⟨σⱼ₀, hinj_j₀, ?_⟩
  intro k hk
  obtain ⟨σk, hinj_k, hmbh_k⟩ := hfamily k hk
  refine ⟨σk, hinj_k, ?_⟩
  exact
    pairwiseHexagonStandardSequenceCertificate_of_pairwiseMagnitudeBracketingHexagonCertificate
      P hk.symm σⱼ₀ σk hmbh_k

/-- The shared-pivot finite-cut bridge family upgrades to the shared-pivot
hexagon family by applying the explicit per-pair transport certificate on each
non-pivot slice. -/
theorem sharedPivotHexagonFamilyCertificate_of_sharedPivotMagnitudeFiniteCutTransportFamilyCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hfinite : SharedPivotMagnitudeFiniteCutTransportFamilyCertificate P j₀) :
    SharedPivotHexagonFamilyCertificate P j₀ := by
  obtain ⟨σⱼ₀, hinj_j₀, hfamily⟩ := hfinite
  refine ⟨σⱼ₀, hinj_j₀, ?_⟩
  intro k hk
  obtain ⟨σk, hinj_k, hfinite_k, htransport_k⟩ := hfamily k hk
  refine ⟨σk, hinj_k, ?_⟩
  exact htransport_k hfinite_k

/-- The bundled shared-pivot hexagon family discharges the broad shared-pivot
Step-4 machinery certificate. -/
theorem sharedPivotAllPairsStep4MachineryCertificate_of_sharedPivotHexagonFamilyCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hhex : SharedPivotHexagonFamilyCertificate P j₀) :
    SharedPivotAllPairsStep4MachineryCertificate P j₀ := by
  obtain ⟨σⱼ₀, hinj_j₀, hfamily⟩ := hhex
  refine ⟨σⱼ₀, hinj_j₀, ?_⟩
  intro k hk
  obtain ⟨σk, hinj_k, hhex_k⟩ := hfamily k hk
  refine ⟨σk, hinj_k, ?_⟩
  exact
    pairwiseStep4TradeoffMachineryCertificate_of_pairwiseHexagonStandardSequenceCertificate
      P j₀ k σⱼ₀ σk hhex_k

/-- The bundled shared-pivot magnitude/bracketing family therefore also
discharges the broad shared-pivot Step-4 machinery certificate. -/
theorem sharedPivotAllPairsStep4MachineryCertificate_of_sharedPivotMagnitudeBracketingFamilyCertificate
  {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (hmbh : SharedPivotMagnitudeBracketingFamilyCertificate P j₀) :
    SharedPivotAllPairsStep4MachineryCertificate P j₀ := by
  exact
    sharedPivotAllPairsStep4MachineryCertificate_of_sharedPivotHexagonFamilyCertificate
      P j₀
      (sharedPivotHexagonFamilyCertificate_of_sharedPivotMagnitudeBracketingFamilyCertificate
        P j₀ hmbh)

/-- The shared-pivot finite-cut bridge family also discharges the broad
shared-pivot Step-4 machinery certificate once the explicit pairwise transport
into the hexagon layer is supplied. -/
theorem sharedPivotAllPairsStep4MachineryCertificate_of_sharedPivotMagnitudeFiniteCutTransportFamilyCertificate
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hfinite : SharedPivotMagnitudeFiniteCutTransportFamilyCertificate P j₀) :
    SharedPivotAllPairsStep4MachineryCertificate P j₀ := by
  exact
    sharedPivotAllPairsStep4MachineryCertificate_of_sharedPivotHexagonFamilyCertificate
      P j₀
      (sharedPivotHexagonFamilyCertificate_of_sharedPivotMagnitudeFiniteCutTransportFamilyCertificate
        P j₀ hfinite)

/-- The pivot-hexagon transport package discharges the broader non-pivot
cross-pair additivity certificate once the pivot slices are supplied. -/
theorem nonPivotPairAdditivityCertificate_of_pivotHexagonTransportCertificate
    {X : ι → Type v} (P : ProductPref X) (V : (i : ι) → X i → ℝ) (j₀ : ι)
    (htransport : PivotHexagonTransportCertificate P V j₀)
    (hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) :
    NonPivotPairAdditivityCertificate P V j₀ := by
  intro j k hj hk hjk x y hagree
  exact htransport j k hj hk hjk (hMatch j hj) (hMatch k hk) x y hagree

/-- **Obligation 3 (non-pivot cross-pair additivity) from the unified coverage
residual.**

The capstone of the Phase 38–40 line: `NonPivotPairAdditivityCertificate P V j₀`
is theorem-backed from a pivot-slice-matched `V` plus the single pivot
coordinate-image coverage residual `TwoPivotSliceTransportCoverageResidual`, with
**no** §IV.6 transport axiom.  Chains the coverage-backed two-pivot transport
(`twoPivotSliceTransportCertificate_of_coverageResidual`, Phase 39) → the
ambient-`V` reattachment (`pivotHexagonTransportCertificate_of_twoPivotSliceTransportCertificate`)
→ the cross-pair discharge above.

This realizes the spec's obligation-3 lemma ladder (3B) end-to-end: the entire
cross-pair transport machinery is proved; the only residual is the pivot
solvability/coverage primitive shared with obligations 5 and 16.  Audit:
`[propext, Classical.choice, Quot.sound]`, no `_from_raw_axioms`. -/
theorem nonPivotPairAdditivityCertificate_of_coverageResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ) (j₀ : ι)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀)
    (hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) :
    NonPivotPairAdditivityCertificate P V j₀ :=
  nonPivotPairAdditivityCertificate_of_pivotHexagonTransportCertificate P V j₀
    (pivotHexagonTransportCertificate_of_twoPivotSliceTransportCertificate P j₀
      (twoPivotSliceTransportCertificate_of_coverageResidual P j₀ hcov) V)
    hMatch

/-- **Obligation 3 from the §IV.5 representation family + the §IV.6 coverage
residual (unifying capstone).**

The single §IV.5 representation residual `SharedPivotGridAdditiveRepresentationFamily`
(Phase 61) supplies the pivot-slice matches `hMatch` (via
`pivotSliceMatch_of_gridAdditiveRepresentationFamily`); combined with the §IV.6
pivot coverage residual `TwoPivotSliceTransportCoverageResidual`, the engine-C
transport (Phases 38–40) discharges `NonPivotPairAdditivityCertificate`
(obligation 3) for the assembled `V`.

This ties the three §IV.5/§IV.6 frontier objects together: the **one**
representation family + the **one** coverage residual ⟹ obligation 3, with all
the Thomsen/hexagon transport machinery theorem-backed.  The genuine remaining
content is exactly those two named residuals (representation + coverage). -/
theorem nonPivotPairAdditivityCertificate_of_gridAdditiveRepresentationFamily_and_coverage
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hrep : SharedPivotGridAdditiveRepresentationFamily P j₀ hdata)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀) :
    ∃ V : (i : ι) → X i → ℝ,
      (∀ k : ι, k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) ∧
      NonPivotPairAdditivityCertificate P V j₀ := by
  obtain ⟨V, hMatch⟩ := pivotSliceMatch_of_gridAdditiveRepresentationFamily P j₀ hdata hrep
  exact ⟨V, hMatch,
    nonPivotPairAdditivityCertificate_of_coverageResidual P V j₀ hcov hMatch⟩

/-- **Obligation 3 from the representation family alone, when the common pivot
utility is surjective.**

If the §IV.5 representation family's common pivot utility `V₀` is **surjective**
onto ℝ, the §IV.6 pivot coverage holds automatically for the family's own slice
utilities (`pivotCompensatesJ_of_surjective`, Phase 38).  Routing each non-pivot
pair `(j, k)` directly through the engine-C transport
`RawAxiomDischargersHexagon.twoPivotSliceTransport` with the family's `(V₀, Vj)`
and `(V₀, Vk)` slice representations yields the `{j,k}`-slice representation — i.e.
obligation 3 — from the representation family **alone**, with no separate coverage
residual.

This is the honest non-degeneracy unification: a surjective common pivot utility
makes the §IV.5 representation family discharge the entire pivot-side frontier
(Step-4 core, A1 matches, and §IV.6 cross-pair additivity).  Surjectivity of `V₀`
is the natural condition (a connected, Archimedean-rich pivot coordinate; cf. the
engine-A IVT discharge of coverage, Phase 41).  It bypasses the family-level
coverage residual entirely by working with the family's own utilities per pair. -/
theorem nonPivotPairAdditivityCertificate_of_gridAdditiveRepresentationFamily_surjectivePivot
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (V₀ : X j₀ → ℝ) (hsurj : Function.Surjective V₀)
    (hslices : ∀ (k : ι) (hk : k ≠ j₀),
      ∃ Vk : X k → ℝ,
        PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) V₀ Vk ∧
        PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk) :
    ∃ V : (i : ι) → X i → ℝ,
      (∀ k : ι, k ≠ j₀ →
        PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) ∧
      NonPivotPairAdditivityCertificate P V j₀ := by
  classical
  -- Assemble the global `V` from `V₀` at `j₀` and chosen per-slice `Vk` elsewhere.
  set V : (i : ι) → X i → ℝ := fun i => if h : i = j₀ then h ▸ V₀ else
    (if hk : i ≠ j₀ then (hslices i hk).choose else fun _ => 0) with hVdef
  have hVj₀ : V j₀ = V₀ := by rw [hVdef]; simp
  have hVk : ∀ (k : ι) (hk : k ≠ j₀), V k = (hslices k hk).choose := by
    intro k hk; rw [hVdef]; simp only []; rw [dif_neg hk, dif_pos hk]
  -- Per-slice representation for the global `V`.
  have hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k) := by
    intro k hk
    rw [hVj₀, hVk k hk]
    exact ((hslices k hk).choose_spec).2
  refine ⟨V, hMatch, ?_⟩
  -- Obligation 3: each non-pivot pair via the engine-C transport with surjective V₀.
  intro j k hj hk hjk x y hagree
  have hjrep : PairwiseSliceRepresentationCertificate P j₀ j (V j₀) (V j) := hMatch j hj
  have hkrep : PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k) := hMatch k hk
  rw [hVj₀] at hjrep hkrep
  have hcov : RawAxiomDischargersHexagon.PivotCompensatesJ (X := X) V₀ (V j) :=
    RawAxiomDischargersHexagon.pivotCompensatesJ_of_surjective V₀ (V j) hsurj
  exact RawAxiomDischargersHexagon.twoPivotSliceTransport
    P (Ne.symm hj) (Ne.symm hk) hjk V₀ (V j) (V k) hjrep hkrep hcov x y hagree

/-- **Stage-4 pivot-slice representation data from the §IV.5 representation
family.**

`PairwiseSliceRepresentationsAtPivot P j₀` is, by definition,
`∃ V₀, ∀ k ≠ j₀, ∃ Vk, PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk` —
which the §IV.5 representation family `SharedPivotGridAdditiveRepresentationFamily`
supplies directly (forgetting the grid-normalization conjunct).  So the single
representation residual also discharges `WakkerStage4PivotSliceRepresentationData`,
the Stage-4 input the end-to-end closure ladder consumes.

This closes the loop: the **one** §IV.5 representation residual feeds the Stage-4
data, the Step-4 core (obl. 14), the A1 pivot-slice matches, and — with a
surjective pivot — obligation 3.  Everything downstream of the representation is
theorem-backed. -/
theorem wakkerStage4PivotSliceRepresentationData_of_gridAdditiveRepresentationFamily
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P] (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hrep : SharedPivotGridAdditiveRepresentationFamily P j₀ hdata) :
    WakkerStage4PivotSliceRepresentationData P := by
  obtain ⟨V₀, hslices⟩ := hrep
  refine ⟨j₀, V₀, ?_⟩
  intro k hk
  obtain ⟨Vk, _hnorm, hrepr⟩ := hslices k hk
  exact ⟨Vk, hrepr⟩

/-- One pivot-touching indifferent swap preserves the global additive sum for
the chosen Stage-4-matched A1 package. -/
theorem pivotTouchingIndifferenceStep_preserves_sum
    {X : ι → Type v} {P : ProductPref X}
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    {x y : Profile X}
    (hstep : PivotTouchingIndifferenceStep P hdata.j₀ x y) :
    (∑ i, hdata.V i (x i)) = (∑ i, hdata.V i (y i)) := by
  obtain ⟨k, hk, hagree, hindiff⟩ := hstep
  have hxy_sum :
      (∑ i, hdata.V i (y i)) ≤ ∑ i, hdata.V i (x i) :=
    (globalGluing_step_of_allPairsAdditivity P hdata.V hdata.hpair
      (j₀ := hdata.j₀) (i := k) hk.symm hagree).mp hindiff.1
  have hyx_sum :
      (∑ i, hdata.V i (x i)) ≤ ∑ i, hdata.V i (y i) :=
    (globalGluing_step_of_allPairsAdditivity P hdata.V hdata.hpair
      (j₀ := hdata.j₀) (i := k) hk.symm (Profile.agreeOff_symm hagree)).mp
      hindiff.2
  exact le_antisymm hyx_sum hxy_sum

/-- A finite chain of pivot-touching indifferent swaps preserves the global
additive sum for the chosen Stage-4-matched A1 package. -/
theorem pivotTouchingIndifferenceChain_preserves_sum
    {X : ι → Type v} {P : ProductPref X}
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    {x y : Profile X}
    (hchain : Relation.TransGen (PivotTouchingIndifferenceStep P hdata.j₀) x y) :
    (∑ i, hdata.V i (x i)) = (∑ i, hdata.V i (y i)) := by
  induction hchain using Relation.TransGen.trans_induction_on with
  | single hstep =>
      exact pivotTouchingIndifferenceStep_preserves_sum hdata hstep
  | trans hab hbc ihab ihbc =>
      exact ihab.trans ihbc

/-- The chosen-A1 strictness residue is recovered from the smaller
pivot-touching chain frontier. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_of_allPairsAdditivity_and_chain
    {X : ι → Type v} {P : ProductPref X}
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hchain :
      AllPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate P hdata) :
    WakkerStep5StrictMonotonicityResidualAtPivot P hdata.V hdata.j₀ := by
  intro x y hxy hnonpair
  exact pivotTouchingIndifferenceChain_preserves_sum hdata
    (hchain x y hxy hnonpair)

/-- The thin chosen-A1 strictness certificate is therefore also recovered from
the pivot-touching chain frontier. -/
theorem allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_of_pivotTouchingChain
    {X : ι → Type v} {P : ProductPref X}
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hchain :
      AllPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate P hdata) :
    AllPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate
      P hdata :=
  wakkerStep5StrictMonotonicityResidualAtPivot_of_allPairsAdditivity_and_chain
    hdata hchain

/-- **Stage-5 strictness residual from the escape residual (axiom-17-free).**

Chains the Phase-49 retargeting interface (from the minimal descending-seeded
escape residual + raw Archimedean + restricted solvability) through the
pivot-touching chain to the chosen-A1 strictness residual.  This theorem-backs
the Stage-5 strictness corridor from the **escape residual** instead of axiom 17:
the genuine reach content (a monotone Archimedean pivot grid seeded above the
target) replaces the bracket axiom. -/
theorem allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_of_descendingSeededEscape
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hgrid : PivotGridDescendingSeededAboveAtTarget P hdata.j₀) :
    AllPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate P hdata :=
  allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_of_pivotTouchingChain
    hdata
    (allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_of_pivotCoordinateRetargeting
      hdata
      (pivotCoordinateRetargetingAtPivotCertificate_of_descendingSeededAbove
        P hdata.j₀ (archimedean hdata.j₀) solvability hgrid))

/-- The thin Stage-5 strictness certificate discharges the broad residual once
the chosen Stage-4-matched A1 package has been fixed. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_of_allPairsAdditivityDrivenCertificate
    {X : ι → Type v} (P : ProductPref X)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hthin :
      AllPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate
        P hdata) :
    WakkerStep5StrictMonotonicityResidualAtPivot P hdata.V hdata.j₀ :=
  hthin

/-- The thin Stage-5 coverage certificate discharges the broad residual once
the chosen Stage-4-matched A1 package has been fixed. -/
theorem wakkerStep5CoordinateImageCoverageResidualFamily_of_allPairsAdditivityDrivenCertificate
    {X : ι → Type v} (P : ProductPref X)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hthin :
      AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate
        P hdata) :
    ∀ j₀ : ι, WakkerStep5CoordinateImageCoverageResidualAtPivot P hdata.V j₀ :=
  hthin

/- [Option A excision — axiom 6 base-transport reach axioms retired as unsound]

The two `_from_raw_axioms` base-transport reach axioms
(`pairwiseArchimedeanBaseTransportUpperReachCertificate_from_raw_axioms` and
`pairwiseArchimedeanBaseTransportLowerReachCertificate_from_raw_axioms`) and
their conjunctive assembly `pairwiseArchimedeanBaseTransportCertificate_from_raw_axioms`
were **deleted**: they asserted the base-transport bracket for *arbitrary*
one-sided ℕ-indexed standard sequences, which is **false** — machine-checked by
instantiating the assembly at `additiveRealBoolPref` (weak order + tradeoff
consistency + essentiality + restricted solvability + Archimedean) and deriving
`False` against `additiveRealBool_not_pairwiseArchimedeanBaseTransportCertificate`.

The genuine reach content is the two-sided `PairwiseBaseTransportEscapeResidual`
(defined below), which is honestly *not* derivable from the raw axioms for
one-sided grids (it needs §IV.2.6 refinement-family two-sided escape).  The
sound consumer is `pairwiseArchimedeanBaseTransportCertificate_of_escapeResidual`.
The canonical from-axioms route is now
`additiveRep_nonempty_from_structural_axioms_reachAxiomFree`. -/

/-- **Two-axis base-transport escape residual (the reach content of axiom 6).**

For every slice base/target pair agreeing off `{j, k}`, some grid profile is
**not weakly below** the target (upper escape) and some grid profile is **not
weakly above** it (lower escape).  This is the genuine Wakker §IV.3 reach content
of axiom 6 — grid unboundedness past the target at an *arbitrary* base — isolated
as one named residual, exactly parallel to the §IV.5/Step-5 escape residual
(`PivotGridEscapesAtTarget`, Phase 42) and the §IV.6 coverage residual (Phase 39).

The two directions are genuinely distinct: the additive-real counterexample
(`additiveRealBool_not_pairwiseArchimedeanBaseTransportCertificate`) fails only
the lower direction (one-sided ℕ-grids cannot reach negative-total targets from
below). -/
def PairwiseBaseTransportEscapeResidual
    {X : ι → Type v} {P : ProductPref X} {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k) : Prop :=
  ∀ base target : Profile X,
    Profile.agreeOff ({j, k} : Set ι) base target →
      (∃ n m : ℕ, ¬ P.weakPref target (PairwiseGridProfile σj σk base n m)) ∧
      (∃ n m : ℕ, ¬ P.weakPref (PairwiseGridProfile σj σk base n m) target)

/-- **Upper-reach half of axiom 6 from the escape residual (theorem-backed).**

The upper bracket `∃ n m, grid ≽ target` follows from the upper escape
`∃ n m, ¬ target ≽ grid` by completeness of the weak order: if `target` is *not*
weakly above the grid profile, then by completeness the grid profile is weakly
above `target`.  This is engine B's "reach from escape" move
(cf. `archimedean_reach_above`), lifted to the two-axis base-transport grid. -/
theorem pairwiseArchimedeanBaseTransportUpperReachCertificate_of_escapeResidual
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hesc : PairwiseBaseTransportEscapeResidual σj σk) :
    ∀ base target : Profile X,
      Profile.agreeOff ({j, k} : Set ι) base target →
        PairwiseFiniteCutUpperBracket σj σk base target := by
  intro base target hbt
  obtain ⟨⟨n, m, hn⟩, _⟩ := hesc base target hbt
  refine ⟨n, m, ?_⟩
  rcases ProductPref.IsWeakOrder.complete (P := P)
    (PairwiseGridProfile σj σk base n m) target with h | h
  · exact h
  · exact absurd h hn

/-- **Lower-reach half of axiom 6 from the escape residual (theorem-backed).**

Dual of the upper-reach discharge: the lower bracket `∃ n m, target ≽ grid`
follows from the lower escape `∃ n m, ¬ grid ≽ target` by completeness. -/
theorem pairwiseArchimedeanBaseTransportLowerReachCertificate_of_escapeResidual
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hesc : PairwiseBaseTransportEscapeResidual σj σk) :
    ∀ base target : Profile X,
      Profile.agreeOff ({j, k} : Set ι) base target →
        PairwiseFiniteCutLowerBracket σj σk base target := by
  intro base target hbt
  obtain ⟨_, ⟨n, m, hn⟩⟩ := hesc base target hbt
  refine ⟨n, m, ?_⟩
  rcases ProductPref.IsWeakOrder.complete (P := P)
    target (PairwiseGridProfile σj σk base n m) with h | h
  · exact h
  · exact absurd h hn

/-- **Conjunctive base-transport certificate from the escape residual
(theorem-backed via completeness).**

Axiom 6's full base-transport certificate is theorem-backed from the single
two-axis escape residual `PairwiseBaseTransportEscapeResidual`: each direction's
bracket follows from the corresponding escape by completeness.  This retires
axiom 6's two reach half-axioms in favor of the one escape residual — the
base-transport analogue of Phase 42's `PivotGridEscapesAtTarget` discharge.

Audit: `[propext, Classical.choice, Quot.sound]` — no `_from_raw_axioms`
dependency; completeness carries the bracket. -/
theorem pairwiseArchimedeanBaseTransportCertificate_of_escapeResidual
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hesc : PairwiseBaseTransportEscapeResidual σj σk) :
    PairwiseArchimedeanBaseTransportCertificate σj σk :=
  ⟨pairwiseArchimedeanBaseTransportUpperReachCertificate_of_escapeResidual σj σk hesc,
    pairwiseArchimedeanBaseTransportLowerReachCertificate_of_escapeResidual σj σk hesc⟩

/-- **Partial discharge of axiom 6 in the surjective-grid case.**

When both standard-sequence grids are surjective (every coordinate
value is hit by the grid map), the base-transport bridge holds via
direct grid-hit witnesses.  This is theorem-backed by the existing
`pairwiseArchimedeanBaseTransportCertificate_of_surjectiveStandardSequences`.

Audit: `[propext, Classical.choice, Quot.sound]`. -/
theorem pairwiseArchimedeanBaseTransportCertificate_from_raw_axioms_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseArchimedeanBaseTransportCertificate σj σk :=
  pairwiseArchimedeanBaseTransportCertificate_of_surjectiveStandardSequences
    P hjk σj σk hsurj_j hsurj_k

/-- **Partial discharge of axiom 6 from the exact cut-construction
certificate.**

Wakker's exact cut-construction certificate (which is itself overstrong
in the non-surjective case) directly discharges the base-transport
bridge.  Theorem-backed via
`pairwiseArchimedeanBaseTransportCertificate_of_pairwiseCutConstructionCertificate`. -/
theorem pairwiseArchimedeanBaseTransportCertificate_from_raw_axioms_of_pairwiseCutConstructionCertificate
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    {j k : ι}
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    {Vj : X j → ℝ} {Vk : X k → ℝ}
    (hcut : PairwiseCutConstructionCertificate σj σk Vj Vk) :
    PairwiseArchimedeanBaseTransportCertificate σj σk :=
  pairwiseArchimedeanBaseTransportCertificate_of_pairwiseCutConstructionCertificate hcut

/-- **Partial discharge of axiom 6 from grid reachability + surjective
second coordinate.**

When the second coordinate's grid is surjective and the first
coordinate has a `PairwiseGridReachabilityCertificate`, the
base-transport bridge follows via the existing reachability theorem. -/
theorem pairwiseArchimedeanBaseTransportCertificate_from_raw_axioms_of_gridReachability_and_surjectiveSecondCoord
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hreach : PairwiseGridReachabilityCertificate σj σk)
    (hsurj_k : Function.Surjective σk.α) :
    PairwiseArchimedeanBaseTransportCertificate σj σk :=
  pairwiseArchimedeanBaseTransportCertificate_of_gridReachability_and_surjectiveSecondCoord
    P hjk σj σk hreach hsurj_k

/-- **Partial discharge of axiom 6 from grid reachability + surjective
first coordinate.**  Symmetric companion to the previous theorem. -/
theorem pairwiseArchimedeanBaseTransportCertificate_from_raw_axioms_of_gridReachability_and_surjectiveFirstCoord
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hreach : PairwiseGridReachabilityCertificate σj σk)
    (hsurj_j : Function.Surjective σj.α) :
    PairwiseArchimedeanBaseTransportCertificate σj σk :=
  pairwiseArchimedeanBaseTransportCertificate_of_gridReachability_and_surjectiveFirstCoord
    P hjk σj σk hreach hsurj_j

/-- **Partial discharge of the upper-reach half of axiom 6 (surjective grids).**

When both standard-sequence grids are surjective, the upper-reach base-transport
half holds by direct grid-hit witnesses: project the conjunctive
`pairwiseArchimedeanBaseTransportCertificate_of_surjectiveStandardSequences`
onto its first (upper) component.  Theorem-backed; no `_from_raw_axioms`
dependency. -/
theorem pairwiseArchimedeanBaseTransportUpperReachCertificate_from_raw_axioms_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    ∀ base target : Profile X,
      Profile.agreeOff ({j, k} : Set ι) base target →
        PairwiseFiniteCutUpperBracket σj σk base target :=
  (pairwiseArchimedeanBaseTransportCertificate_of_surjectiveStandardSequences
    P hjk σj σk hsurj_j hsurj_k).1

/-- **Partial discharge of the lower-reach half of axiom 6 (surjective grids).**

Dual of the upper-reach surjective discharge: project the conjunctive
surjective base-transport certificate onto its second (lower) component. -/
theorem pairwiseArchimedeanBaseTransportLowerReachCertificate_from_raw_axioms_of_surjectiveStandardSequences
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    {j k : ι} (hjk : j ≠ k)
    (σj : ProductPref.StandardSequence P j)
    (σk : ProductPref.StandardSequence P k)
    (hsurj_j : Function.Surjective σj.α)
    (hsurj_k : Function.Surjective σk.α) :
    ∀ base target : Profile X,
      Profile.agreeOff ({j, k} : Set ι) base target →
        PairwiseFiniteCutLowerBracket σj σk base target :=
  (pairwiseArchimedeanBaseTransportCertificate_of_surjectiveStandardSequences
    P hjk σj σk hsurj_j hsurj_k).2

/- **Open obligation 2 (deprecated).**  The older bundled seam below the
broad shared-pivot Step-4 frontier was the magnitude/bracketing family.
This declaration was retired: the audit and end-to-end pipeline now route
through the honest finite-cut family
(`sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms`), which
splits the bracketing content into the smaller seams 12, 14, 15.  No
downstream code referenced the older bundled axiom. -/
section ObligationTwoBracketingFamilyDeprecated
end ObligationTwoBracketingFamilyDeprecated

/-- **Thin frontier 2a.1a.i.**  Choose only a non-pivot auxiliary coordinate
at the pivot.  This is the true residual below the pair-attached coordinate
wrapper.

Theorem-backed under `[Nontrivial ι]`: classical existence of `k ≠ j₀` from
`Nontrivial ι` (which follows automatically from
`[Fact (3 ≤ Fintype.card ι)]` adopted by every downstream consumer). -/
noncomputable def sharedPivotPivotReferenceCoordinateAtPivotData_from_raw_axioms
    {X : ι → Type v} [Nontrivial ι] (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) :
    SharedPivotPivotReferenceCoordinateAtPivotData j₀ := by
  classical
  exact ⟨(exists_ne j₀).choose, (exists_ne j₀).choose_spec⟩

/-- **Thin frontier 2a.1a.i (derived wrapper).**  Reattach the pivot-level
non-pivot coordinate choice to the theorem-backed strict pivot seed pair. -/
noncomputable def sharedPivotPivotReferenceCoordinateOnStrictPreferenceSeedPairData_from_raw_axioms
    {X : ι → Type v} [Nontrivial ι] (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) :
    SharedPivotPivotReferenceCoordinateOnStrictPreferenceSeedPairData P j₀
      (sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀) := by
  let hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀ :=
    sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀
  exact
    sharedPivotPivotReferenceCoordinateOnStrictPreferenceSeedPairData_of_referenceCoordinateAtPivotData
      P j₀ hpair
      (sharedPivotPivotReferenceCoordinateAtPivotData_from_raw_axioms
        P essential solvability archimedean j₀)

/-- **Compensated reference exchange + indifference bundle.**

Internal helper: returns the canonical reference exchange data together
with the descending seed indifference witness, all derived from the
topology bundle's compensated reference exchange theorem. -/
noncomputable def sharedPivotPivotCompensatedReferenceExchangeBundle_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    Σ' (data : SharedPivotPivotReferenceExchangeAtPivotData (X := X) j₀),
      P.indiff
        (Function.update
          (Function.update (sharedPivotPivotSeedProfileData_of_essential P essential j₀).base
            j₀ (sharedPivotPivotSeedProfileData_of_essential P essential j₀).a0)
          data.k data.r)
        (Function.update
          (Function.update (sharedPivotPivotSeedProfileData_of_essential P essential j₀).base
            j₀ (sharedPivotPivotSeedProfileData_of_essential P essential j₀).a1)
          data.k data.s) := by
  classical
  let hcoord : SharedPivotPivotReferenceCoordinateAtPivotData j₀ :=
    sharedPivotPivotReferenceCoordinateAtPivotData_from_raw_axioms
      P essential solvability archimedean j₀
  let hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀ :=
    sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀
  let r₀ : X hcoord.k := (essential hcoord.k).choose_spec.choose
  let result :=
    RawAxiomDischargersTopology.compensated_reference_exchange_of_wakkerCoordinateTopology_and_restrictedSolvability
      solvability htop hcoord.hk hpair.base hpair.a0 hpair.a1
      hpair.hweak hpair.hnotweak r₀
  let s : X hcoord.k := result.choose
  let hrs_and_indiff := result.choose_spec
  refine ⟨{ k := hcoord.k, hk := hcoord.hk, r := r₀, s := s, hrs := hrs_and_indiff.1 }, ?_⟩
  have hbase_eq :
      (sharedPivotPivotSeedProfileData_of_essential P essential j₀).base = hpair.base := by
    simp [sharedPivotPivotSeedProfileData_of_essential,
      sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair, hpair]
  have ha0_eq :
      (sharedPivotPivotSeedProfileData_of_essential P essential j₀).a0 = hpair.a0 := by
    simp [sharedPivotPivotSeedProfileData_of_essential,
      sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair, hpair]
  have ha1_eq :
      (sharedPivotPivotSeedProfileData_of_essential P essential j₀).a1 = hpair.a1 := by
    simp [sharedPivotPivotSeedProfileData_of_essential,
      sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair, hpair]
  rw [hbase_eq, ha0_eq, ha1_eq]
  exact hrs_and_indiff.2

/-- **Thin frontier 2a.1a.ii.**  Derived pivot-level reference exchange,
assembled from the chosen non-pivot coordinate, an arbitrary `r : X k`
from `Essential P k`, and the **compensating `s`** produced by the
topology bundle (Phase 5 architectural follow-on).

This is the **compensated** reference exchange constructor.  Its `s` is
chosen to make the descending seed indifference hold automatically,
retiring axioms 9 and 10 in favor of the smaller analytic axioms in
`RawAxiomDischargersTopology`. -/
noncomputable def sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotReferenceExchangeAtPivotData (X := X) j₀ :=
  (sharedPivotPivotCompensatedReferenceExchangeBundle_from_raw_axioms
    P essential solvability archimedean htop j₀).fst

/-- **Thin frontier 2a.1a.ii (derived wrapper).**  Derived reference-exchange package, assembled
from the chosen non-pivot coordinate and theorem-backed distinct reference
values on that coordinate. -/
noncomputable def sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀
      (sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀) := by
  let hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀ :=
    sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀
  exact
    sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_of_referenceExchangeAtPivotData
      P j₀ hpair
      (sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms
        P essential solvability archimedean htop j₀)

/-- **Thin frontier 2a.1a.iii (theorem-backed via the topology bundle).**

Forward weak-preference half of the descending seed comparison,
specialized to the canonical theorem-backed seed profile and canonical
raw-axiom reference exchange.

Theorem-backed by the compensated reference exchange bundle from the
topology module: the canonical reference exchange's `(r, s)` are
chosen so the descending seed indifference holds, and the forward
half of that indifference is the forward weak-preference. -/
theorem sharedPivotPivotDescendingSeedWeakPreferenceForwardOnSeedProfileAndReferenceExchangeCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotDescendingSeedWeakPreferenceForwardOnSeedProfileAndReferenceExchangeCertificate
      P j₀
      (sharedPivotPivotSeedProfileData_of_essential P essential j₀)
      (sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms
        P essential solvability archimedean htop j₀) := by
  -- Unfold the certificate.
  unfold SharedPivotPivotDescendingSeedWeakPreferenceForwardOnSeedProfileAndReferenceExchangeCertificate
  -- Use the bundled indifference witness.
  have hindiff :=
    (sharedPivotPivotCompensatedReferenceExchangeBundle_from_raw_axioms
      P essential solvability archimedean htop j₀).snd
  -- The forward half of indiff is the forward weakPref.
  -- Both sides need to match the canonical profiles in the certificate.
  show P.weakPref
    (sharedPivotPivotDescendingSeedInitialProfile_of_seedProfileAndReferenceExchange j₀ _ _)
    (sharedPivotPivotDescendingSeedSuccessorProfile_of_seedProfileAndReferenceExchange j₀ _ _)
  unfold sharedPivotPivotDescendingSeedInitialProfile_of_seedProfileAndReferenceExchange
    sharedPivotPivotDescendingSeedSuccessorProfile_of_seedProfileAndReferenceExchange
  -- These reduce to the indifference profile shapes used in the bundle.
  unfold sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms at hindiff ⊢
  exact hindiff.1

/-- **Thin frontier 2a.1a.iv (theorem-backed via the topology bundle).**

Backward weak-preference half of the descending seed comparison,
specialized to the same canonical seed / reference-exchange data. -/
theorem sharedPivotPivotDescendingSeedWeakPreferenceBackwardOnSeedProfileAndReferenceExchangeCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotDescendingSeedWeakPreferenceBackwardOnSeedProfileAndReferenceExchangeCertificate
      P j₀
      (sharedPivotPivotSeedProfileData_of_essential P essential j₀)
      (sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms
        P essential solvability archimedean htop j₀) := by
  unfold SharedPivotPivotDescendingSeedWeakPreferenceBackwardOnSeedProfileAndReferenceExchangeCertificate
  have hindiff :=
    (sharedPivotPivotCompensatedReferenceExchangeBundle_from_raw_axioms
      P essential solvability archimedean htop j₀).snd
  show P.weakPref
    (sharedPivotPivotDescendingSeedSuccessorProfile_of_seedProfileAndReferenceExchange j₀ _ _)
    (sharedPivotPivotDescendingSeedInitialProfile_of_seedProfileAndReferenceExchange j₀ _ _)
  unfold sharedPivotPivotDescendingSeedInitialProfile_of_seedProfileAndReferenceExchange
    sharedPivotPivotDescendingSeedSuccessorProfile_of_seedProfileAndReferenceExchange
  unfold sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms at hindiff ⊢
  exact hindiff.2

/-- **Thin frontier 2a.1a.iii (derived wrapper).**  Reattach the forward
weak-preference seam to the theorem-backed strict pair and pair-attached raw
reference exchange. -/
theorem sharedPivotPivotDescendingSeedWeakPreferenceForwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotDescendingSeedWeakPreferenceForwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
      P j₀
      (sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀)
      (sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_from_raw_axioms
        P essential solvability archimedean htop j₀) := by
  exact
    sharedPivotPivotDescendingSeedWeakPreferenceForwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_of_seedProfileAndReferenceExchange
      P j₀
      (sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀)
      (sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (by
        simpa [sharedPivotPivotSeedProfileData_of_essential,
          sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms] using
          (sharedPivotPivotDescendingSeedWeakPreferenceForwardOnSeedProfileAndReferenceExchangeCertificate_from_raw_axioms
            P essential solvability archimedean htop j₀))

/-- **Thin frontier 2a.1a.iv (derived wrapper).**  Reattach the backward
weak-preference seam to the theorem-backed strict pair and pair-attached raw
reference exchange. -/
theorem sharedPivotPivotDescendingSeedWeakPreferenceBackwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotDescendingSeedWeakPreferenceBackwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
      P j₀
      (sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀)
      (sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_from_raw_axioms
        P essential solvability archimedean htop j₀) := by
  exact
    sharedPivotPivotDescendingSeedWeakPreferenceBackwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_of_seedProfileAndReferenceExchange
      P j₀
      (sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀)
      (sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (by
        simpa [sharedPivotPivotSeedProfileData_of_essential,
          sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms] using
          (sharedPivotPivotDescendingSeedWeakPreferenceBackwardOnSeedProfileAndReferenceExchangeCertificate_from_raw_axioms
            P essential solvability archimedean htop j₀))

/-- **Thin frontier 2a.1a.v.**  Derived descending seed indifference,
assembled from the two one-sided weak-preference seams above on the canonical
raw-axiom reference exchange. -/
theorem sharedPivotPivotDescendingSeedIndifferenceOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotDescendingSeedIndifferenceOnStrictPreferenceSeedPairAndReferenceExchangeCertificate
      P j₀
      (sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀)
      (sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_from_raw_axioms
        P essential solvability archimedean htop j₀) := by
  exact
    sharedPivotPivotDescendingSeedIndifferenceOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_of_forward_and_backward
      P j₀
      (sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀)
      (sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (sharedPivotPivotDescendingSeedWeakPreferenceForwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (sharedPivotPivotDescendingSeedWeakPreferenceBackwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀)

/-- **Thin frontier 2a.1a.vi.**  Derived pivot seed data, assembled from the
theorem-backed strict-pair/reference-exchange layers plus the two smaller
raw-facing descending weak-preference seams above. -/
noncomputable def sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotStandardSequenceSeedData P j₀ := by
  let hpair : SharedPivotPivotStrictPreferenceSeedPairData P j₀ :=
    sharedPivotPivotStrictPreferenceSeedPairData_of_essential P essential j₀
  let href : SharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData P j₀ hpair :=
    sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_from_raw_axioms
      P essential solvability archimedean htop j₀
  exact
    sharedPivotPivotStandardSequenceSeedData_of_strictPreferenceSeedPair_referenceExchange_and_descendingSeedIndifference
      P j₀ hpair href
      (sharedPivotPivotDescendingSeedIndifferenceOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀)

/-- **Thin frontier 2a.1a.vii.**  One-step extensibility on the canonical
theorem-backed seed-profile / raw-reference context.

After adopting **Option A of the topology architectural decision** (see
`RawAxiomDischargersTopology.lean`), this is now a `theorem` rather than a
primitive `axiom`.  The discharge route is:

```
WakkerCoordinateTopology P + RestrictedSolvability P
  → CoordinateOneStepBracket P j₀ base k r s
  → ProductPref.OneStepExtensible P j₀ base k r s
```

The smaller analytic axiom
`coordinateOneStepBracket_of_wakkerCoordinateTopology` (in
`RawAxiomDischargersTopology.lean`) is the honest residual: it is the
single-line connectedness/IVT step Wakker (1989) III.4.2 uses, isolated
from the bookkeeping bracket-fills-the-gap step.

The required topology data is taken as explicit hypotheses
(`[∀ i, TopologicalSpace (X i)]` + `WakkerCoordinateTopology P`) rather
than as silent global instances.  This matches Wakker's monograph
treatment, where connectedness + continuity of `≽` are explicit
structural assumptions of the setting. -/
theorem sharedPivotPivotOneStepExtensibleOnSeedProfileAndReferenceExchangeCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotOneStepExtensibleOnSeedProfileAndReferenceExchangeCertificate
      P j₀
      (sharedPivotPivotSeedProfileData_of_essential P essential j₀)
      (sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms
        P essential solvability _archimedean htop j₀) := by
  -- Unfold the certificate: it is `OneStepExtensible P j₀ base k r s`.
  unfold SharedPivotPivotOneStepExtensibleOnSeedProfileAndReferenceExchangeCertificate
  -- The reference exchange data carries `k ≠ j₀` and `r ≠ s`.
  let href := sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms
    P essential solvability _archimedean htop j₀
  -- We need: OneStepExtensible P j₀ hseed.base href.k href.r href.s.
  -- Use the topology-bundle bridge.  Note the bridge expects `j ≠ k`, not
  -- `k ≠ j`, so we use href.hk.symm.
  exact
    RawAxiomDischargersTopology.oneStepExtensible_of_wakkerCoordinateTopology_and_restrictedSolvability
      solvability htop href.hk.symm
      (sharedPivotPivotSeedProfileData_of_essential P essential j₀).base
      href.r href.s href.hrs

/-- **Thin frontier 2a.1a.vii (derived wrapper).**  Reattach the smaller
one-step extensibility seam to the canonical pivot seed data.

Now requires `[∀ i, TopologicalSpace (X i)]` plus a
`WakkerCoordinateTopology P` bundle (see Phase 3 architectural decision in
`RawAxiomDischargersTopology.lean`). -/
theorem sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀
      (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
        P essential solvability archimedean htop j₀) := by
  exact
    sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_of_seedProfileAndReferenceExchange
      P j₀
      (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (by
        simpa [sharedPivotPivotStandardSequenceSeedData_from_raw_axioms,
          sharedPivotPivotStandardSequenceSeedData_of_strictPreferenceSeedPair_referenceExchange_and_descendingSeedIndifference,
          sharedPivotPivotSeedProfileData_of_standardSequenceSeedData,
          sharedPivotPivotReferenceExchangeAtPivotData_of_standardSequenceSeedData,
          sharedPivotPivotSeedProfileData_of_essential,
          sharedPivotPivotSeedProfileData_of_strictPreferenceSeedPair,
          sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms,
          sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_from_raw_axioms,
          sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_of_referenceExchangeAtPivotData]
          using
            (sharedPivotPivotOneStepExtensibleOnSeedProfileAndReferenceExchangeCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀))

/-- **Thin frontier 2a.1a.viii / axiom 12.**  Injectivity of the
theorem-backed pivot grid constructed from the canonical chosen seed
data and canonical one-step extension witness.

**Wakker reference:** §IV.2.6 (the Archimedean axiom in its working
form).  Wakker's argument:

1. A strict standard sequence `σ` on coordinate `j` has consecutive
   grid points in **strict** preference: `(α n) ≻ (α n+1)` at base.
2. Tradeoff consistency propagates strictness from step 0 to every
   subsequent step, so `α n ≠ α n+1` for all `n`.
3. The grid is **strictly monotone** in preference, so injective
   in `α`.

**Mathematical content:** The current generic API does not expose any
smaller theorem-backed injectivity predicate below the actual
constructed pivot sequence.  The honest residual is the entire
Wakker IV.2.6 strict-monotonicity-from-Archimedean argument, applied
to the canonical chosen seed/extension data.

**Why not yet proved:** this requires (a) a propagation lemma showing
that step-0 strictness implies every-step strictness via tradeoff
consistency, and (b) the inductive injectivity-from-monotonicity
argument.  Neither is currently in `Core.lean` for generic coordinate
types.

**Estimated effort:** 3–5 days of Wakker IV.2.6 proof work, with a
prerequisite lemma about strict-step propagation along standard
sequences.

**Decomposition (this session, spec §S0.4 / §G):** the injectivity content
factors — via the theorem-backed §F/§G propagation infrastructure in
`RawAxiomDischargersStandardSequence.lean` — into a strict seed (free from
`Essential`) plus a one-step **strict lift**, and that lift splits further into:

* a **weak-descending** family seam `hweak` — the per-step
  `weakPref (α n) (α (n+1))` lift (the genuinely deep
  single-coordinate-`r/s` reference direction of `M2Frontier`); and
* a **reverse-strict** family seam `hrev` — propagation of the
  `¬ weakPref (α (n+1)) (α n) → ¬ weakPref (α (n+2)) (α (n+1))` half.

The single monolithic injectivity axiom is therefore replaced by these two
strictly-weaker named seams, with axiom 12 re-proved as a theorem via
`sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_weakDescending_and_reverseStrict`.
Each half-seam is strictly weaker (neither alone yields injectivity), mirroring
the upper/lower splits of axioms 6 and 17. -/
theorem sharedPivotPivotGridWeakDescendingOnSeedDataCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    ∀ n,
      P.weakPref
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α n))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 1))) :=
  RawAxiomDischargersIVT.weaklyDescending_of_separable_and_isStrict
    P
    (sharedPivotPivotStandardSequence_of_seedData_and_extension
      P solvability j₀
      (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀))
    (RawAxiomDischargersTopology.coordinateWeakSeparable_of_wakkerCoordinateTopology htop j₀)
    (RawAxiomDischargersTopology.coordinateWeakSeparable_of_wakkerCoordinateTopology htop
      (sharedPivotPivotStandardSequence_of_seedData_and_extension
        P solvability j₀
        (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
          P essential solvability archimedean htop j₀)
        (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
          P essential solvability archimedean htop j₀)).k)
    (sharedPivotPivotStandardSequence_isStrict_of_seedData
      P solvability j₀
      (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀))

/-- **Reverse-strict propagation half of axiom 12.**  Propagation of the
strict-gap (`¬ weakPref` reverse direction) along the canonical constructed
pivot sequence: if the gap at step `n` does not close, neither does the gap at
step `n+1`.  Strictly weaker than the monolithic injectivity axiom. -/
theorem sharedPivotPivotGridReverseStrictOnSeedDataCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    ∀ n,
      ¬ P.weakPref
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 1)))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α n)) →
      ¬ P.weakPref
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 2)))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 1))) :=
  RawAxiomDischargersTopology.reverseStrict_family_of_wakkerCoordinateTopology
    htop
    (sharedPivotPivotStandardSequence_of_seedData_and_extension
      P solvability j₀
      (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀))

/-- **Weak-descending half of axiom 12 (12a) from the §III.4 reference-direction
residual (theorem-backed via engine B §7).**

The canonical constructed pivot sequence `σ` carries its own `spaced` field, so
the per-step weak-descending property `weakPref (α n) (α (n+1))` is exactly
`weaklyDescending_of_referenceDirection_and_cancel` applied to `σ`: the genuine
inputs are the §III.4 reference-direction transported comparison and the
coordinate cancellation, both single-coordinate-independence facts.  This
theorem-backs axiom 12a from the **same** unified §III.4 primitive that
discharges the reach/crossing frontier (axioms 6, 17, §III.4 extensibility,
Phase 47) — no separate injectivity axiom.

Audit: `[propext, Classical.choice, Quot.sound]` — the `Classical.choice` is from
the canonical sequence's `Classical.choose` construction, not a `_from_raw_axioms`
seam. -/
theorem sharedPivotPivotGridWeakDescendingOnSeedDataCertificate_of_referenceDirection_and_cancel
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (htransported : ∀ n,
      P.weakPref
        (Function.update (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α n))
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).k
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).r)
        (Function.update (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 1)))
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).k
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).r))
    (hcancel : ∀ n,
      RawAxiomDischargersIVT.CoordinateCancelAtStep P
        (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)) n) :
    ∀ n,
      P.weakPref
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α n))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 1))) :=
  RawAxiomDischargersIVT.weaklyDescending_of_referenceDirection_and_cancel P
    (sharedPivotPivotStandardSequence_of_seedData_and_extension
      P solvability j₀
      (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀))
    htransported hcancel

/-- **Obligation 12a from the reference-direction comparison alone (cancellation
discharged by the Phase-52 topology axiom).**

Tighter than `sharedPivotPivotGridWeakDescendingOnSeedDataCertificate_of_referenceDirection_and_cancel`:
the per-step cancellation hypothesis `hcancel` is now **supplied** by the
weak single-coordinate independence topology axiom (Phase 52,
`coordinateCancelAtStep_family_of_wakkerCoordinateTopology`), so axiom 12a follows
from the reference-direction transported comparison alone, on the
`WakkerCoordinateTopology` bundle.

This realizes the unification: obligation 12a's weak-descending injectivity half
needs only the §III.4 weak single-coordinate independence (the named topology
axiom) plus the transported comparison — the same single primitive underlying the
whole reach/crossing frontier. -/
theorem sharedPivotPivotGridWeakDescendingOnSeedDataCertificate_of_referenceDirection
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (htransported : ∀ n,
      P.weakPref
        (Function.update (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α n))
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).k
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).r)
        (Function.update (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 1)))
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).k
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).r)) :
    ∀ n,
      P.weakPref
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α n))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 1))) :=
  sharedPivotPivotGridWeakDescendingOnSeedDataCertificate_of_referenceDirection_and_cancel
    P essential solvability archimedean htop j₀ htransported
    (RawAxiomDischargersTopology.coordinateCancelAtStep_family_of_wakkerCoordinateTopology
      htop
      (sharedPivotPivotStandardSequence_of_seedData_and_extension
        P solvability j₀
        (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
          P essential solvability archimedean htop j₀)
        (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
          P essential solvability archimedean htop j₀)))

/-- **Obligation 12b (reverse-strict injectivity half) discharged from the
separability topology axiom.**

The reverse-strict propagation along the canonical constructed pivot sequence is
supplied directly by `RawAxiomDischargersTopology.reverseStrict_family_of_wakkerCoordinateTopology`
(Phase 58–59), which routes through the single `coordinateWeakSeparable_of_wakkerCoordinateTopology`
axiom and the sequence's `spaced` field.  This theorem-backs axiom 12b on the
canonical sequence — so **both** obligation-12 injectivity halves (12a, Phase 53;
12b, here) now come from the one §III.4 separability axiom, with no standalone
12a/12b axioms. -/
theorem sharedPivotPivotGridReverseStrictOnSeedDataCertificate_of_separability
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    ∀ n,
      ¬ P.weakPref
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 1)))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α n)) →
      ¬ P.weakPref
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 2)))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 1))) :=
  RawAxiomDischargersTopology.reverseStrict_family_of_wakkerCoordinateTopology
    htop
    (sharedPivotPivotStandardSequence_of_seedData_and_extension
      P solvability j₀
      (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀))

/- **Thin frontier 2a.1a.viii / axiom 12 (theorem-backed via §G split).**
The reassembly theorem `sharedPivotPivotGridInjectiveOnSeedDataCertificate_from_raw_axioms`
is defined further below, immediately after the §G propagation helper
`sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_weakDescending_and_reverseStrict`
that it depends on (Lean elaborates top-down, so the derived theorem must follow
that helper).  It assembles the two strictly-weaker half-seams above
(`...WeakDescendingOnSeedDataCertificate...` + `...ReverseStrictOnSeedDataCertificate...`)
into grid injectivity.  The monolithic injectivity axiom is retired in favor of
the two named seams. -/

/-- **Partial discharge of axiom 12 in the `Subsingleton (X j₀)` regime.**

If `X j₀` is a subsingleton, then any two values `a0, a1 : X j₀` are equal,
so the strict-pivot-pair seed `(hweak ∧ hnotweak)` would force a
self-comparison `weakPref X X` to fail at one direction — but
self-comparisons are reflexive under `IsWeakOrder.complete`,
contradicting `hnotweak`.

Hence under `Subsingleton (X j₀)`, the seed data structure
`SharedPivotPivotStandardSequenceSeedData P j₀` is **uninhabited**, and
the grid-injectivity certificate holds vacuously.

This isolates a real degenerate case where the cert is provable without
invoking Wakker §IV.2.6 Archimedean injectivity.  In any non-degenerate
setting (where `Essential P j₀` is satisfiable), `X j₀` necessarily has
at least two distinct values, so this discharge is genuinely
degenerate. -/
theorem sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_subsingleton
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    [Subsingleton (X j₀)]
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀)
    (hext : SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀ hseed) :
    SharedPivotPivotGridInjectiveOnSeedDataCertificate P solvability j₀ hseed hext := by
  -- Derive False from hseed.hweak + hseed.hnotweak + Subsingleton (X j₀).
  exfalso
  have ha0a1 : hseed.a0 = hseed.a1 := Subsingleton.allEq _ _
  -- The two profiles are equal under a0 = a1.
  have hupdate_eq :
      (Function.update hseed.base j₀ hseed.a0 : Profile X) =
        Function.update hseed.base j₀ hseed.a1 := by
    rw [ha0a1]
  -- hnotweak says ¬ weakPref (a1-version) (a0-version), but
  -- under hupdate_eq these are the same profile, giving weakPref by
  -- reflexivity from completeness.
  apply hseed.hnotweak
  rw [hupdate_eq]
  rcases ProductPref.IsWeakOrder.complete (P := P)
    (Function.update hseed.base j₀ hseed.a1)
    (Function.update hseed.base j₀ hseed.a1) with h | h <;> exact h

/-- **Raw-axiom-form discharge of axiom 12 in the `Subsingleton (X j₀)` regime.** -/
theorem sharedPivotPivotGridInjectiveOnSeedDataCertificate_from_raw_axioms_of_subsingleton
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    [Subsingleton (X j₀)] :
    SharedPivotPivotGridInjectiveOnSeedDataCertificate P solvability j₀
      (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀) :=
  sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_subsingleton
    P solvability j₀ _ _

/-- **Strict-step discharge of axiom 12 (spec §S0.4 route).**

The injectivity certificate `SharedPivotPivotGridInjectiveOnSeedDataCertificate`
unfolds to `Function.Injective σ.α`, where `σ` is the theorem-backed pivot
standard sequence.  By the order-theoretic injectivity lemma
`standardSequence_injective_of_strictStep` (proved in
`RawAxiomDischargersStandardSequence.lean`), this follows from the hypothesis
that **every consecutive coordinate-`j₀` step of the constructed grid is
strict**.

This reduces axiom 12 to exactly sub-part (a) of the Wakker §IV.2.6 argument
named in the axiom docstring above: the strict-step propagation along the
standard sequence.  Sub-part (b) — injectivity from monotonicity — is now a
proved theorem rather than part of the opaque axiom.  The strict-step
hypothesis `hstep` is the honest residual (Wakker propagates step-0 strictness
to every step via tradeoff consistency + the Archimedean axiom). -/
theorem sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_strictStep
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀)
    (hext : SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀ hseed)
    (hstep : ∀ n,
      P.strict
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α n))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α (n + 1)))) :
    SharedPivotPivotGridInjectiveOnSeedDataCertificate P solvability j₀ hseed hext :=
  RawAxiomDischargersStandardSequence.standardSequence_injective_of_strictStep
    P
    (sharedPivotPivotStandardSequence_of_seedData_and_extension
      P solvability j₀ hseed hext)
    hstep

/-- **Raw-axiom-form discharge of axiom 12 via the strict-step residual.**

This is the raw-facing entry point matching `axiom 12`'s exact signature,
reducing it to the strict-step hypothesis on the **theorem-backed
raw-constructed** pivot sequence rather than the opaque axiom.  Sub-part
(b) of Wakker §IV.2.6 (injectivity from monotonicity) is fully
theorem-backed; the only residual is sub-part (a), the strict-step
propagation `hstep`. -/
theorem sharedPivotPivotGridInjectiveOnSeedDataCertificate_from_raw_axioms_of_strictStep
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (hstep : ∀ n,
      P.strict
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α n))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀
            (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
              P essential solvability archimedean htop j₀)
            (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
              P essential solvability archimedean htop j₀)).α (n + 1)))) :
    SharedPivotPivotGridInjectiveOnSeedDataCertificate P solvability j₀
      (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀) :=
  sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_strictStep
    P solvability j₀ _ _ hstep

/-- **Axiom 12 discharge from the one-step strict lift (spec §S0.4 route, full).**

This is the strongest honest reduction of axiom 12 available without the
genuinely topology-derived single-coordinate reference direction.  Grid
injectivity is obtained by:

* deriving **step-0 strictness** from the seed
  (`sharedPivotPivotStandardSequence_isStrict_of_seedData`, ultimately from
  `Essential`), and
* propagating it along the sequence via the **inductive strict-step
  propagation** lemma `standardSequence_allStepsStrict_of_isStrict_and_oneStepLift`,
  whose only remaining input is the **one-step strict lift** `hlift`.

Compared with `..._of_strictStep`, which assumed *all* steps strict, this
theorem assumes only the single one-step lift residual and derives the seed
strictness internally.  The one-step lift is the documented deep residual:
per the honest `M2Frontier.lean` analysis, the hexagon `TradeoffConsistency`
does not supply it on its own (the spaced indifferences differ at both `j₀`
and `k`, failing the hexagon's `agreeOff {j₀}` shape; the genuine residual is
a single-coordinate-at-`k` reference direction). -/
theorem sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_oneStepLift
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀)
    (hext : SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀ hseed)
    (hlift : ∀ n,
      P.strict
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α n))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α (n + 1))) →
      P.strict
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α (n + 1)))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α (n + 2)))) :
    SharedPivotPivotGridInjectiveOnSeedDataCertificate P solvability j₀ hseed hext :=
  RawAxiomDischargersStandardSequence.standardSequence_injective_of_isStrict_and_oneStepLift
    P
    (sharedPivotPivotStandardSequence_of_seedData_and_extension
      P solvability j₀ hseed hext)
    (sharedPivotPivotStandardSequence_isStrict_of_seedData
      P solvability j₀ hseed hext)
    hlift

/-- **Axiom 12 discharge, fully factored (spec §S0.4 / §G route).**

The strongest honest reduction of axiom 12: grid injectivity from

* the **strict seed** (derived internally from the seed via
  `sharedPivotPivotStandardSequence_isStrict_of_seedData`, ultimately from
  `Essential`);
* the **weak descending lift** `hweak` — exactly the per-step content of
  `M2Frontier.HexagonStepLiftCertificate`, documented there as derivable from
  the genuinely deep single-coordinate-at-`k` `StandardSequenceReferenceDirection`;
  and
* the **reverse-strict propagation** `hrev` — the only new named seam.

This factors the single one-step strict lift of `..._of_oneStepLift` into the
two strictly smaller pieces of spec §G, isolating exactly where the topology-
derived content lives (the weak descending direction) versus the cheap
strict-gap propagation. -/
theorem sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_weakDescending_and_reverseStrict
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (solvability : ProductPref.RestrictedSolvability P)
    (j₀ : ι)
    (hseed : SharedPivotPivotStandardSequenceSeedData P j₀)
    (hext : SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀ hseed)
    (hweak : ∀ n,
      P.weakPref
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α n))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α (n + 1))))
    (hrev : ∀ n,
      ¬ P.weakPref
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α (n + 1)))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α n)) →
      ¬ P.weakPref
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α (n + 2)))
        (Function.update
          (sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).base j₀
          ((sharedPivotPivotStandardSequence_of_seedData_and_extension
            P solvability j₀ hseed hext).α (n + 1)))) :
    SharedPivotPivotGridInjectiveOnSeedDataCertificate P solvability j₀ hseed hext :=
  RawAxiomDischargersStandardSequence.standardSequence_injective_of_isStrict_weakDescending_reverseStrict
    P
    (sharedPivotPivotStandardSequence_of_seedData_and_extension
      P solvability j₀ hseed hext)
    (sharedPivotPivotStandardSequence_isStrict_of_seedData
      P solvability j₀ hseed hext)
    hweak hrev

/-- **Thin frontier 2a.1a.viii / axiom 12 (theorem-backed via §G split).**
Injectivity of the theorem-backed pivot grid constructed from the canonical
chosen seed data and canonical one-step extension witness.

A **theorem** (not an axiom) assembling the two strictly-weaker half-seams
`sharedPivotPivotGridWeakDescendingOnSeedDataCertificate_from_raw_axioms` and
`sharedPivotPivotGridReverseStrictOnSeedDataCertificate_from_raw_axioms` (both
declared earlier, near axiom 12's old position) through the §G propagation
helper `sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_weakDescending_and_reverseStrict`
above (which derives step-0 strictness internally from the seed, ultimately
from `Essential`).  The monolithic injectivity axiom is retired in favor of the
two named seams; each half-seam is strictly weaker (neither alone yields
injectivity), mirroring the upper/lower splits of axioms 6 and 17. -/
theorem sharedPivotPivotGridInjectiveOnSeedDataCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotGridInjectiveOnSeedDataCertificate P solvability j₀
      (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀) :=
  sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_weakDescending_and_reverseStrict
    P solvability j₀
    (sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
      P essential solvability archimedean htop j₀)
    (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
      P essential solvability archimedean htop j₀)
    (sharedPivotPivotGridWeakDescendingOnSeedDataCertificate_from_raw_axioms
      P essential solvability archimedean htop j₀)
    (sharedPivotPivotGridReverseStrictOnSeedDataCertificate_from_raw_axioms
      P essential solvability archimedean htop j₀)

/-- **Thin frontier 2a.1a.**  Derived pivot-side shared standard-sequence data,
assembled from the theorem-backed pivot constructor layer and injectivity of
the resulting grid. -/
noncomputable def sharedPivotPivotStandardSequenceData_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotPivotStandardSequenceData P j₀ := by
  let hseed : SharedPivotPivotStandardSequenceSeedData P j₀ :=
    sharedPivotPivotStandardSequenceSeedData_from_raw_axioms
      P essential solvability archimedean htop j₀
  have hext : SharedPivotPivotStandardSequenceExtensionOnSeedCertificate P j₀ hseed := by
    simpa [hseed] using
      (sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀)
  have hinj : SharedPivotPivotGridInjectiveOnSeedDataCertificate P solvability j₀ hseed hext := by
    simpa [hseed, hext] using
      (sharedPivotPivotGridInjectiveOnSeedDataCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀)
  exact
    sharedPivotPivotStandardSequenceData_of_seedData_extension_and_gridInjective
      P solvability j₀ hseed hext
      hinj

/-- **Thinning of axiom 13 via the §F/§G standard-sequence propagation
infrastructure.**

Mirrors the fully-factored pivot grid injectivity
(`sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_weakDescending_and_reverseStrict`)
across every non-pivot coordinate.  Given, for each `k ≠ j₀`, a standard
sequence `σ k hk` on `k` together with

* `hstrict` — step-`0` strictness `(σ k hk).IsStrict` (free from `Essential`);
* `hweak`   — the weak descending lift (the documented `M2Frontier`
  reference-direction residual, per coordinate); and
* `hrev`    — the reverse-strict propagation residual,

the entire non-pivot family certificate follows from
`RawAxiomDischargersStandardSequence.standardSequence_injective_of_isStrict_weakDescending_reverseStrict`
applied coordinatewise.  No opaque all-steps assumption and no dependency on
axiom 12 or axiom 13. -/
theorem sharedPivotNonpivotStandardSequenceFamilyCertificate_of_familyWeakDescending_and_reverseStrict
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (j₀ : ι)
    (σ : ∀ k : ι, k ≠ j₀ → ProductPref.StandardSequence P k)
    (hstrict : ∀ (k : ι) (hk : k ≠ j₀), (σ k hk).IsStrict)
    (hweak : ∀ (k : ι) (hk : k ≠ j₀) (n : ℕ),
      P.weakPref
        (Function.update (σ k hk).base k ((σ k hk).α n))
        (Function.update (σ k hk).base k ((σ k hk).α (n + 1))))
    (hrev : ∀ (k : ι) (hk : k ≠ j₀) (n : ℕ),
      ¬ P.weakPref
          (Function.update (σ k hk).base k ((σ k hk).α (n + 1)))
          (Function.update (σ k hk).base k ((σ k hk).α n)) →
      ¬ P.weakPref
          (Function.update (σ k hk).base k ((σ k hk).α (n + 2)))
          (Function.update (σ k hk).base k ((σ k hk).α (n + 1)))) :
    SharedPivotNonpivotStandardSequenceFamilyCertificate P j₀ := by
  intro k hk
  exact
    ⟨σ k hk,
      RawAxiomDischargersStandardSequence.standardSequence_injective_of_isStrict_weakDescending_reverseStrict
        P (σ k hk) (hstrict k hk) (hweak k hk) (hrev k hk)⟩

/- **Thin frontier 2a.1b / axiom 13 — RETIRED (Phase 13).**

This was previously a primitive `axiom`
`sharedPivotNonpivotStandardSequenceFamilyCertificate_from_raw_axioms`.
It is now **dead code** and has been deleted: the downstream consumer
`sharedPivotNonpivotStandardSequenceFamilyOnPivotDataCertificate_from_raw_axioms`
routes through the theorem
`sharedPivotNonpivotStandardSequenceFamilyCertificate_from_raw_axioms_via_pivotData`
(defined just below), which discharges the non-pivot family certificate from
**axiom 12 alone** (per-coordinate pivot-data builder), not from this axiom.

Neither end-to-end consumer (`additiveRep_nonempty_from_thin_frontier`,
`additiveRep_nonempty_from_raw_axioms`) depended on this axiom, as confirmed by
`#print axioms`.  Retiring it strictly shrinks the audit, mirroring the Phase-4
deletion of the dead axiom 7.

The degenerate-case discharge
`sharedPivotNonpivotStandardSequenceFamilyCertificate_from_raw_axioms_of_card_eq_one`
(above) and the §F/§G theorem
`sharedPivotNonpivotStandardSequenceFamilyCertificate_of_familyWeakDescending_and_reverseStrict`
remain, as they never referenced this axiom. -/

/-- **Reduction of axiom 13 to axiom 12 (per-coordinate pivot-data route).**

This realizes the reduction named in axiom 13's docstring ("once axiom 12 is
replaced by a genuine theorem, this axiom reduces to a per-coordinate
application of that theorem").  For each `k ≠ j₀`, treat `k` itself as the
pivot coordinate and invoke the theorem-backed pivot-data builder
`sharedPivotPivotStandardSequenceData_from_raw_axioms` at `k`; its fields
`σⱼ₀ : StandardSequence P k` and `hinj_j₀ : Injective σⱼ₀.α` are exactly the
witness and injectivity that the non-pivot family certificate requires.

The resulting theorem depends ONLY on axiom 12 (transitively, through the
pivot-data builder's use of
`sharedPivotPivotGridInjectiveOnSeedDataCertificate_from_raw_axioms`) and NOT
on axiom 13.  So axiom 13 is no longer an independent frontier axiom: it is
strictly subsumed by axiom 12.  Note the extra `[∀ i, TopologicalSpace (X i)]`,
`[Nontrivial ι]`, and `WakkerCoordinateTopology` premises required by the
pivot-data builder. -/
theorem sharedPivotNonpivotStandardSequenceFamilyCertificate_from_raw_axioms_via_pivotData
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotNonpivotStandardSequenceFamilyCertificate P j₀ := by
  intro k _hk
  refine ⟨?_, ?_⟩
  · exact (sharedPivotPivotStandardSequenceData_from_raw_axioms
      P essential solvability archimedean htop k).σⱼ₀
  · exact (sharedPivotPivotStandardSequenceData_from_raw_axioms
      P essential solvability archimedean htop k).hinj_j₀

/-- **Thin frontier 2a.1b (derived wrapper).**  Reattach the smaller pivot-
free non-pivot family seam to the already fixed pivot-side sequence data.

Now routed through `sharedPivotNonpivotStandardSequenceFamilyCertificate_from_raw_axioms_via_pivotData`,
so this wrapper depends only on axiom 12 (per-coordinate pivot data) and NOT on
axiom 13.  This requires the extra `[∀ i, TopologicalSpace (X i)]` and
`WakkerCoordinateTopology` premises that the pivot-data builder needs. -/
theorem sharedPivotNonpivotStandardSequenceFamilyOnPivotDataCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (hpivot : SharedPivotPivotStandardSequenceData P j₀) :
    SharedPivotNonpivotStandardSequenceFamilyOnPivotDataCertificate P j₀ hpivot :=
  sharedPivotNonpivotStandardSequenceFamilyOnPivotDataCertificate_of_nonpivotFamily
    P j₀ hpivot
    (sharedPivotNonpivotStandardSequenceFamilyCertificate_from_raw_axioms_via_pivotData
      P essential solvability archimedean htop j₀)

/-- **Thin frontier 2a.1.**  Derived shared-pivot sequence data, assembled
from the pivot-side and non-pivot-side fragments above. -/
noncomputable def sharedPivotStandardSequenceFamilyData_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotStandardSequenceFamilyData P j₀ := by
  let hpivot : SharedPivotPivotStandardSequenceData P j₀ :=
    sharedPivotPivotStandardSequenceData_from_raw_axioms
      P essential solvability archimedean htop j₀
  exact
    sharedPivotStandardSequenceFamilyData_of_pivotData_and_nonpivotFamily
      P j₀ hpivot
      (sharedPivotNonpivotStandardSequenceFamilyOnPivotDataCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀ hpivot)

/-- **Thin frontier 2a.3a / axiom 14 — RESTATED as a theorem on the named input
(endpoint 1).**

The §IV.5 Step-4 order-calibration core is machine-checked **irreducible** from
Wakker's axiom set {A1 coordinate independence + restricted solvability +
Archimedean + topology}: see `OptionB_ConsolidationSummary.md` and the probe
`OptionB_SectionIV5HardConstraints.constraint1_a1_does_not_imply_hexagon`
(a concrete `n = 3` comonotone model satisfying A1 on every coordinate yet
violating the Thomsen / `DoubleCancellation` condition), plus the seven
machine-checked irreducibility findings.

It is therefore **restated** (no longer a raw `axiom`) to consume the
proven-necessary, A1-non-derivable named structural input
`SharedPivotGridAdditiveRepresentationFamily` — the per-slice common-pivot grid
representation family, equivalently the KLST Thomsen hexagon (the standard
Wakker/KLST hypothesis) — via the theorem-backed
`sharedPivotStep4TradeoffFamilyOnDataCertificate_of_gridAdditiveRepresentationFamily`.
This eliminates the last `_from_raw_axioms` **axiom**; the genuine irreducible
content is now carried as an explicit, honest, proven-necessary hypothesis. -/
theorem sharedPivotStep4TradeoffFamilyOnDataCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (_htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (hrep : SharedPivotGridAdditiveRepresentationFamily P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P _essential _solvability _archimedean _htop j₀)) :
    SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P _essential _solvability _archimedean _htop j₀) :=
  sharedPivotStep4TradeoffFamilyOnDataCertificate_of_gridAdditiveRepresentationFamily
    P j₀
    (sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P _essential _solvability _archimedean _htop j₀)
    hrep

/-- **Thin frontier 2a.2a / axiom 14 — hexagon family (theorem-backed).**
The direct hexagon family on the canonical chosen shared-pivot data, now derived
from the strictly-leaner Step-4 order-calibration core (axiom 14') by adjoining
the theorem-backed slice-interpolation conjunct.  This is sufficient to derive
the named transport family by ignoring the finite-cut input of each
implication. -/
theorem sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (hrep : SharedPivotGridAdditiveRepresentationFamily P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀)) :
    SharedPivotHexagonFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) :=
  sharedPivotHexagonFamilyOnDataCertificate_of_step4TradeoffFamily
    P j₀
    (sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀)
    (sharedPivotStep4TradeoffFamilyOnDataCertificate_from_raw_axioms
      P essential solvability archimedean htop j₀ hrep)

/-- **Infrastructure wrapper for axiom 14 on canonical raw data.**

Reduces the canonical raw-facing hexagon-family target to the three smaller
family-level inputs on the same canonical shared-pivot data:

* Step-4 tradeoff machinery family,
* finite-cut interpolation family,
* finite-cut hexagon transport family.

This is the raw-facing specialization of
`sharedPivotHexagonFamilyOnDataCertificate_of_step4Tradeoff_finiteCutInterpolation_and_transport`.
It isolates the non-surjective residual as the transport seam while keeping the
other two components explicit and reusable. -/
theorem sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_finiteCutInterpolation_and_transport
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (htradeoff : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀))
    (hcut : SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀))
    (htransport : SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀)) :
    SharedPivotHexagonFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) := by
  let hdata : SharedPivotStandardSequenceFamilyData P j₀ :=
    sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀
  simpa [hdata] using
    (sharedPivotHexagonFamilyOnDataCertificate_of_step4Tradeoff_finiteCutInterpolation_and_transport
      P j₀ hdata htradeoff hcut htransport)

/-- **Canonical 2a.2 intermediary seam alias (non-surjective transport route).**

Named shorthand for the canonical-data intermediary hexagon-family interface
assembled from Step-4 tradeoff, finite-cut interpolation, and transport
families. -/
def sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_finiteCutInterpolation_and_transport_CanonicalResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  SharedPivotHexagonFamilyOnDataCertificate P j₀
    (sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀)

/-- Unwrap lemma for the canonical 2a.2 intermediary seam alias
(non-surjective transport route). -/
theorem sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_finiteCutInterpolation_and_transport_CanonicalResidual_iff
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_finiteCutInterpolation_and_transport_CanonicalResidual
      P essential solvability archimedean htop j₀ ↔
    SharedPivotHexagonFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) :=
  Iff.rfl

/-- Direct chaining helper from the 2a.2 intermediary theorem (non-surjective
transport route) to its canonical alias goal. -/
theorem sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_finiteCutInterpolation_and_transport_implies_sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_finiteCutInterpolation_and_transport_CanonicalResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (htradeoff : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀))
    (hcut : SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀))
    (htransport : SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀)) :
    sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_finiteCutInterpolation_and_transport_CanonicalResidual
      P essential solvability archimedean htop j₀ :=
  sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_finiteCutInterpolation_and_transport
    P essential solvability archimedean htop j₀ htradeoff hcut htransport

/-- Extra-short local sugar for the canonical 2a.2 intermediary seam alias
(non-surjective transport route). -/
abbrev canonicalSharedPivotHexagonFamilyOnDataIntermediaryResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_finiteCutInterpolation_and_transport_CanonicalResidual
    P essential solvability archimedean htop j₀

/-- **Surjective-regime infrastructure wrapper for axiom 14 on canonical raw
data.**

In the surjective-grid regime, the canonical raw-facing hexagon-family target
reduces to the Step-4 tradeoff core alone.  This packages the theorem-backed
collapse
`sharedPivotHexagonFamilyOnDataCertificate_of_step4Tradeoff_and_surjectiveGrids`
at the raw-facing canonical-data level. -/
theorem sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_surjectiveGrids
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (htradeoff : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀))
    (hsurj_j₀ : Function.Surjective
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀).σⱼ₀.α)
    (hsurj_k : ∀ (k : ι) (hk : k ≠ j₀), Function.Surjective
      ((sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀).σk k hk).α) :
    SharedPivotHexagonFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) := by
  let hdata : SharedPivotStandardSequenceFamilyData P j₀ :=
    sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀
  simpa [hdata] using
    (sharedPivotHexagonFamilyOnDataCertificate_of_step4Tradeoff_and_surjectiveGrids
      P j₀ hdata htradeoff hsurj_j₀ hsurj_k)

/-- **Canonical 2a.2 intermediary seam alias (surjective-grid route).**

Named shorthand for the canonical-data intermediary hexagon-family interface
assembled from Step-4 tradeoff plus surjective-grid hypotheses. -/
def sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_surjectiveGrids_CanonicalResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  SharedPivotHexagonFamilyOnDataCertificate P j₀
    (sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀)

/-- Unwrap lemma for the canonical 2a.2 intermediary seam alias
(surjective-grid route). -/
theorem sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_surjectiveGrids_CanonicalResidual_iff
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_surjectiveGrids_CanonicalResidual
      P essential solvability archimedean htop j₀ ↔
    SharedPivotHexagonFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) :=
  Iff.rfl

/-- Direct chaining helper from the 2a.2 intermediary theorem (surjective-grid
route) to its canonical alias goal. -/
theorem sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_surjectiveGrids_implies_sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_surjectiveGrids_CanonicalResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (htradeoff : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀))
    (hsurj_j₀ : Function.Surjective
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀).σⱼ₀.α)
    (hsurj_k : ∀ (k : ι) (hk : k ≠ j₀), Function.Surjective
      ((sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀).σk k hk).α) :
    sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_surjectiveGrids_CanonicalResidual
      P essential solvability archimedean htop j₀ :=
  sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_surjectiveGrids
    P essential solvability archimedean htop j₀ htradeoff hsurj_j₀ hsurj_k

/-- Extra-short local sugar for the canonical 2a.2 intermediary seam alias
(surjective-grid route). -/
abbrev canonicalSharedPivotHexagonFamilyOnDataSurjectiveIntermediaryResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_surjectiveGrids_CanonicalResidual
    P essential solvability archimedean htop j₀

/-- **Canonical non-surjective residual alias (transport seam).**

Named shorthand for the canonical raw-data finite-cut hexagon transport seam.
This keeps final-discharge goals concise in the non-surjective regime while
remaining definitionally identical to the underlying seam certificate. -/
def sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_from_raw_axioms_NonSurjectiveResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀
    (sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀)

/-- Extra-short local sugar for the canonical transport non-surjective
residual.  Pure abbreviation of the longer canonical alias above. -/
abbrev canonicalTransportNonSurjectiveResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_from_raw_axioms_NonSurjectiveResidual
    P essential solvability archimedean htop j₀

/-- Unwrap lemma for the canonical transport non-surjective residual alias. -/
theorem sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_from_raw_axioms_NonSurjectiveResidual_iff
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_from_raw_axioms_NonSurjectiveResidual
      P essential solvability archimedean htop j₀ ↔
    SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) :=
  Iff.rfl

/-- **Thin frontier 2a.2.**  Derived finite-cut-to-hexagon transport family on
the same canonical chosen shared-pivot data.  The stronger hexagon-family
target above is already enough to supply this implication-shaped seam. -/
theorem sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (hrep : SharedPivotGridAdditiveRepresentationFamily P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀)) :
    SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) := by
  exact
    sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_of_hexagonFamilyOnDataCertificate
      P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀)
      (sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms
        P essential solvability archimedean htop j₀ hrep)

/-- Direct chaining helper from the canonical raw transport theorem to the
named non-surjective residual alias. -/
theorem sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_from_raw_axioms_implies_sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_from_raw_axioms_NonSurjectiveResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (hrep : SharedPivotGridAdditiveRepresentationFamily P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀)) :
    sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_from_raw_axioms_NonSurjectiveResidual
      P essential solvability archimedean htop j₀ :=
  sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_from_raw_axioms
    P essential solvability archimedean htop j₀ hrep

/- **Thin frontier 2a.3a — RESTATED ON THE NAMED INPUT (endpoint 1).**  The
shared-pivot Step-4 tradeoff-machinery family on the canonical chosen
shared-pivot data was formerly the primitive
`axiom sharedPivotStep4TradeoffFamilyOnDataCertificate_from_raw_axioms`.  It is
now a **theorem** (declared above) consuming the proven-necessary, A1-non-derivable
named structural input `SharedPivotGridAdditiveRepresentationFamily` (the Thomsen
hexagon ≡ the per-slice grid representation), discharged via
`sharedPivotStep4TradeoffFamilyOnDataCertificate_of_gridAdditiveRepresentationFamily`.
This eliminates the last `_from_raw_axioms` axiom; see `OptionB_ConsolidationSummary.md`
for the machine-checked irreducibility of this content from Wakker's axiom set.
The hexagon family remains the derived theorem. -/

/- **Thin frontier 2a.3b / axiom 15 (historical narration).**  Shared-pivot
finite-cut interpolation family on the canonical chosen shared-pivot sequence
data.

**Wakker reference:** §IV.2.7 (Step 4 of standard-sequence existence:
finite-cut interpolation between consecutive grid points).

**Mathematical content:** for each non-pivot slice `(j₀, k)`, supply
the finite-cut interpolation theorem certificate on the canonical
shared-pivot grids.  This is the **interpolation** half of Wakker's
Step 4: between any two grid points (with consecutive standard-sequence
indices), Wakker's argument constructs an indifferent intermediate
profile via tradeoff consistency, allowing values strictly between the
grid points to be reached.

**Why this was C2:** the existing pairwise theorem-backed regressions
in `Certificates.lean` only lower this from the stronger exact
cut-construction theorem certificate or from the surjective-grid
degenerate case.

**Decomposition (this session, spec §2F):** the per-slice finite-cut
interpolation theorem certificate is `coverage ∧ interpolationExtension`.
The **interpolation/extension** conjunct turns out to be **fully
theorem-backed** from the weak order alone — `PairwiseInterpolationExtensionWitness`
only asks for a slice-shaped profile indifferent to `target`, and `z := target`
works unconditionally (`pairwiseInterpolationExtensionCertificate_of_surjectiveStandardSequences`,
which despite its name needs no surjectivity).  The **coverage** conjunct is the
base-transport obligation 6.  So axiom 15 is now a **theorem** with **no new
primitive seam**: its entire content reduces to obligation 6. -/

/-- **Interpolation/extension family seam — discharged as a theorem (Phase 16).**

The per-slice `PairwiseInterpolationExtensionCertificate` is provable from the
weak order alone (take the interpolation witness `z := target`, which is
reflexively indifferent and agrees off `{j₀, k}` with itself).  So this is a
theorem, not an axiom: it adds **no** primitive content to the frontier. -/
theorem sharedPivotInterpolationExtensionFamilyOnDataCertificate_from_raw_axioms
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    SharedPivotInterpolationExtensionFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) :=
  sharedPivotInterpolationExtensionFamilyOnDataCertificate_of_surjectiveGrids
    P j₀
    (sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀)

-- [Option A excision] `sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_from_raw_axioms`
-- retired: its finite-cut coverage half rested on the deleted (unsound)
-- base-transport reach axioms.  The surjective-grid form
-- (`..._of_surjectiveGrids`) remains as the sound route.

/-- **Canonical non-surjective residual alias (interpolation seam).**

Named shorthand for the canonical raw-data finite-cut interpolation seam.
Definitionally equal to the underlying certificate, but easier to target in
final-discharge proof goals for the non-surjective regime. -/
def sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_from_raw_axioms_NonSurjectiveResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀
    (sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀)

/-- Extra-short local sugar for the canonical interpolation non-surjective
residual.  Pure abbreviation of the longer canonical alias above. -/
abbrev canonicalInterpolationNonSurjectiveResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_from_raw_axioms_NonSurjectiveResidual
    P essential solvability archimedean htop j₀

/-- Unwrap lemma for the canonical interpolation non-surjective residual alias. -/
theorem sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_from_raw_axioms_NonSurjectiveResidual_iff
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_from_raw_axioms_NonSurjectiveResidual
      P essential solvability archimedean htop j₀ ↔
    SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) :=
  Iff.rfl

/-- **Surjective-regime infrastructure wrapper for axiom 15 on canonical raw
data.**

Packages the theorem-backed surjective-grid closure of the finite-cut
interpolation family at the raw-facing canonical shared-pivot data level. -/
theorem sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_from_raw_axioms_of_surjectiveGrids
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (hsurj_j₀ : Function.Surjective
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀).σⱼ₀.α)
    (hsurj_k : ∀ (k : ι) (hk : k ≠ j₀), Function.Surjective
      ((sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀).σk k hk).α) :
    SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) := by
  let hdata : SharedPivotStandardSequenceFamilyData P j₀ :=
    sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀
  simpa [hdata] using
    (sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_of_surjectiveGrids
      P j₀ hdata hsurj_j₀ hsurj_k)

-- [Option A excision] `..._from_raw_axioms_implies_..._NonSurjectiveResidual`
-- retired with the deleted interpolation family theorem.

/-- **Infrastructure wrapper for thin frontier 2a.3 on canonical raw data.**

On the canonical chosen shared-pivot data, reduce the finite-cut family target
to the theorem-backed constructor from the Step-4 tradeoff family and the
finite-cut interpolation family.  This names the intermediate interface so the
raw-facing wrapper can avoid jumping directly into the low-level constructor. -/
theorem sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_finiteCutInterpolation
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (htradeoff : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀))
    (hcut : SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀)) :
    SharedPivotMagnitudeFiniteCutFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) := by
  let hdata : SharedPivotStandardSequenceFamilyData P j₀ :=
    sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀
  simpa [hdata] using
    (sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_of_step4Tradeoff_and_finiteCutInterpolation
      P j₀ hdata htradeoff hcut)

/-- **Canonical 2a.3 intermediary seam alias.**

Named shorthand for the canonical-data intermediary finite-cut family interface
in thin frontier 2a.3. -/
def sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_finiteCutInterpolation_CanonicalResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  SharedPivotMagnitudeFiniteCutFamilyOnDataCertificate P j₀
    (sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀)

/-- Unwrap lemma for the canonical 2a.3 intermediary seam alias. -/
theorem sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_finiteCutInterpolation_CanonicalResidual_iff
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_finiteCutInterpolation_CanonicalResidual
      P essential solvability archimedean htop j₀ ↔
    SharedPivotMagnitudeFiniteCutFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀) :=
  Iff.rfl

/-- Direct chaining helper from the 2a.3 intermediary theorem to its canonical
alias goal. -/
theorem sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_finiteCutInterpolation_implies_sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_finiteCutInterpolation_CanonicalResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (htradeoff : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀))
    (hcut : SharedPivotFiniteCutInterpolationFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀)) :
    sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_finiteCutInterpolation_CanonicalResidual
      P essential solvability archimedean htop j₀ :=
  sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_finiteCutInterpolation
    P essential solvability archimedean htop j₀ htradeoff hcut

/-- Extra-short local sugar for the canonical 2a.3 intermediary seam alias. -/
abbrev canonicalSharedPivotMagnitudeFiniteCutFamilyOnDataIntermediaryResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_finiteCutInterpolation_CanonicalResidual
    P essential solvability archimedean htop j₀

-- [Option A excision] `sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms`
-- retired: it supplied the finite-cut family from the deleted interpolation
-- family (which rested on the unsound base-transport reach axioms).  The
-- parameterized helper `..._of_step4Tradeoff_and_finiteCutInterpolation` (which
-- takes the finite-cut family as an argument) remains as the sound interface.

/-- **Infrastructure wrapper for thin frontier 2a on canonical raw data.**

On the canonical chosen shared-pivot data, reduce the bundled transport-family
target to the theorem-backed constructor from the finite-cut family and the
transport family on that same data.  This names the intermediate interface so
the raw-facing wrapper avoids jumping directly into the low-level constructor. -/
theorem sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms_of_magnitudeFiniteCutFamily_and_transportOnData
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (hfinite : SharedPivotMagnitudeFiniteCutFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀))
    (htransport : SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀)) :
    SharedPivotMagnitudeFiniteCutTransportFamilyCertificate P j₀ := by
  let hdata : SharedPivotStandardSequenceFamilyData P j₀ :=
    sharedPivotStandardSequenceFamilyData_from_raw_axioms
      P essential solvability archimedean htop j₀
  have hfinite' : SharedPivotMagnitudeFiniteCutFamilyOnDataCertificate P j₀ hdata := by
    simpa [hdata] using hfinite
  have htransport' : SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀ hdata := by
    simpa [hdata] using htransport
  exact
    sharedPivotMagnitudeFiniteCutTransportFamilyCertificate_of_data_and_components
      P j₀ hdata
      hfinite'
      htransport'

/-- **Canonical 2a intermediary seam alias.**

Named shorthand for the canonical-data intermediary bundled transport-family
interface in thin frontier 2a. -/
def sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms_of_magnitudeFiniteCutFamily_and_transportOnData_CanonicalResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  SharedPivotMagnitudeFiniteCutTransportFamilyCertificate P j₀

/-- Unwrap lemma for the canonical 2a intermediary seam alias. -/
theorem sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms_of_magnitudeFiniteCutFamily_and_transportOnData_CanonicalResidual_iff
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) :
    sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms_of_magnitudeFiniteCutFamily_and_transportOnData_CanonicalResidual
      P essential solvability archimedean htop j₀ ↔
    SharedPivotMagnitudeFiniteCutTransportFamilyCertificate P j₀ :=
  Iff.rfl

/-- Direct chaining helper from the 2a intermediary theorem to its canonical
alias goal. -/
theorem sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms_of_magnitudeFiniteCutFamily_and_transportOnData_implies_sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms_of_magnitudeFiniteCutFamily_and_transportOnData_CanonicalResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (hfinite : SharedPivotMagnitudeFiniteCutFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀))
    (htransport : SharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate P j₀
      (sharedPivotStandardSequenceFamilyData_from_raw_axioms
        P essential solvability archimedean htop j₀)) :
    sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms_of_magnitudeFiniteCutFamily_and_transportOnData_CanonicalResidual
      P essential solvability archimedean htop j₀ :=
  sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms_of_magnitudeFiniteCutFamily_and_transportOnData
    P essential solvability archimedean htop j₀ hfinite htransport

/-- Extra-short local sugar for the canonical 2a intermediary seam alias. -/
abbrev canonicalSharedPivotMagnitudeFiniteCutTransportIntermediaryResidual
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) : Prop :=
  sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms_of_magnitudeFiniteCutFamily_and_transportOnData_CanonicalResidual
    P essential solvability archimedean htop j₀

-- [Option A excision] `sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms`
-- retired: it supplied the magnitude finite-cut family from the deleted
-- `sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms` (which
-- rested on the unsound base-transport reach axioms).  The parameterized helper
-- `..._of_magnitudeFiniteCutFamily_and_transportOnData` remains as the sound interface.

/-- **Thin frontier 3 / axiom 16.**  Local transport from two pivot
slices with a common pivot utility into the corresponding non-pivot
slice.

**Wakker reference:** §IV.6 (Thomsen-condition transport / hexagon
condition for cross-coordinate independence).

**Mathematical content:** Given two pivot slices `(j₀, j)` and
`(j₀, k)` represented additively by utilities `(V₀, Vⱼ)` and
`(V₀, Vₖ)` (sharing the pivot `V₀`), conclude that the non-pivot pair
`(j, k)` is also represented additively by `(Vⱼ, Vₖ)`.

This is **Wakker IV.6's main cross-pair theorem** in its smallest
honest form.  The argument uses the Thomsen (hexagon) condition: if
two pivot slices are linearly compatible via a common pivot utility,
then any "hexagon" of cross-coordinate updates closes by tradeoff
consistency, propagating the additive representation to the non-pivot
pair.

**Why this is heavy:** Wakker's IV.6 chapter is a multi-page argument
involving careful manipulation of indifference triangles (hexagons)
and use of the connectedness of the slice utility images.  Lifting it
to generic coordinate types requires either density assumptions or a
constructive argument from `RestrictedSolvability`.

The only downstream consumer of the broader ambient-`V` wrapper
`PivotHexagonTransportCertificate P V j₀` uses `V` solely through the
two slice witnesses, so this local form is a strictly cleaner residual.

**Estimated effort:** 3–6 weeks.  The genuine Wakker IV.6 content.

**Decomposition (this session):** the output `PairwiseSliceRepresentationCertificate`
is the biconditional `weakPref x y ↔ Vⱼ(y)+Vₖ(y) ≤ Vⱼ(x)+Vₖ(x)`.  Following the
directional-split methodology (axioms 6, 12, 17), the single conjunctive
transport axiom is replaced by two strictly-weaker named seams — a **forward**
seam (`weakPref → score-inequality`) and a **backward** seam (`score-inequality
→ weakPref`) — and the conjunction is proved as a theorem.  Each half-seam is
strictly weaker (it postulates only one implication direction of the Thomsen
transport). -/
-- [Option A restate] axiom 16 forward/backward seams converted from raw `axiom`s
-- into sound theorems consuming the pivot coverage residual
-- `TwoPivotSliceTransportCoverageResidual` (the genuine §IV.6 content, itself
-- dischargeable from a surjective / connected+continuous+unbounded pivot via
-- `pivotCompensatesJ_of_surjective` / `surjective_of_continuous_unbounded`).
-- The previous raw axioms were a soundness risk: the transport reduces to pivot
-- coverage `PivotCompensatesJ`, which is provably false for a bounded pivot
-- utility and is NOT supplied by `RestrictedSolvability` (betweenness only).
theorem twoPivotSliceTransportForwardCertificate_from_raw_axioms
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀) :
    TwoPivotSliceTransportForwardCertificate P j₀ :=
  twoPivotSliceTransportForwardCertificate_of_coverageResidual P j₀ hcov

/-- **Backward half of axiom 16 (restated, sound).**  The `←` direction of the
Thomsen transport, derived from the pivot coverage residual. -/
theorem twoPivotSliceTransportBackwardCertificate_from_raw_axioms
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀) :
    TwoPivotSliceTransportBackwardCertificate P j₀ :=
  twoPivotSliceTransportBackwardCertificate_of_coverageResidual P j₀ hcov

/-- **Thin frontier 3 / axiom 16 (restated, sound).**
Local transport from two pivot slices with a common pivot utility into the
corresponding non-pivot slice, derived from the pivot coverage residual
`TwoPivotSliceTransportCoverageResidual` via the engine-C theorem
`twoPivotSliceTransportCertificate_of_coverageResidual`. -/
theorem twoPivotSliceTransportCertificate_from_raw_axioms
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀) :
    TwoPivotSliceTransportCertificate P j₀ :=
  twoPivotSliceTransportCertificate_of_coverageResidual P j₀ hcov

/-- **Local two-pivot transport seam alias.**

Named shorthand for the honest IV.6 local residual on a fixed pivot `j₀`.
Definitionally equal to `TwoPivotSliceTransportCertificate P j₀`, but cleaner
to target in endgame proofs and audits. -/
def twoPivotSliceTransportCertificate_from_raw_axioms_Residual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) : Prop :=
  TwoPivotSliceTransportCertificate P j₀

/-- Unwrap lemma for the local two-pivot transport seam alias. -/
theorem twoPivotSliceTransportCertificate_from_raw_axioms_Residual_iff
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) :
    twoPivotSliceTransportCertificate_from_raw_axioms_Residual
      P essential solvability archimedean j₀ ↔
    TwoPivotSliceTransportCertificate P j₀ :=
  Iff.rfl

/-- Direct chaining helper from the raw two-pivot transport theorem to the
named local residual alias. -/
theorem twoPivotSliceTransportCertificate_from_raw_axioms_implies_twoPivotSliceTransportCertificate_from_raw_axioms_Residual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀) :
    twoPivotSliceTransportCertificate_from_raw_axioms_Residual
      P essential solvability archimedean j₀ :=
  twoPivotSliceTransportCertificate_from_raw_axioms
    P essential solvability archimedean j₀ hcov

/-- Extra-short local sugar for the two-pivot transport residual. -/
abbrev canonicalTwoPivotTransportResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) : Prop :=
  twoPivotSliceTransportCertificate_from_raw_axioms_Residual
    P essential solvability archimedean j₀

/-- **Thin frontier 3 (derived wrapper).**  Reattach the local two-pivot-slice
transport seam to an ambient matched utility family `V`. -/
theorem pivotHexagonTransportCertificate_from_raw_axioms
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) (V : (i : ι) → X i → ℝ)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀) :
    PivotHexagonTransportCertificate P V j₀ := by
  exact
    pivotHexagonTransportCertificate_of_twoPivotSliceTransportCertificate
      P j₀
      (twoPivotSliceTransportCertificate_from_raw_axioms
        P essential solvability archimedean j₀ hcov)
      V

/-- **Stage-matched IV.6 transport wrapper.**

Consumer-facing packaging of the local two-pivot transport seam on a chosen
`Stage4MatchedAllPairsAdditivityData P` package: once `hdata` is fixed, recover
the ambient-`V` pivot-hexagon transport certificate for `hdata.V` at its chosen
pivot `hdata.j₀`. -/
theorem pivotHexagonTransportCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hcov : TwoPivotSliceTransportCoverageResidual P hdata.j₀) :
    PivotHexagonTransportCertificate P hdata.V hdata.j₀ :=
  pivotHexagonTransportCertificate_from_raw_axioms
    P essential solvability archimedean hdata.j₀ hdata.V hcov

/-- **Stage-matched pivot-hexagon transport seam alias.**

Named shorthand for the chosen-`V` IV.6 transport interface on a fixed
`Stage4MatchedAllPairsAdditivityData P` package. -/
def pivotHexagonTransportCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  PivotHexagonTransportCertificate P hdata.V hdata.j₀

/-- Unwrap lemma for the stage-matched pivot-hexagon transport seam alias. -/
theorem pivotHexagonTransportCertificate_from_raw_axioms_StageMatchedResidual_iff
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) :
    pivotHexagonTransportCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata ↔
    PivotHexagonTransportCertificate P hdata.V hdata.j₀ :=
  Iff.rfl

/-- Direct chaining helper from the stage-matched pivot-hexagon transport
theorem to its named alias goal. -/
theorem pivotHexagonTransportCertificate_from_raw_axioms_implies_pivotHexagonTransportCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hcov : TwoPivotSliceTransportCoverageResidual P hdata.j₀) :
    pivotHexagonTransportCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata :=
  pivotHexagonTransportCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    P essential solvability archimedean hdata hcov

/-- Extra-short local sugar for the stage-matched pivot-hexagon transport seam
alias. -/
abbrev canonicalStageMatchedPivotHexagonTransportResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  pivotHexagonTransportCertificate_from_raw_axioms_StageMatchedResidual
    P essential solvability archimedean hdata

/-- **Thin frontier 4 / axiom 17.**  The genuine chain content below
the chosen-A1 strictness residue: a per-target pivot-retargeting
bracketing.

**Wakker reference:** §IV.5 + §IV.2 (Archimedean reachability for
arbitrary base profiles, applied to single-coordinate retargeting).

**Mathematical content:** for any target profile, any non-pivot
coordinate `k ≠ j₀`, and any `vk : X k`, find pivot values `v, w` such
that the perturbed-then-pivot-adjusted profiles bracket `target` in
preference.  This is per-base Archimedean reachability — it requires
the pivot coordinate's standard sequences to cover **arbitrary base
profiles**, not just standard-sequence-aligned ones.

**Why this is C2:** the Archimedean axiom is structurally about
specific standard-sequence grids, but the conclusion here is about
arbitrary bases.  Bridging this requires either (a) a base-transport
argument (related to axiom 6 but for the pivot coordinate alone) or
(b) a constructive argument using `RestrictedSolvability` to interpolate
between bracket endpoints.

**Estimated effort:** 1–2 weeks.  Reuses some infrastructure from the
axiom 6 effort.

**Decomposition (this session):** the conjunctive bracket is split into
two strictly smaller named seams — an upper-reach axiom
(`pivotCoordinateRetargetingBracketUpperReachAtPivotCertificate_from_raw_axioms`)
and a lower-reach axiom
(`pivotCoordinateRetargetingBracketLowerReachAtPivotCertificate_from_raw_axioms`).
The conjunctive certificate is then proved as a theorem.  Each half-axiom is
strictly weaker than the original (it postulates only one direction of the
bracket), mirroring the upper/lower split already used for
`coordinateOneStepBracket_of_wakkerCoordinateTopology` in
`RawAxiomDischargersTopology.lean`. -/
-- [Option A restate] axiom 17 retired as raw axioms.  The pivot-retargeting
-- bracket is a coverage/reach condition over the pivot coordinate, NOT supplied
-- by RestrictedSolvability (betweenness only) — the same gap as axiom 6, but over
-- the full coordinate.  It is restated as a theorem consuming the two-sided pivot
-- escape residual `PivotGridEscapesAtTarget` (the genuine §IV.2 Archimedean reach
-- content), routed through the engine-B theorem
-- `pivotCoordinateRetargetingBracketAtPivotCertificate_of_pivotGridEscapes`.
theorem pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hesc : PivotGridEscapesAtTarget P j₀) :
    PivotCoordinateRetargetingBracketAtPivotCertificate P j₀ :=
  pivotCoordinateRetargetingBracketAtPivotCertificate_of_pivotGridEscapes
    P j₀ (archimedean j₀) hesc

/-- **Partial discharge of the upper-reach half of axiom 17 in `card ι = 1`.**

When `Fintype.card ι = 1`, the inner `∀ k : ι, k ≠ j₀` is vacuous since the
only coordinate is `j₀` itself, so the upper-reach seam holds trivially without
any of the raw axioms.  This is a genuine theorem-backed discharge of the
upper-reach half-axiom in the degenerate singleton regime; the real Wakker
§IV.5 + §IV.2 per-base reachability content lives in the `card ι ≥ 2` regime. -/
theorem pivotCoordinateRetargetingBracketUpperReachAtPivotCertificate_of_card_eq_one
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hcard : Fintype.card ι = 1) :
    ∀ target : Profile X,
      ∀ k : ι, k ≠ j₀ →
        ∀ vk : X k,
          ∃ v : X j₀,
            P.weakPref (Function.update (Function.update target k vk) j₀ v) target := by
  intro _target k hk _vk
  exfalso
  have h2 : 2 ≤ Fintype.card ι := by
    calc 2 = ({j₀, k} : Finset ι).card := by
            rw [Finset.card_insert_of_notMem (by simpa using Ne.symm hk),
                Finset.card_singleton]
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **Partial discharge of the lower-reach half of axiom 17 in `card ι = 1`.**

Dual to the upper-reach singleton discharge: the inner `∀ k : ι, k ≠ j₀` is
vacuous when `Fintype.card ι = 1`, so the lower-reach seam holds trivially. -/
theorem pivotCoordinateRetargetingBracketLowerReachAtPivotCertificate_of_card_eq_one
    {X : ι → Type v} (P : ProductPref X) (j₀ : ι)
    (hcard : Fintype.card ι = 1) :
    ∀ target : Profile X,
      ∀ k : ι, k ≠ j₀ →
        ∀ vk : X k,
          ∃ w : X j₀,
            P.weakPref target (Function.update (Function.update target k vk) j₀ w) := by
  intro _target k hk _vk
  exfalso
  have h2 : 2 ≤ Fintype.card ι := by
    calc 2 = ({j₀, k} : Finset ι).card := by
            rw [Finset.card_insert_of_notMem (by simpa using Ne.symm hk),
                Finset.card_singleton]
      _ ≤ Fintype.card ι := Finset.card_le_univ _
  omega

/-- **Thin frontier 4A → 4 (derived wrapper).**  In the `card ι ≥ 3` regime
actually used downstream, the smaller one-step pivot-retargeting bracketing
seam already implies the broader finite-chain frontier. -/
theorem allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_pivotCoordinateRetargetingBracket
    {X : ι → Type v} [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    AllPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate P hdata := by
  exact
    allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_of_pivotCoordinateRetargeting
      hdata
      (pivotCoordinateRetargetingAtPivotCertificate_of_bracketing_and_restrictedSolvability
        P hdata.j₀
        (pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms
          P essential solvability archimedean hdata.j₀ hesc)
        solvability)

/-- **Compatibility seam alias for the 4A→4 bridge wrapper.**

Named shorthand for the bridge from the chosen-pivot retargeting bracketing
seam to the broader pivot-touching chain frontier. -/
def allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_pivotCoordinateRetargetingBracket_CompatibilityResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  AllPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate P hdata

/-- Unwrap lemma for the 4A→4 bridge compatibility seam alias. -/
theorem allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_pivotCoordinateRetargetingBracket_CompatibilityResidual_iff
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) :
    allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_pivotCoordinateRetargetingBracket_CompatibilityResidual
      P essential solvability archimedean hdata ↔
    AllPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate P hdata :=
  Iff.rfl

/-- Direct chaining helper from the 4A→4 bridge wrapper to its compatibility
alias goal. -/
theorem allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_pivotCoordinateRetargetingBracket_implies_allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_pivotCoordinateRetargetingBracket_CompatibilityResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_pivotCoordinateRetargetingBracket_CompatibilityResidual
      P essential solvability archimedean hdata :=
  allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_pivotCoordinateRetargetingBracket
    P essential solvability archimedean hdata hesc

/-- Extra-short local sugar for the 4A→4 bridge compatibility seam alias. -/
abbrev canonicalPivotTouchingChainBridgeCompatibilityResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_pivotCoordinateRetargetingBracket_CompatibilityResidual
    P essential solvability archimedean hdata

/-- **Stage-matched pivot-retargeting wrapper.**

For a fixed chosen `Stage4MatchedAllPairsAdditivityData P` package, the honest
one-step pivot-retargeting bracketing seam specializes immediately to the
chosen pivot `hdata.j₀`.  This keeps the strictness corridor consumer-facing at
the same `hdata` granularity as the IV.6 and Stage-5 wrappers. -/
theorem pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    PivotCoordinateRetargetingBracketAtPivotCertificate P hdata.j₀ :=
  pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms
    P essential solvability archimedean hdata.j₀ hesc

/-- **Stage-matched pivot-retargeting seam alias.**

Named shorthand for the chosen-pivot one-step retargeting bracketing seam on a
fixed `Stage4MatchedAllPairsAdditivityData P` package. -/
def pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  PivotCoordinateRetargetingBracketAtPivotCertificate P hdata.j₀

/-- Unwrap lemma for the stage-matched pivot-retargeting seam alias. -/
theorem pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_StageMatchedResidual_iff
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) :
    pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata ↔
    PivotCoordinateRetargetingBracketAtPivotCertificate P hdata.j₀ :=
  Iff.rfl

/-- Direct chaining helper from the stage-matched pivot-retargeting theorem to
its named alias goal. -/
theorem pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_implies_pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata :=
  pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    P essential solvability archimedean hdata hesc

/-- Extra-short local sugar for the stage-matched pivot-retargeting seam alias. -/
abbrev canonicalStageMatchedPivotRetargetingResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    P essential solvability archimedean hdata

/-- **Stage-matched one-step retargeting wrapper.**

For a fixed chosen `Stage4MatchedAllPairsAdditivityData P` package, the
theorem-backed one-step pivot-compensated retargeting interface is recovered
directly from the smaller chosen-pivot bracketing seam plus restricted
solvability. -/
theorem pivotCoordinateRetargetingAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    PivotCoordinateRetargetingAtPivotCertificate P hdata.j₀ :=
  pivotCoordinateRetargetingAtPivotCertificate_of_bracketing_and_restrictedSolvability
    P hdata.j₀
    (pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
      P essential solvability archimedean hdata hesc)
    solvability

/-- **Stage-matched one-step retargeting seam alias.**

Named shorthand for the chosen-pivot one-step retargeting interface on a fixed
`Stage4MatchedAllPairsAdditivityData P` package. -/
def pivotCoordinateRetargetingAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  PivotCoordinateRetargetingAtPivotCertificate P hdata.j₀

/-- Unwrap lemma for the stage-matched one-step retargeting seam alias. -/
theorem pivotCoordinateRetargetingAtPivotCertificate_from_raw_axioms_StageMatchedResidual_iff
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) :
    pivotCoordinateRetargetingAtPivotCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata ↔
    PivotCoordinateRetargetingAtPivotCertificate P hdata.j₀ :=
  Iff.rfl

/-- Direct chaining helper from the stage-matched one-step retargeting theorem
to its named alias goal. -/
theorem pivotCoordinateRetargetingAtPivotCertificate_from_raw_axioms_implies_pivotCoordinateRetargetingAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    pivotCoordinateRetargetingAtPivotCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata :=
  pivotCoordinateRetargetingAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    P essential solvability archimedean hdata hesc

/-- Extra-short local sugar for the stage-matched one-step retargeting seam
alias. -/
abbrev canonicalStageMatchedPivotRetargetingStepResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  pivotCoordinateRetargetingAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    P essential solvability archimedean hdata

/-- **Stage-matched chain wrapper below chosen-A1 strictness.**

Once the chosen Stage-4-matched package `hdata` is fixed, the broader
pivot-touching chain frontier is recovered directly from the smaller chosen-
pivot retargeting bracketing seam. -/
theorem allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    {X : ι → Type v} [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    AllPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate P hdata := by
  exact
    allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_of_pivotCoordinateRetargeting
      hdata
      (pivotCoordinateRetargetingAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
        P essential solvability archimedean hdata hesc)

/-- **Stage-matched pivot-touching chain seam alias.**

Named shorthand for the chosen-`V` pivot-touching chain frontier on a fixed
`Stage4MatchedAllPairsAdditivityData P` package. -/
def allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  AllPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate P hdata

/-- Unwrap lemma for the stage-matched pivot-touching chain seam alias. -/
theorem allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_StageMatchedResidual_iff
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) :
    allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata ↔
    AllPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate P hdata :=
  Iff.rfl

/-- Direct chaining helper from the stage-matched pivot-touching chain theorem
to its named alias goal. -/
theorem allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_implies_allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata :=
  allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    P essential solvability archimedean hdata hesc

/-- Extra-short local sugar for the stage-matched pivot-touching chain seam
alias. -/
abbrev canonicalStageMatchedPivotTouchingChainResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    P essential solvability archimedean hdata

/-- **Thin frontier 4 (theorem-backed under `[Fact (3 ≤ Fintype.card ι)]`).**

Now retired as a primitive axiom and discharged via
`allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_pivotCoordinateRetargetingBracket`,
which routes through axiom 17 (`pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms`).

The `card ι ≥ 3` instance is required because the chain construction
needs a non-pivot coordinate witness for each step.  Every downstream
consumer of this declaration has `[Fact (3 ≤ Fintype.card ι)]` already,
so this is not a new structural constraint. -/
theorem allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    AllPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate P hdata :=
  allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    P essential solvability archimedean hdata hesc

/-- **Stage-matched strictness wrapper below chosen-A3 strictness.**

Once the chosen Stage-4-matched package `hdata` is fixed, the broader
strict-monotonicity residual is recovered directly from the smaller chosen-`V`
pivot-touching chain frontier. -/
theorem allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    AllPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate P hdata := by
  exact
    allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_of_pivotTouchingChain
      hdata
      (allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
        P essential solvability archimedean hdata hesc)

/-- **Thin frontier 4 (derived wrapper).**  Recover the chosen-A1 strictness
residue from the smaller pivot-touching chain seam. -/
theorem allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
  (hdata : Stage4MatchedAllPairsAdditivityData P)
  (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
  AllPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate P hdata := by
  exact
    allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
      P essential solvability archimedean hdata hesc

/-- **Stage-matched strictness seam alias.**

Named shorthand for the chosen-`V` Stage-5 strictness residual seam on a fixed
`Stage4MatchedAllPairsAdditivityData P` package. -/
def allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  AllPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate
    P hdata

/-- Unwrap lemma for the stage-matched strictness seam alias. -/
theorem allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual_iff
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) :
    allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata ↔
    AllPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate
      P hdata :=
  Iff.rfl

/-- Direct chaining helper from the raw stage-matched strictness seam to its
named alias goal. -/
theorem allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_implies_allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata :=
  allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms
    P essential solvability archimedean hdata hesc

/-- Extra-short local sugar for the stage-matched strictness seam alias. -/
abbrev canonicalStageMatchedStrictnessResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    P essential solvability archimedean hdata

/-- **Thin frontier 5 / axiom 19.**  The Stage-5 coverage residue
below the overstrong arbitrary-`V` frontier: only promise the per-pivot
coverage family on that same chosen Stage-4-matched A1 package.

**Wakker reference:** §IV.6 + §IV.2.7 (Step 5 of additive
representation: realize the canonical pivot value computed from the
all-pairs additivity equation in the image of `V j₀`).

**Mathematical content:** for the chosen all-pairs-additivity utility
family `V`, the canonical pivot value satisfying the all-pairs equation
is realized by some `c : X j₀`, i.e., `V j₀ c = (target value)`.  This
is **coordinate-image coverage**.

**Why this is C3:** without continuity of `V j₀` and density of the
standard-sequence grid (both currently passed in as end-to-end inputs
`hcont`, `hdense_grid`), this axiom is unreachable from the raw axioms
alone.  Wakker's monograph derives it from connectedness + IVT applied
to the continuous coordinate utility, plus density of the rational
grid points within `Set.range (V j₀)`.

**Estimated effort:** 2–4 weeks.  The hardest residual on the list
that depends on continuity / density data not present in the four raw
axioms.  In Wakker's setting this is automatic from his structural
inputs, but lifting to Lean's typed-skeleton form requires either
adopting those structural inputs as instances or adding an
`AdditiveRep`-aware variant. -/
-- [Option A restate] axiom 19 retired as a raw axiom.  Coordinate-image coverage
-- (`∃ c : X j₀` realizing the canonical pivot value) is a coverage condition over
-- the pivot coordinate, NOT supplied by RestrictedSolvability (betweenness only);
-- per the repo's own note it is "unreachable from the raw axioms alone… derived
-- from connectedness + IVT".  It is restated to consume the coverage residual as
-- an explicit (non-circular) hypothesis, surfacing the genuine §IV.6 content.
theorem allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hcov19 : AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate P hdata) :
    AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate
    P hdata :=
  hcov19

/-- **Stage-matched coverage seam alias.**

Named shorthand for the chosen-`V` Stage-5 coordinate-image coverage residual
seam on a fixed `Stage4MatchedAllPairsAdditivityData P` package.  This keeps
endgame goals shorter while remaining definitionally equal to the underlying
certificate. -/
def allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate
    P hdata

/-- Unwrap lemma for the stage-matched coverage seam alias. -/
theorem allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual_iff
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) :
    allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata ↔
    AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate
      P hdata :=
  Iff.rfl

/-- Direct chaining helper from the raw stage-matched coverage seam to its
named alias goal. -/
theorem allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms_implies_allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hcov19 : AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate P hdata) :
    allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata :=
  allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms
    P essential solvability archimedean hdata hcov19

/-- Extra-short local sugar for the stage-matched coverage seam alias. -/
abbrev canonicalStageMatchedCoverageResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms_StageMatchedResidual
    P essential solvability archimedean hdata

/-- **Partial discharge of axiom 19 (global-gluing fragment).**

The chosen-`V` coordinate-image coverage residue family is the per-pivot
coverage residue of `hdata.V` quantified over all pivots.  Under a full
`GlobalGluingCertificate P hdata.V`, each per-pivot residue is discharged
without any standard-sequence / Archimedean content (choose `c := x j₀`, so
`Function.update x j₀ c = x`, and read both brackets off the global gluing
equivalence).  This is the coverage analogue of
`wakkerStep5StrictMonotonicityResidualAtPivot_of_globalGluingCertificate`,
applied at every pivot.

This is the first named partial discharge of axiom 19: it shows the axiom is
**not** strictly unprovable, but holds whenever the global additive sum already
tracks preference — exactly the situation produced once the M1 global-gluing
output is in hand.  The genuine residual content is therefore only in producing
`V` / global gluing from the raw axioms in the first place, not in the coverage
family itself. -/
theorem allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_of_globalGluingCertificate
    {X : ι → Type v} {P : ProductPref X}
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hglobal : GlobalGluingCertificate P hdata.V) :
    AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate
      P hdata := by
  intro j₀
  exact wakkerStep5CoordinateImageCoverageResidualAtPivot_of_globalGluingCertificate
    P hdata.V j₀ hglobal

/-- **Raw-axiom-form discharge of axiom 19 from a global-gluing certificate.**

Preserves the full raw-hypothesis list of axiom 19 but proves the target
without using any of those hypotheses when a `GlobalGluingCertificate P hdata.V`
is available, via
`allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_of_globalGluingCertificate`.
Audits at only the foundational axioms, with no `_from_raw_axioms` dependency. -/
theorem allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms_of_globalGluingCertificate
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hglobal : GlobalGluingCertificate P hdata.V) :
    AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate
      P hdata :=
  allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_of_globalGluingCertificate
    hdata hglobal

/-- **Strictly-weaker partial discharge of obligation 19 from the forward
gluing direction alone.**

The coverage residual `∃ c, x ≽ update x j₀ c ≽ y` is witnessed by `c := x j₀`
(so `update x j₀ c = x`): the **upper** bracket `x ≽ x` is reflexivity, and the
**lower** bracket `x ≽ y` follows from the *forward* gluing direction
`∑ V(y) ≤ ∑ V(x) → P.weakPref x y` — without needing the backward direction.

This is strictly weaker than
`..._of_globalGluingCertificate` (which uses the full biconditional gluing): only
the `→` half of each `(hglobal x y)` is consumed.  It pinpoints that the honest
residual content of obligation 19 is *only* the forward "additive sum tracks
preference" direction, not the coverage existential, which is trivial once that
forward direction is available. -/
theorem allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_of_forwardGluing
    {X : ι → Type v} {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hfwd : ∀ x y : Profile X,
      (∑ i, hdata.V i (y i)) ≤ (∑ i, hdata.V i (x i)) → P.weakPref x y) :
    AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate
      P hdata := by
  intro j₀ x y hle
  refine ⟨x j₀, ?_, ?_⟩
  · -- upper bracket: `update x j₀ (x j₀) = x`, then reflexivity.
    have hself : Function.update x j₀ (x j₀) = x := Function.update_eq_self j₀ x
    rw [hself]
    rcases ProductPref.IsWeakOrder.complete (P := P) x x with h | h <;> exact h
  · -- lower bracket: `update x j₀ (x j₀) = x`, then forward gluing gives `x ≽ y`.
    have hself : Function.update x j₀ (x j₀) = x := Function.update_eq_self j₀ x
    rw [hself]
    exact hfwd x y hle

/-- **Raw-axiom-form forward-gluing discharge of axiom 19.**

Preserves the full raw-hypothesis list but proves the target from only the
forward gluing direction (strictly weaker than the full global-gluing
discharge above). -/
theorem allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms_of_forwardGluing
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (_essential   : ∀ i, ProductPref.Essential P i)
    (_solvability : ProductPref.RestrictedSolvability P)
    (_archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hfwd : ∀ x y : Profile X,
      (∑ i, hdata.V i (y i)) ≤ (∑ i, hdata.V i (x i)) → P.weakPref x y) :
    AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate
      P hdata :=
  allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_of_forwardGluing
    hdata hfwd

-- [Option A excision] `pairwiseFiniteCutCoverageCertificate_from_raw_axioms_of_thinBaseTransportFrontier`
-- retired: rested on the deleted (unsound) base-transport reach axioms.

-- [Option A excision] obligation 2 helper
-- `sharedPivotAllPairsStep4MachineryCertificate_from_raw_axioms_of_thinMagnitudeFiniteCutTransportFrontier`
-- retired: it consumed the deleted transport family (which rested on the
-- unsound base-transport reach axioms).

/-- Obligation 3 recovered from the thinner pivot-hexagon transport frontier. -/
theorem nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) (V : (i : ι) → X i → ℝ)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀)
    (hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) :
    NonPivotPairAdditivityCertificate P V j₀ := by
  exact nonPivotPairAdditivityCertificate_of_pivotHexagonTransportCertificate
    P V j₀
    (pivotHexagonTransportCertificate_from_raw_axioms
      P essential solvability archimedean j₀ V hcov)
    hMatch

/-- **Compatibility seam alias for the IV.6→A1 bridge wrapper.**

Named shorthand for the bridge from the pivot-hexagon transport interface to
the non-pivot additivity frontier. -/
def nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport_CompatibilityResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) (V : (i : ι) → X i → ℝ)
    (hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) : Prop :=
  NonPivotPairAdditivityCertificate P V j₀

/-- Unwrap lemma for the IV.6→A1 bridge compatibility seam alias. -/
theorem nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport_CompatibilityResidual_iff
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) (V : (i : ι) → X i → ℝ)
    (hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) :
    nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport_CompatibilityResidual
      P essential solvability archimedean j₀ V hMatch ↔
    NonPivotPairAdditivityCertificate P V j₀ :=
  Iff.rfl

/-- Direct chaining helper from the IV.6→A1 bridge wrapper to its compatibility
alias goal. -/
theorem nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport_implies_nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport_CompatibilityResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) (V : (i : ι) → X i → ℝ)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀)
    (hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) :
    nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport_CompatibilityResidual
      P essential solvability archimedean j₀ V hMatch :=
  nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport
    P essential solvability archimedean j₀ V hcov hMatch

/-- Extra-short local sugar for the IV.6→A1 bridge compatibility seam alias. -/
abbrev canonicalNonPivotPairAdditivityBridgeCompatibilityResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) (V : (i : ι) → X i → ℝ)
    (hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) : Prop :=
  nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport_CompatibilityResidual
    P essential solvability archimedean j₀ V hMatch

/-- **Stage-matched A1 cross-pair wrapper.**

Once a chosen `Stage4MatchedAllPairsAdditivityData P` package is fixed,
the broad non-pivot additivity certificate is recovered directly from the
local IV.6 transport seam specialized to `hdata.V`, `hdata.j₀`, and
`hdata.hMatch`.  This is the consumer-facing form used by the Stage-4 →
Stage-5 assembly corridor. -/
theorem nonPivotPairAdditivityCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hcov : TwoPivotSliceTransportCoverageResidual P hdata.j₀) :
    NonPivotPairAdditivityCertificate P hdata.V hdata.j₀ := by
  exact
    nonPivotPairAdditivityCertificate_of_pivotHexagonTransportCertificate
      P hdata.V hdata.j₀
      (pivotHexagonTransportCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
        P essential solvability archimedean hdata hcov)
      hdata.hMatch

/-- The broad strict-monotonicity residue recovered from the thinner
all-pairs-driven Stage-5 strictness frontier on chosen A1 data. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_allPairsAdditivityDrivenFrontier
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    WakkerStep5StrictMonotonicityResidualAtPivot P hdata.V hdata.j₀ := by
  exact
    wakkerStep5StrictMonotonicityResidualAtPivot_of_allPairsAdditivityDrivenCertificate
      P hdata
      (allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
        P essential solvability archimedean hdata hesc)

/-- **Compatibility seam alias for the broad Step-5 strictness frontier wrapper.**

Named shorthand for the bridge from the all-pairs-driven strictness certificate
layer to the broad Step-5 strictness residual. -/
def wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  WakkerStep5StrictMonotonicityResidualAtPivot P hdata.V hdata.j₀

/-- Unwrap lemma for the broad Step-5 strictness frontier compatibility seam
alias. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual_iff
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) :
    wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual
      P essential solvability archimedean hdata ↔
    WakkerStep5StrictMonotonicityResidualAtPivot P hdata.V hdata.j₀ :=
  Iff.rfl

/-- Direct chaining helper from the broad Step-5 strictness frontier wrapper
to its compatibility alias goal. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_implies_wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual
      P essential solvability archimedean hdata :=
  wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_allPairsAdditivityDrivenFrontier
    P essential solvability archimedean hdata hesc

/-- Extra-short local sugar for the broad Step-5 strictness frontier
compatibility seam alias. -/
abbrev canonicalStep5StrictnessFrontierCompatibilityResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual
    P essential solvability archimedean hdata

/-- **Stage-matched A3 residual wrapper.**

Consumer-facing packaging of the thinner chosen-`V` strictness frontier: once
the Stage-4-matched all-pairs-additivity package `hdata` is fixed, the broad
Step-5 strictness residual is recovered directly from the named stage-matched
strictness seam. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    WakkerStep5StrictMonotonicityResidualAtPivot P hdata.V hdata.j₀ := by
  exact
    wakkerStep5StrictMonotonicityResidualAtPivot_of_allPairsAdditivityDrivenCertificate
      P hdata
      (allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
        P essential solvability archimedean hdata hesc)

/-- **Stage-matched Step-5 strictness residual seam alias.**

Named shorthand for the chosen-`V` Step-5 strictness residual interface on a
fixed `Stage4MatchedAllPairsAdditivityData P` package. -/
def wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  WakkerStep5StrictMonotonicityResidualAtPivot P hdata.V hdata.j₀

/-- Unwrap lemma for the stage-matched Step-5 strictness residual seam alias. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_StageMatchedResidual_iff
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) :
    wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata ↔
    WakkerStep5StrictMonotonicityResidualAtPivot P hdata.V hdata.j₀ :=
  Iff.rfl

/-- Direct chaining helper from the stage-matched Step-5 strictness residual
theorem to its named alias goal. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_implies_wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata :=
  wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    P essential solvability archimedean hdata hesc

/-- Extra-short local sugar for the stage-matched Step-5 strictness residual
seam alias. -/
abbrev canonicalStageMatchedStep5StrictnessResidual
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_StageMatchedResidual
    P essential solvability archimedean hdata

/-- In the `card ι ≥ 3` regime used by the end-to-end closure ladder, the
broad strict-monotonicity residue is already recovered from the smaller
one-step pivot-retargeting bracketing seam. -/
theorem wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_pivotCoordinateRetargetingBracketFrontier
    {X : ι → Type v} [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    WakkerStep5StrictMonotonicityResidualAtPivot P hdata.V hdata.j₀ := by
  exact
    wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
      P essential solvability archimedean hdata hesc

/-- The broad coordinate-image coverage residue recovered from the thinner
all-pairs-driven Stage-5 coverage frontier on chosen A1 data. -/
theorem wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_allPairsAdditivityDrivenFrontier
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hcov19 : AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate P hdata) :
    ∀ j₀ : ι, WakkerStep5CoordinateImageCoverageResidualAtPivot P hdata.V j₀ := by
  exact
    wakkerStep5CoordinateImageCoverageResidualFamily_of_allPairsAdditivityDrivenCertificate
      P hdata
      (allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms
        P essential solvability archimedean hdata hcov19)

/-- **Compatibility seam alias for the broad Step-5 coverage frontier wrapper.**

Named shorthand for the bridge from the all-pairs-driven coverage certificate
layer to the broad Step-5 coverage residual family. -/
def wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  ∀ j₀ : ι, WakkerStep5CoordinateImageCoverageResidualAtPivot P hdata.V j₀

/-- Unwrap lemma for the broad Step-5 coverage frontier compatibility seam
alias. -/
theorem wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual_iff
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) :
    wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual
      P essential solvability archimedean hdata ↔
    (∀ j₀ : ι, WakkerStep5CoordinateImageCoverageResidualAtPivot P hdata.V j₀) :=
  Iff.rfl

/-- Direct chaining helper from the broad Step-5 coverage frontier wrapper to
its compatibility alias goal. -/
theorem wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_implies_wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hcov19 : AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate P hdata) :
    wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual
      P essential solvability archimedean hdata :=
  wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_allPairsAdditivityDrivenFrontier
    P essential solvability archimedean hdata hcov19

/-- Extra-short local sugar for the broad Step-5 coverage frontier
compatibility seam alias. -/
abbrev canonicalStep5CoverageFrontierCompatibilityResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_allPairsAdditivityDrivenFrontier_CompatibilityResidual
    P essential solvability archimedean hdata

/-- **Stage-matched A2 residual-family wrapper.**

Intermediate consumer-facing packaging of the smaller chosen-`V` coverage
frontier: once the Stage-4-matched package `hdata` is fixed, recover the full
per-pivot residual family for `hdata.V` directly from the stage-matched
coverage seam. -/
theorem wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hcov19 : AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate P hdata) :
    ∀ j₀ : ι, WakkerStep5CoordinateImageCoverageResidualAtPivot P hdata.V j₀ := by
  exact
    wakkerStep5CoordinateImageCoverageResidualFamily_of_allPairsAdditivityDrivenCertificate
      P hdata
      (allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms
        P essential solvability archimedean hdata hcov19)

/-- **Stage-matched Step-5 coverage residual-family seam alias.**

Named shorthand for the chosen-`V` Step-5 coverage residual-family interface on
a fixed `Stage4MatchedAllPairsAdditivityData P` package. -/
def wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  ∀ j₀ : ι, WakkerStep5CoordinateImageCoverageResidualAtPivot P hdata.V j₀

/-- Unwrap lemma for the stage-matched Step-5 coverage residual-family seam
alias. -/
theorem wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_StageMatchedResidual_iff
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) :
    wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata ↔
    (∀ j₀ : ι, WakkerStep5CoordinateImageCoverageResidualAtPivot P hdata.V j₀) :=
  Iff.rfl

/-- Direct chaining helper from the stage-matched Step-5 coverage residual-
family theorem to its named alias goal. -/
theorem wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_implies_wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_StageMatchedResidual
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hcov19 : AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate P hdata) :
    wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_StageMatchedResidual
      P essential solvability archimedean hdata :=
  wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    P essential solvability archimedean hdata hcov19

/-- Extra-short local sugar for the stage-matched Step-5 coverage residual-
family seam alias. -/
abbrev canonicalStageMatchedStep5CoverageResidualFamily
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P) : Prop :=
  wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_StageMatchedResidual
    P essential solvability archimedean hdata

/-- **Stage-matched A3 certificate wrapper.**

Once the chosen Stage-4-matched all-pairs-additivity package `hdata` has been
fixed, the broad Step-5 strict-monotonicity certificate is theorem-backed from
the thinner chosen-`V` frontier.  This packages the consumer-facing form used
downstream, so later closures do not need to manually reassemble the residual
and certificate layers. -/
theorem wakkerStep5StrictMonotonicityCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hesc : PivotGridEscapesAtTarget P hdata.j₀) :
    WakkerStep5StrictMonotonicityCertificate P hdata.V hdata.hpair solvability :=
  wakkerStep5StrictMonotonicityCertificate_of_allPairsAdditivity
    hdata.j₀ hdata.V hdata.hpair solvability
    (wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
      P essential solvability archimedean hdata hesc)

/-- **Stage-matched A2 certificate wrapper.**

Consumer-facing packaging of the thinner chosen-`V` coordinate-image coverage
frontier: once the Stage-4-matched all-pairs-additivity package `hdata` is
fixed, the full Step-5 coverage certificate follows from the theorem-backed
assembly over the per-pivot residue family. -/
theorem wakkerStep5CoordinateImageCoverageCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
    {X : ι → Type v} [Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (hdata : Stage4MatchedAllPairsAdditivityData P)
    (hcov19 : AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate P hdata) :
    WakkerStep5CoordinateImageCoverageCertificate P hdata.V hdata.hpair solvability :=
  wakkerStep5CoordinateImageCoverageCertificate_of_residueAtPivot
    hdata.V hdata.hpair solvability
    (wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
      P essential solvability archimedean hdata hcov19)

-- [Option A excision] The end-to-end thin-frontier scaffold
-- `additiveRep_nonempty_from_thin_frontier` was retired: it rested on the
-- unsound base-transport reach axioms (machine-checked: deriving `False` at the
-- `additiveRealBool` model).  The canonical from-axioms route is now
-- `additiveRep_nonempty_from_structural_axioms_reachAxiomFree`.

/-! ## Frontier obligations (theorem-backed forms)

The five frontier obligations declared at the top of the file as anchor
docstrings are now discharged here as theorems, routed through the smaller
thin-frontier wrappers above.  Their `_from_raw_axioms` audits should
therefore depend only on the smaller axioms surfaced by the thinned
wrappers, not on themselves. -/

/- [Option A excision] obligation 1 `pairwiseFiniteCutCoverageCertificate_from_raw_axioms`
retired: it routed through the deleted thin base-transport frontier (unsound
reach axioms).  The surjective / escape-residual / cut-construction forms of
finite-cut coverage remain as the sound routes. -/

/- **Obligation 2 (theorem-backed under `[Nontrivial ι]` plus topology).**
Shared-pivot all-pairs Step-4 machinery for any chosen pivot `j₀`, from the
raw axioms.

Discharged via
`sharedPivotAllPairsStep4MachineryCertificate_from_raw_axioms_of_thinMagnitudeFiniteCutTransportFrontier`.
The remaining mathematical content lives in the smaller axioms
`sharedPivotPivotGridInjective...`,
`sharedPivotHexagonFamilyOnData...`, and
`sharedPivotFiniteCutInterpolationFamilyOnData...` (axiom 11 having been
retired by the topology architectural decision in
`RawAxiomDischargersTopology.lean`). -/
/- [Option A excision] obligation 2 `sharedPivotAllPairsStep4MachineryCertificate_from_raw_axioms`
retired: it routed through the deleted thin magnitude/finite-cut transport
frontier, which rested on the unsound base-transport reach axioms.  The Step-4
machinery from surjective/escape-residual routes remains available; the
canonical from-axioms construction is now
`additiveRep_nonempty_from_structural_axioms_reachAxiomFree`. -/
theorem nonPivotPairAdditivityCertificate_from_raw_axioms
    {X : ι → Type v} (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) (V : (i : ι) → X i → ℝ)
    (hcov : TwoPivotSliceTransportCoverageResidual P j₀)
    (hMatch : ∀ k : ι, k ≠ j₀ →
      PairwiseSliceRepresentationCertificate P j₀ k (V j₀) (V k)) :
    NonPivotPairAdditivityCertificate P V j₀ :=
  nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport
    P essential solvability archimedean j₀ V hcov hMatch

/-! ## End-to-end: raw axioms + structural inputs ⇒ `Nonempty (AdditiveRep P)`

The wrapper below uses all five named obligations above together with
the audit-clean Stage-3 C1 closer to produce `Nonempty (AdditiveRep P)`
directly from the raw axioms — modulo, of course, the five obligations
themselves.  This pin-points what the open Wakker frontier is: it is
not a sea of unspecified work but exactly the five named axioms above.

The pivot `j₀`, the non-pivot witness `k_witness`, and the pair of
`StandardSequence`s `(σⱼ, σₖ)` are passed as structural inputs (their
existence is itself part of the Wakker IV.2.7 frontier, but is *not*
on the list of five open obligations above — that list concerns the
*certificates*, not the underlying constructors).  Future work can
replace those structural inputs by a sixth, separately-named obligation
producing a `StandardSequence` for every coordinate from the raw axioms. -/

-- [Option A excision] `additiveRep_nonempty_from_raw_axioms` retired together
-- with `additiveRep_nonempty_from_thin_frontier`: both rested on the unsound
-- base-transport reach axioms.  The canonical from-axioms route is
-- `additiveRep_nonempty_from_structural_axioms_reachAxiomFree`.

/-- **C1 (common-scale compatibility) — the §IV.5 representation family from the
shared-pivot Step-4 tradeoff family + continuity + grid density (Phase 74).**

Realizes roadmap item **C1**'s genuinely-hard third subpart, the *common-scale
compatibility* (a single pivot utility `V₀` calibrating every slice).  The per-slice
grid-additive representations are mechanical from the Step-4 tradeoff family
(`pairwise_additivity_of_…pairwiseStep4TradeoffMachineryCertificate`), each producing
its own grid-normalized pivot utility `V₀^(k)` on the **shared** `hdata.σⱼ₀` grid.
The deep content — forcing all the `V₀^(k)` to coincide into one `V₀` — is closed by
the existing M5 density-extension closer
(`CertificateChecklist.sharedPivotGrid_global_agreement`): two pivot utilities that
agree on the dense `σⱼ₀`-grid and are continuous are equal everywhere
(`Continuous.ext_on`).

The honest inputs (matching Wakker §IV.5):
* `hStep4` — the shared-pivot Step-4 tradeoff family on the chosen data (engine-C
  characterized core: each slice possesses a grid-additive representation);
* `hcont` — continuity of each per-slice pivot utility produced by the Step-4
  chain (the M4 continuity-discharge content);
* `hdense` — density of the shared pivot grid `Set.range hdata.σⱼ₀.α` in `X j₀`
  (the M4 between-points / standard-sequence density content).

Crucially, continuity is demanded **only** for the finitely-relevant per-slice pivot
utilities (passed as a hypothesis on the specific utilities), not the over-strong
`∀ V, Continuous V`.  This is *not* a free reduction: the common-scale compatibility
genuinely needs continuity + density (the §IV.5 / topological non-degeneracy), exactly
as A1/B2 needed structural inputs.

Audit: `[propext, Classical.choice, Quot.sound]`. -/
theorem sharedPivotGridAdditiveRepresentationFamily_of_step4Family_continuous_dense
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (solvability : ProductPref.RestrictedSolvability P)
    (j₀ : ι) [T2Space (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hStep4 : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata)
    (hdense : Dense (Set.range hdata.σⱼ₀.α))
    (hcont : ∀ (k : ι) (hk : k ≠ j₀) (Vⱼ₀ : X j₀ → ℝ) (Vk : X k → ℝ),
      PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) Vⱼ₀ Vk →
      PairwiseSliceRepresentationCertificate P j₀ k Vⱼ₀ Vk →
      Continuous Vⱼ₀) :
    SharedPivotGridAdditiveRepresentationFamily P j₀ hdata := by
  classical
  -- Per-slice grid-normalized representations from the Step-4 tradeoff family.
  have hPer : ∀ (k : ι) (hk : k ≠ j₀),
      ∃ (Vⱼ₀ : X j₀ → ℝ) (Vk : X k → ℝ),
        PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) Vⱼ₀ Vk ∧
        PairwiseSliceRepresentationCertificate P j₀ k Vⱼ₀ Vk := by
    intro k hk
    exact
      pairwise_additivity_of_injectiveStandardSequences_restrictedSolvability_and_pairwiseStep4TradeoffMachineryCertificate
        P solvability (Ne.symm hk) hdata.σⱼ₀ (hdata.σk k hk)
        hdata.hinj_j₀ (hdata.hinj_k k hk) (hStep4 k hk)
  -- Choose a reference non-pivot coordinate (exists since card ι ≥ 3 ≥ 2).
  obtain ⟨k₀, hk₀⟩ := exists_ne j₀
  obtain ⟨V₀, Vk₀, hnorm₀, hslice₀⟩ := hPer k₀ hk₀
  -- The common pivot utility is the reference one.  Each slice's own pivot
  -- utility agrees with V₀ on the dense σⱼ₀-grid (both grid-normalized) and is
  -- continuous, hence equals V₀ everywhere (M5 density extension).
  refine ⟨V₀, ?_⟩
  intro k hk
  obtain ⟨Vⱼ₀_k, Vk, hnorm_k, hslice_k⟩ := hPer k hk
  have hshared : CertificateChecklist.SharedPivotGridCertificate hdata.σⱼ₀ V₀ Vⱼ₀_k :=
    ⟨hnorm₀.1, hnorm_k.1⟩
  have hcont₀ : Continuous V₀ := hcont k₀ hk₀ V₀ Vk₀ hnorm₀ hslice₀
  have hcont_k : Continuous Vⱼ₀_k := hcont k hk Vⱼ₀_k Vk hnorm_k hslice_k
  have heq : V₀ = Vⱼ₀_k :=
    CertificateChecklist.sharedPivotGrid_global_agreement
      hdata.σⱼ₀ V₀ Vⱼ₀_k hshared hcont₀ hcont_k hdense
  refine ⟨Vk, ?_, ?_⟩
  · -- Grid normalization for (V₀, Vk): V₀ = Vⱼ₀_k on the grid, and Vⱼ₀_k is normalized.
    rw [heq]; exact hnorm_k
  · rw [heq]; exact hslice_k

/-- **End-to-end additive representation from the single §IV.5 representation
residual (Phase 65 capstone).**

The structural endpoint of the consolidation arc: `Nonempty (AdditiveRep P)`
follows from the §IV.5 common-pivot grid-additive representation family
(`SharedPivotGridAdditiveRepresentationFamily` on chosen shared-pivot data) plus
the raw axioms, the topology bundle, and the standard Stage-5 closure inputs.

The representation family supplies the Stage-4 pivot-slice data directly
(`wakkerStage4PivotSliceRepresentationData_of_gridAdditiveRepresentationFamily`,
Phase 64); the cross-pair additivity, strictness, and coverage Stage-5 residuals
route through the existing `Stage4MatchedAllPairsAdditivityData`-specialized
seams; and the closure ladder assembles the global representation.

This exhibits the §IV.5 representation family as the **single pivot-side entry
point** to the end-to-end theorem: given it (the genuine deep §IV.5 content) on
the chosen data, the additive representation exists, with everything downstream
theorem-backed. -/
theorem additiveRep_nonempty_of_gridAdditiveRepresentationFamily
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hcov : ∀ j₀' : ι, TwoPivotSliceTransportCoverageResidual P j₀')
    (hesc : ∀ j₀' : ι, PivotGridEscapesAtTarget P j₀')
    (hcov19 : ∀ hdata' : Stage4MatchedAllPairsAdditivityData P,
      AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate P hdata')
    (hrep : SharedPivotGridAdditiveRepresentationFamily P j₀ hdata) :
    Nonempty (AdditiveRep P) := by
  -- Stage-4 pivot-slice data from the representation family (Phase 64).
  have hStage4 : WakkerStage4PivotSliceRepresentationData P :=
    wakkerStage4PivotSliceRepresentationData_of_gridAdditiveRepresentationFamily
      P j₀ hdata hrep
  -- Fix the A1 output package from Stage-4 data + the cross-pair residual.
  let hA1 : Stage4MatchedAllPairsAdditivityData P :=
    stage4MatchedAllPairsAdditivityData_of_stage4Data_and_cross
      P hStage4
      (fun j₀' V hMatch =>
        nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport
          P essential solvability archimedean j₀' V (hcov j₀') hMatch)
  -- Stage-5 coverage and strictness residuals on the chosen A1 package.
  have hcov : WakkerStep5CoordinateImageCoverageCertificate P hA1.V hA1.hpair solvability :=
    wakkerStep5CoordinateImageCoverageCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
      P essential solvability archimedean hA1 (hcov19 hA1)
  have hstrict : WakkerStep5StrictMonotonicityCertificate P hA1.V hA1.hpair solvability :=
    wakkerStep5StrictMonotonicityCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
      P essential solvability archimedean hA1 (hesc hA1.j₀)
  have hStep5 : WakkerStage5GlobalGluingData P solvability :=
    ⟨hA1.j₀, hA1.V,
      fun k hk => hA1.hMatch k hk,
      hA1.hpair, hcov, hstrict⟩
  simpa [WakkerStage5AdditiveAssemblyData] using
    wakkerStage5AdditiveAssemblyData_of_stage5GlobalGluingData
      (P := P) solvability hStep5

/-- **End-to-end additive representation from the §IV.5 Step-4 family + continuity
+ density (Phase 74 — C1 discharge).**

Composes the C1 common-scale closer
(`sharedPivotGridAdditiveRepresentationFamily_of_step4Family_continuous_dense`) with
the Phase-65 representation-family capstone
(`additiveRep_nonempty_of_gridAdditiveRepresentationFamily`): the additive
representation follows from the shared-pivot Step-4 tradeoff family on the data plus
the §IV.5 analytic inputs (continuity of per-slice pivot utilities + pivot-grid
density), with the common-scale compatibility mechanized by the M5 density
extension.

Audit note: the **C1 closer itself audits at `[propext, Classical.choice,
Quot.sound]`** — it is the clean deliverable.  This end-to-end composition routes
through the Phase-65 capstone, which (since the C1-constructed `V₀` is not asserted
surjective) uses the documented Stage-5 cross-pair/coverage/strictness
`_from_raw_axioms` seams; it therefore inherits exactly those seams (the same ones
`additiveRep_nonempty_of_gridAdditiveRepresentationFamily` exposes), not a clean
foundational-only audit.  For a fully seam-free end-to-end route use the
named-residuals/surjective-pivot capstones (Phases 66/68), which additionally take
the surjective-`V₀` non-degeneracy condition (C2). -/
theorem additiveRep_nonempty_of_step4Family_continuous_dense
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) [T2Space (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hcov : ∀ j₀' : ι, TwoPivotSliceTransportCoverageResidual P j₀')
    (hesc : ∀ j₀' : ι, PivotGridEscapesAtTarget P j₀')
    (hcov19 : ∀ hdata' : Stage4MatchedAllPairsAdditivityData P,
      AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate P hdata')
    (hStep4 : SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata)
    (hdense : Dense (Set.range hdata.σⱼ₀.α))
    (hcont : ∀ (k : ι) (hk : k ≠ j₀) (Vⱼ₀ : X j₀ → ℝ) (Vk : X k → ℝ),
      PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) Vⱼ₀ Vk →
      PairwiseSliceRepresentationCertificate P j₀ k Vⱼ₀ Vk →
      Continuous Vⱼ₀) :
    Nonempty (AdditiveRep P) :=
  additiveRep_nonempty_of_gridAdditiveRepresentationFamily
    P essential solvability archimedean htop j₀ hdata hcov hesc hcov19
    (sharedPivotGridAdditiveRepresentationFamily_of_step4Family_continuous_dense
      P solvability j₀ hdata hStep4 hdense hcont)

/-- **End-to-end additive representation from a surjective-pivot representation
family (Phase 66 — axiom-16-free pivot side).**

Sharper than `additiveRep_nonempty_of_gridAdditiveRepresentationFamily`: when the
common pivot utility `V₀` is **surjective**, obligation 3 (the cross-pair
additivity) is discharged from the representation family itself (Phase 63), so the
A1 all-pairs additivity certificate is built **without** the axiom-16 two-pivot
transport seam.  The resulting `Stage4MatchedAllPairsAdditivityData` is assembled
from the explicit representation `V`, and the Stage-5 coverage/strictness
residuals route through the existing matched-package discharges.

This shows the pivot-side construction, under a surjective common pivot (the
natural topology-bundle condition, Phase 41), needs neither axiom 6, 12, 14, nor
**16** — only the Stage-5 coverage/strictness seams remain. -/
theorem additiveRep_nonempty_of_surjectivePivotRepresentationFamily
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hesc : ∀ j₀' : ι, PivotGridEscapesAtTarget P j₀')
    (hcov19 : ∀ hdata' : Stage4MatchedAllPairsAdditivityData P,
      AllPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate P hdata')
    (V₀ : X j₀ → ℝ) (hsurj : Function.Surjective V₀)
    (hslices : ∀ (k : ι) (hk : k ≠ j₀),
      ∃ Vk : X k → ℝ,
        PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) V₀ Vk ∧
        PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk) :
    Nonempty (AdditiveRep P) := by
  classical
  -- Obligation 3 + pivot-slice matches from the surjective-pivot family (Phase 63).
  obtain ⟨V, hMatch, hCross⟩ :=
    nonPivotPairAdditivityCertificate_of_gridAdditiveRepresentationFamily_surjectivePivot
      P j₀ hdata V₀ hsurj hslices
  -- A1 all-pairs additivity from the explicit representation `V` — NO axiom 16.
  have hpair : AllPairsAdditivityCertificate P V :=
    allPairsAdditivityCertificate_of_pairwiseSliceRepresentationsAtPivot
      j₀ V hMatch hCross
  -- Package as the chosen Stage-4-matched A1 data on the explicit `V`.
  let hA1 : Stage4MatchedAllPairsAdditivityData P :=
    { j₀ := j₀, V := V, hMatch := hMatch, hpair := hpair }
  -- Stage-5 coverage and strictness residuals on the chosen A1 package.
  have hcov : WakkerStep5CoordinateImageCoverageCertificate P hA1.V hA1.hpair solvability :=
    wakkerStep5CoordinateImageCoverageCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
      P essential solvability archimedean hA1 (hcov19 hA1)
  have hstrict : WakkerStep5StrictMonotonicityCertificate P hA1.V hA1.hpair solvability :=
    wakkerStep5StrictMonotonicityCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
      P essential solvability archimedean hA1 (hesc hA1.j₀)
  have hStep5 : WakkerStage5GlobalGluingData P solvability :=
    ⟨hA1.j₀, hA1.V, fun k hk => hA1.hMatch k hk, hA1.hpair, hcov, hstrict⟩
  simpa [WakkerStage5AdditiveAssemblyData] using
    wakkerStage5AdditiveAssemblyData_of_stage5GlobalGluingData
      (P := P) solvability hStep5

/-- **End-to-end additive representation from the named structural residuals only
(Phase 68 — axiom 6/12/14/16/17-free).**

The tightest end-to-end statement: `Nonempty (AdditiveRep P)` from
* the §IV.5 surjective-pivot grid-additive representation family (no axiom 6/12/14;
  surjective pivot ⟹ no axiom 16, Phase 66),
* the descending-seeded escape residual for the strictness corridor (no axiom 17,
  Phase 67), and
* the Stage-5 coordinate-image coverage residual family (obl. 5 — engine-A IVT
  dischargeable, Phase 41).

No axiom 6, 12, 14, 16, or 17 appears; the representation family supplies Stage-4
data + A1 matches + obligation 3, the escape residual supplies strictness, and the
coverage residual supplies the image-coverage certificate.  This exhibits the
additive representation as following from exactly the named structural residuals
plus the §III.4 separability axiom (in the topology bundle underlying the
representation construction). -/
theorem additiveRep_nonempty_of_namedResiduals
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (V₀ : X j₀ → ℝ) (hsurj : Function.Surjective V₀)
    (hslices : ∀ (k : ι) (hk : k ≠ j₀),
      ∃ Vk : X k → ℝ,
        PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) V₀ Vk ∧
        PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk)
    (hescape : PivotGridDescendingSeededAboveAtTarget P j₀)
    (hcoverage : ∀ (V : (i : ι) → X i → ℝ) (j₀' : ι),
      WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀') :
    Nonempty (AdditiveRep P) := by
  classical
  -- Obligation 3 + pivot-slice matches from the surjective-pivot family (Phase 63).
  obtain ⟨V, hMatch, hCross⟩ :=
    nonPivotPairAdditivityCertificate_of_gridAdditiveRepresentationFamily_surjectivePivot
      P j₀ hdata V₀ hsurj hslices
  -- A1 all-pairs additivity from the explicit representation `V` — NO axiom 16.
  have hpair : AllPairsAdditivityCertificate P V :=
    allPairsAdditivityCertificate_of_pairwiseSliceRepresentationsAtPivot
      j₀ V hMatch hCross
  let hA1 : Stage4MatchedAllPairsAdditivityData P :=
    { j₀ := j₀, V := V, hMatch := hMatch, hpair := hpair }
  -- Strictness from the escape residual — NO axiom 17.
  have hstrictResidue : WakkerStep5StrictMonotonicityResidualAtPivot P hA1.V hA1.j₀ :=
    allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_of_descendingSeededEscape
      archimedean solvability hA1 hescape
  have hstrict : WakkerStep5StrictMonotonicityCertificate P hA1.V hA1.hpair solvability :=
    wakkerStep5StrictMonotonicityCertificate_of_allPairsAdditivity
      hA1.j₀ hA1.V hA1.hpair solvability hstrictResidue
  -- Coverage from the coverage residual family — obl. 5 (engine-A dischargeable).
  have hcov : WakkerStep5CoordinateImageCoverageCertificate P hA1.V hA1.hpair solvability :=
    wakkerStep5CoordinateImageCoverageCertificate_of_residueAtPivot
      hA1.V hA1.hpair solvability (fun j₀' => hcoverage hA1.V j₀')
  have hStep5 : WakkerStage5GlobalGluingData P solvability :=
    ⟨hA1.j₀, hA1.V, fun k hk => hA1.hMatch k hk, hA1.hpair, hcov, hstrict⟩
  simpa [WakkerStage5AdditiveAssemblyData] using
    wakkerStage5AdditiveAssemblyData_of_stage5GlobalGluingData
      (P := P) solvability hStep5

/-- **Bundled named residuals for the Wakker additive representation (Phase 69).**

Packages the genuine deep §IV.5/§IV.6/Step-5 content the additive representation
rests on, at a chosen pivot `j₀` and shared-pivot data `hdata`, as a single
structure:

* `V₀` + `hsurj` — a **surjective** common pivot utility (the §IV.5
  common-pivot scale; surjectivity is the natural connected-Archimedean
  non-degeneracy condition, Phase 41/66);
* `hslices` — the §IV.5 grid-additive slice representations on each non-pivot
  slice sharing `V₀`;
* `hescape` — the §IV.2/§IV.5 reach content (a monotone Archimedean pivot grid
  seeded above the target);
* `hcoverage` — the §IV.2.7/Step-5 coordinate-image coverage.

These are exactly the residuals the zero-raw-axiom capstone consumes; bundling
them gives a single-hypothesis statement of the representation theorem. -/
structure WakkerAdditiveRepNamedResiduals
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) where
  V₀ : X j₀ → ℝ
  hsurj : Function.Surjective V₀
  hslices : ∀ (k : ι) (hk : k ≠ j₀),
    ∃ Vk : X k → ℝ,
      PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) V₀ Vk ∧
      PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk
  hescape : PivotGridDescendingSeededAboveAtTarget P j₀
  hcoverage : ∀ (V : (i : ι) → X i → ℝ) (j₀' : ι),
    WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀'

/-- **Wakker additive representation from the single bundled residual structure
(Phase 69 capstone).**

`Nonempty (AdditiveRep P)` from the raw order axioms plus the **single** bundled
`WakkerAdditiveRepNamedResiduals` structure — the one-hypothesis form of the
zero-raw-axiom-seam end-to-end theorem.  Audit: `[propext, Classical.choice,
Quot.sound]`, no `_from_raw_axioms`. -/
theorem additiveRep_nonempty_of_bundledResiduals
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι)
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (hres : WakkerAdditiveRepNamedResiduals P j₀ hdata) :
    Nonempty (AdditiveRep P) :=
  additiveRep_nonempty_of_namedResiduals
    P essential solvability archimedean j₀ hdata
    hres.V₀ hres.hsurj hres.hslices hres.hescape hres.hcoverage

/-! ### C2 — surjectivity of the common pivot utility from the analytic inputs
(Phase 73)

The bundle field `hsurj : Function.Surjective V₀` is the §IV.2.7/§IV.5
non-degeneracy condition.  Roadmap item **C2** reduces it to the genuine
analytic inputs: a *connected* pivot coordinate, a *continuous* pivot utility,
and an *Archimedean two-sided unbounded* pivot grid.  This is the engine-A IVT
discharge of surjectivity (`RawAxiomDischargersHexagon.surjective_of_continuous_unbounded`,
Phase 41): a continuous real function on a connected space whose image is
unbounded above and below is surjective.  No overclaim — surjectivity is *not*
free, it is exactly the content of connectedness + continuity + unboundedness. -/

/-- **C2 — the common pivot utility is surjective from connectedness + continuity
+ two-sided unboundedness.**

Reduces the bundle field `hsurj` to the genuine §IV.2/§IV.5 analytic inputs.
Pure restatement of `RawAxiomDischargersHexagon.surjective_of_continuous_unbounded`
specialized to the pivot coordinate; audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem pivotUtilitySurjective_of_continuous_unbounded
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {j₀ : ι} [PreconnectedSpace (X j₀)]
    (V₀ : X j₀ → ℝ) (hcont : Continuous V₀)
    (habove : ∀ t : ℝ, ∃ a, t ≤ V₀ a)
    (hbelow : ∀ t : ℝ, ∃ b, V₀ b ≤ t) :
    Function.Surjective V₀ :=
  RawAxiomDischargersHexagon.surjective_of_continuous_unbounded V₀ hcont habove hbelow

/-- **End-to-end additive representation with the pivot surjectivity reduced to
the analytic inputs (Phase 73 — C2 discharge).**

Identical to `additiveRep_nonempty_of_namedResiduals` except the `hsurj` field is
replaced by the genuine §IV.2/§IV.5 analytic inputs (connectedness of the pivot
coordinate, continuity of `V₀`, two-sided Archimedean unboundedness of its grid),
from which surjectivity is derived by the engine-A IVT discharge (C2).  This
exhibits the surjective-pivot non-degeneracy as following from the standard
topological/Archimedean data rather than being assumed. -/
theorem additiveRep_nonempty_of_namedResiduals_continuousPivot
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (j₀ : ι) [PreconnectedSpace (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (V₀ : X j₀ → ℝ)
    (hcont : Continuous V₀)
    (habove : ∀ t : ℝ, ∃ a, t ≤ V₀ a)
    (hbelow : ∀ t : ℝ, ∃ b, V₀ b ≤ t)
    (hslices : ∀ (k : ι) (hk : k ≠ j₀),
      ∃ Vk : X k → ℝ,
        PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) V₀ Vk ∧
        PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk)
    (hescape : PivotGridDescendingSeededAboveAtTarget P j₀)
    (hcoverage : ∀ (V : (i : ι) → X i → ℝ) (j₀' : ι),
      WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀') :
    Nonempty (AdditiveRep P) :=
  additiveRep_nonempty_of_namedResiduals
    P essential solvability archimedean j₀ hdata V₀
    (pivotUtilitySurjective_of_continuous_unbounded V₀ hcont habove hbelow)
    hslices hescape hcoverage

/-! ### B2 — Step-5 coordinate-image coverage from surjective pivot + equal-score
faithfulness (Phase 73)

Roadmap item **B2** asks to reduce the Step-5 coverage residual
`WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀` via the engine-A IVT
route.  A rigorous analysis (A1 discipline) shows what the genuine content is:

* the coverage residual demands, for `∑V(y) ≤ ∑V(x)`, a pivot value `c` with the
  bracket `x ≽ update x j₀ c ≽ y`;
* the **first** leg `x ≽ update x j₀ c` is a single-coordinate comparison and is
  **theorem-backed** from all-pairs additivity (`globalGluing_update_step…`);
* the **second** leg `update x j₀ c ≽ y` compares two profiles of *equal*
  additive score across many coordinates — this genuinely needs `V` to be a
  **faithful** representation of `≽`, and is *not* derivable from the raw axioms
  for an arbitrary `V` (the same lesson as A1: faithfulness is structural, not
  free).

So the honest reduction is: with a **surjective** pivot utility (C2 — reducible
to connectedness + continuity + unboundedness) the pivot can be tuned to
*equalize* the additive scores, and then the only remaining content is the clean
"equal additive score implies weak preference" faithfulness residual.  This is
strictly leaner than the coverage residual (no existential, no bracket, a single
implication) and isolates exactly the faithfulness content. -/

/-- **Equal-additive-score weak preference (the B2 faithfulness residual).**

`∀ x y, ∑V(x) = ∑V(y) → x ≽ y`.  Symmetric in `x, y`, so it equally gives
`y ≽ x` and hence indifference whenever the additive scores agree.  This is the
genuine representation-faithfulness content of the §IV.2.7/Step-5 coverage
residual — not derivable from the raw axioms for an arbitrary `V`, but strictly
leaner than the coverage residual itself (no bracketing existential). -/
def EqualAdditiveScoreWeakPreference
    {X : ι → Type v} (P : ProductPref X) (V : (i : ι) → X i → ℝ) : Prop :=
  ∀ x y : Profile X,
    (∑ i, V i (x i)) = (∑ i, V i (y i)) → P.weakPref x y

/-- **B2 discharge — the coverage residual from a surjective pivot + equal-score
faithfulness (Phase 73).**

Given all-pairs additivity, a **surjective** pivot utility `V j₀`, and the
equal-additive-score faithfulness residual, the Step-5 coordinate-image coverage
residual `WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀` is
theorem-backed:

* surjectivity supplies a pivot value `c` making `∑V(update x j₀ c) = ∑V(y)`
  (equalizing the additive scores);
* the first bracket leg `x ≽ update x j₀ c` is then the single-coordinate
  additivity comparison `globalGluing_update_step_of_allPairsAdditivity`
  (`∑V(update x j₀ c) = ∑V(y) ≤ ∑V(x)`);
* the second bracket leg `update x j₀ c ≽ y` is exactly the equal-score
  faithfulness residual at the equalized scores.

Audit: `[propext, Classical.choice, Quot.sound]` — no `_from_raw_axioms`.  This
realizes roadmap item **B2**: the coverage residual reduces to surjectivity (C2,
engine-A IVT) plus the leaner equal-score faithfulness residual. -/
theorem wakkerStep5CoordinateImageCoverageResidualAtPivot_of_surjectivePivot_and_equalScore
    {X : ι → Type v} [Nontrivial ι]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (V : (i : ι) → X i → ℝ) (j₀ : ι)
    (hpair : AllPairsAdditivityCertificate P V)
    (hsurj : Function.Surjective (V j₀))
    (hequal : EqualAdditiveScoreWeakPreference P V) :
    WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀ := by
  intro x y hle
  obtain ⟨i, hi⟩ := exists_ne j₀
  -- A pivot value equalizing the additive score of `update x j₀ c` to ∑V(y).
  obtain ⟨c, hc⟩ := hsurj (V j₀ (x j₀) + ((∑ a, V a (y a)) - (∑ a, V a (x a))))
  -- Off the pivot the updated profile is unchanged; at the pivot its value is `c`.
  have hpivot : V j₀ (Function.update x j₀ c j₀) = V j₀ c := by
    rw [Function.update_self]
  -- The additive score after the pivot update.
  have hgsum : (∑ a, V a (Function.update x j₀ c a))
      = (∑ a, V a (x a)) - V j₀ (x j₀) + V j₀ c := by
    have e1 := Finset.sum_erase_add Finset.univ
      (fun a => V a (Function.update x j₀ c a)) (Finset.mem_univ j₀)
    have e2 := Finset.sum_erase_add Finset.univ
      (fun a => V a (x a)) (Finset.mem_univ j₀)
    have erest : (∑ a ∈ Finset.univ.erase j₀, V a (Function.update x j₀ c a))
        = (∑ a ∈ Finset.univ.erase j₀, V a (x a)) :=
      Finset.sum_congr rfl (fun a ha => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)])
    simp only [Function.update_self] at e1 e2
    rw [erest] at e1
    linarith [e1, e2]
  have hcsum : (∑ a, V a (Function.update x j₀ c a)) = (∑ a, V a (y a)) := by
    rw [hgsum, hc]; ring
  refine ⟨c, ?_, ?_⟩
  · -- Leg 1: x ≽ update x j₀ c — single-coordinate additivity.
    rw [globalGluing_update_step_of_allPairsAdditivity P V hpair hi x c, hcsum]
    exact hle
  · -- Leg 2: update x j₀ c ≽ y — equal-score faithfulness.
    exact hequal _ y hcsum

/-- **WP-B2 — equal-score faithfulness is immediate from a representation.**

Given any additive representation `R` of `P`, the equal-additive-score
faithfulness residual `EqualAdditiveScoreWeakPreference P R.V` holds: if
`∑R.V(x) = ∑R.V(y)` then in particular `∑R.V(y) ≤ ∑R.V(x)`, which by
`R.represents` is exactly `x ≽ y`.

This discharges roadmap item **WP-B2**: the equal-score residual (the leaner
content of the Step-5 coverage residual) hides nothing false — it is a one-line
consequence of having a faithful representation, so the coverage residual is
sound once C1 produces the representation.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem equalAdditiveScoreWeakPreference_of_additiveRep
    {X : ι → Type v} {P : ProductPref X} (R : AdditiveRep P) :
    EqualAdditiveScoreWeakPreference P R.V := by
  intro x y hxy
  exact (R.represents x y).mpr (le_of_eq hxy.symm)

/-- **End-to-end additive representation from the deepest reduced residuals
(Phase 76 — B1 seed germ + C2 analytic surjectivity).**

The maximally-reduced end-to-end statement assembled from the Phase 71–75
reductions: `Nonempty (AdditiveRep P)` with the named-residual bundle's two
*derivable* fields replaced by their genuine germs —

* **B1 (`hescape`)** is replaced by the per-target standard-sequence **seed germ**
  `PivotStrictSeededAboveSeedDataFamily P j₀` plus §III.4 separability `hsep`; the
  descending-seeded escape residual is constructed from them via
  `pivotGridDescendingSeededAboveAtTarget_of_seedDataFamily` (Phases 72 + 75);
* **C2 (`hsurj`)** is replaced by the analytic inputs (connectedness
  `[PreconnectedSpace (X j₀)]`, continuity `hcont`, two-sided unboundedness
  `habove`/`hbelow`); surjectivity of the common pivot utility is derived via
  `pivotUtilitySurjective_of_continuous_unbounded` (Phase 73, engine-A IVT).

The two genuinely-irreducible residuals remain explicit:
* **C1 (`hslices`)** — the §IV.5 common-pivot grid-additive slice representations;
* **B2 (`hcoverage`)** — the Step-5 coordinate-image coverage.

This exhibits the additive representation as resting on exactly: the raw order
axioms, the topology bundle (carrying §III.4 separability and the §III.4.2 IVT
seam), the §IV.2.7 seed germ, the §IV.5 slice representations, and the Step-5
coverage — with every other piece (the infinite standard-sequence construction,
the descending family, the pivot surjectivity, obligations 3/14/16, the Stage-4/5
closure ladder) theorem-backed. -/
theorem additiveRep_nonempty_of_seedGerm_and_analyticPivot
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (hsep : ∀ i, RawAxiomDischargersIVT.CoordinateWeakSeparable P i)
    (j₀ : ι) [PreconnectedSpace (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (V₀ : X j₀ → ℝ)
    (hcont : Continuous V₀)
    (habove : ∀ t : ℝ, ∃ a, t ≤ V₀ a)
    (hbelow : ∀ t : ℝ, ∃ b, V₀ b ≤ t)
    (hslices : ∀ (k : ι) (hk : k ≠ j₀),
      ∃ Vk : X k → ℝ,
        PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) V₀ Vk ∧
        PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk)
    (hseed : PivotStrictSeededAboveSeedDataFamily P j₀)
    (hcoverage : ∀ (V : (i : ι) → X i → ℝ) (j₀' : ι),
      WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀') :
    Nonempty (AdditiveRep P) :=
  additiveRep_nonempty_of_namedResiduals
    P essential solvability archimedean j₀ hdata
    V₀
    (pivotUtilitySurjective_of_continuous_unbounded V₀ hcont habove hbelow)
    hslices
    (pivotGridDescendingSeededAboveAtTarget_of_seedDataFamily
      P solvability htop hsep j₀ hseed)
    hcoverage

/-! ### WP0 — the unified canonical target (Option B)

`OptionB_UnconditionalConstructionRoadmap.md` WP0 fixes a **single** canonical
construction theorem with the coordinate-independence hypothesis made explicit,
so that "Option B is done" has a precise meaning: discharge the residual frontier
`OptionBResidualFrontier` and the public `wakker_IV_2_7` becomes unconditional.

Coordinate independence is **not** a separate hypothesis here: it is the
`separable` field already carried by `RawAxiomDischargersTopology.WakkerCoordinateTopology`
(Phase 71), projected by `coordinateWeakSeparable_of_wakkerCoordinateTopology`.
So the structural-axiom surface of the canonical target is exactly Wakker/KLST's
hypothesis set: weak order, tradeoff consistency, essentiality, restricted
solvability, Archimedean, and the topology bundle (connectedness + preference
continuity + coordinate independence). -/

/-- **Option B residual frontier (the four remaining open residuals).**

Bundles exactly the residuals that WP-C1.a, WP-C1.b, WP-density, WP-B1, and WP-B2
of the Option B roadmap must discharge, at a chosen pivot `j₀` with shared-pivot
data `hdata`:

* `V₀` + analytic non-degeneracy (`hcont`/`habove`/`hbelow`) — the §IV.2/§IV.5
  pivot utility with continuity + two-sided unboundedness (C2 is *derived* from
  these, Phase 73; the residual is exhibiting such a `V₀`, i.e. WP-density +
  the calibrated pivot utility);
* `hslices` — the §IV.5 common-pivot grid-additive slice representations (C1);
* `hseed` — the §IV.2.7 standard-sequence seed germ (B1);
* `hcoverage` — the Step-5 coordinate-image coverage (B2).

When every field is theorem-backed from the structural axioms + topology bundle,
`additiveRep_nonempty_from_structural_axioms_and_coordinateIndependence` becomes
an unconditional construction. -/
structure OptionBResidualFrontier
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) (j₀ : ι) [PreconnectedSpace (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) where
  V₀ : X j₀ → ℝ
  hcont : Continuous V₀
  habove : ∀ t : ℝ, ∃ a, t ≤ V₀ a
  hbelow : ∀ t : ℝ, ∃ b, V₀ b ≤ t
  hslices : ∀ (k : ι) (hk : k ≠ j₀),
    ∃ Vk : X k → ℝ,
      PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) V₀ Vk ∧
      PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk
  hseed : PivotStrictSeededAboveSeedDataFamily P j₀
  hcoverage : ∀ (V : (i : ι) → X i → ℝ) (j₀' : ι),
    WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀'

/-- **WP0 canonical target — `Nonempty (AdditiveRep P)` from the structural
axioms + topology bundle (coordinate independence explicit) + the residual
frontier.**

This is the single theorem Option B drives to be unconditional.  Coordinate
independence enters only through `htop.separable` (projected by
`coordinateWeakSeparable_of_wakkerCoordinateTopology`), so the structural surface
is exactly Wakker/KLST's hypothesis set.  The body delegates to the Phase-76
maximally-reduced capstone.

Audit: `[propext, Classical.choice, Quot.sound]` + the §III.4.2 topology IVT
seams (inherited from the topology bundle); **no** `_from_raw_axioms` seam. -/
theorem additiveRep_nonempty_from_structural_axioms_and_coordinateIndependence
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) [PreconnectedSpace (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (frontier : OptionBResidualFrontier P j₀ hdata) :
    Nonempty (AdditiveRep P) :=
  additiveRep_nonempty_of_seedGerm_and_analyticPivot
    P essential solvability archimedean htop
    (fun i => RawAxiomDischargersTopology.coordinateWeakSeparable_of_wakkerCoordinateTopology htop i)
    j₀ hdata
    frontier.V₀ frontier.hcont frontier.habove frontier.hbelow
    frontier.hslices frontier.hseed frontier.hcoverage

/-- **WP0 bridge to the public Wakker IV.2.7 wrapper.**

Feeds the canonical target's `Nonempty (AdditiveRep P)` into the construction
certificate consumed by `WakkerDebreuKoopmans.wakker_IV_2_7`.  Once
`OptionBResidualFrontier` is theorem-backed, this makes the **public**
`wakker_IV_2_7` hold without its `hConstruct` hypothesis being externally
supplied — i.e. the wrapper's gap is closed through the canonical target.

The construction certificate `∃ V, ∀ x y, weakPref x y ↔ ∑V(y) ≤ ∑V(x)` is read
directly off the constructed `AdditiveRep`. -/
theorem wakkerConstruction_of_structural_axioms_and_coordinateIndependence
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) [PreconnectedSpace (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (frontier : OptionBResidualFrontier P j₀ hdata) :
    ∃ V : (i : ι) → X i → ℝ,
      ∀ x y : Profile X,
        P.weakPref x y ↔ (∑ i, V i (y i)) ≤ (∑ i, V i (x i)) := by
  obtain ⟨R⟩ :=
    additiveRep_nonempty_from_structural_axioms_and_coordinateIndependence
      P essential solvability archimedean htop j₀ hdata frontier
  exact ⟨R.V, R.represents⟩

/-! ### WP-T — reach-axiom-free canonical target (Option B)

The WP-T variants below route the standard-sequence construction through the
engine-A∘B Archimedean escape (`pivotGridDescendingSeededAboveAtTarget_of_seedDataWithEscapeFamily`)
instead of the bracket reach **axioms**.  The §III.4.2
`coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology` axioms
are therefore **eliminated** from the canonical target's dependency set; the B1
residual now carries the honest §IV.2.6 escape grid in the enriched seed germ
`PivotStrictSeededAboveSeedDataWithEscapeFamily`. -/

/-- **WP-T reach-axiom-free capstone** (escape-seed variant of
`additiveRep_nonempty_of_seedGerm_and_analyticPivot`). -/
theorem additiveRep_nonempty_of_seedGermEscape_and_analyticPivot
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) [PreconnectedSpace (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (V₀ : X j₀ → ℝ)
    (hcont : Continuous V₀)
    (habove : ∀ t : ℝ, ∃ a, t ≤ V₀ a)
    (hbelow : ∀ t : ℝ, ∃ b, V₀ b ≤ t)
    (hslices : ∀ (k : ι) (hk : k ≠ j₀),
      ∃ Vk : X k → ℝ,
        PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) V₀ Vk ∧
        PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk)
    (hseed : PivotStrictSeededAboveSeedDataWithEscapeFamily P j₀)
    (hcoverage : ∀ (V : (i : ι) → X i → ℝ) (j₀' : ι),
      WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀') :
    Nonempty (AdditiveRep P) :=
  additiveRep_nonempty_of_namedResiduals
    P essential solvability archimedean j₀ hdata
    V₀
    (pivotUtilitySurjective_of_continuous_unbounded V₀ hcont habove hbelow)
    hslices
    (pivotGridDescendingSeededAboveAtTarget_of_seedDataWithEscapeFamily
      P solvability htop archimedean
      (fun i => RawAxiomDischargersTopology.coordinateWeakSeparable_of_wakkerCoordinateTopology htop i)
      j₀ hseed)
    hcoverage

/-- **WP-T reach-axiom-free residual frontier.**

Identical to `OptionBResidualFrontier` but the B1 field is the *enriched* seed
germ `PivotStrictSeededAboveSeedDataWithEscapeFamily` carrying the §IV.2.6
Archimedean escape grid.  Using it eliminates the two §III.4.2 bracket reach
axioms from the canonical target. -/
structure OptionBResidualFrontierEscape
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) (j₀ : ι) [PreconnectedSpace (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀) where
  V₀ : X j₀ → ℝ
  hcont : Continuous V₀
  habove : ∀ t : ℝ, ∃ a, t ≤ V₀ a
  hbelow : ∀ t : ℝ, ∃ b, V₀ b ≤ t
  hslices : ∀ (k : ι) (hk : k ≠ j₀),
    ∃ Vk : X k → ℝ,
      PairwiseGridNormalizationWitness hdata.σⱼ₀ (hdata.σk k hk) V₀ Vk ∧
      PairwiseSliceRepresentationCertificate P j₀ k V₀ Vk
  hseed : PivotStrictSeededAboveSeedDataWithEscapeFamily P j₀
  hcoverage : ∀ (V : (i : ι) → X i → ℝ) (j₀' : ι),
    WakkerStep5CoordinateImageCoverageResidualAtPivot P V j₀'

/-- **WP-T reach-axiom-free canonical target.**

Like `additiveRep_nonempty_from_structural_axioms_and_coordinateIndependence`,
but consuming the escape frontier so the §III.4.2 bracket reach axioms are
**eliminated**.  Audit (verified below): `[propext, Classical.choice,
Quot.sound]` — **no** `coordinateOneStepBracket*` axiom, **no** `_from_raw_axioms`
seam.  This is the WP-T endpoint: the canonical Option-B target now depends only
on foundational axioms plus the explicit residual frontier (C1 slices, B1 escape
seed germ, B2 coverage). -/
theorem additiveRep_nonempty_from_structural_axioms_reachAxiomFree
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)] [Nontrivial ι]
    [_hcard : Fact (3 ≤ Fintype.card ι)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (essential   : ∀ i, ProductPref.Essential P i)
    (solvability : ProductPref.RestrictedSolvability P)
    (archimedean : ∀ i, ProductPref.Archimedean P i)
    (htop : RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (j₀ : ι) [PreconnectedSpace (X j₀)]
    (hdata : SharedPivotStandardSequenceFamilyData P j₀)
    (frontier : OptionBResidualFrontierEscape P j₀ hdata) :
    Nonempty (AdditiveRep P) :=
  additiveRep_nonempty_of_seedGermEscape_and_analyticPivot
    P essential solvability archimedean htop j₀ hdata
    frontier.V₀ frontier.hcont frontier.habove frontier.hbelow
    frontier.hslices frontier.hseed frontier.hcoverage

end RawAxiomDischargers
end CertificateChecklist
end WakkerRoadmap

/-! ## Axiom audit (frontier-revealing)

This audit pins down the open mathematical obligations.  After the
multi-session reduction work (see `RawAxiomDischargersAttackPlan.md`),
the end-to-end skeleton depends on:

* **12 primitive `axiom` declarations** in this file: 4, 5, 6, 9, 10,
  12, 13, 14, 15, 16, 17, 19 (Wakker IV.2, IV.5, IV.6 residual content);
* **1 primitive `axiom` declaration** in `RawAxiomDischargersTopology`:
  `coordinateOneStepBracket_of_wakkerCoordinateTopology`
  (Wakker III.4.2 IVT/connectedness step);
* `[propext, Classical.choice, Quot.sound]`.

Historically, this audit listed five frontier obligations as primitive
axioms.  After the reduction work:

* **Obligations 1, 2, 3 are theorem-backed.**  They route through the
  smaller thin-frontier axioms.
* **Obligations 4 and 5 remain as overstrong frontier axioms** (they
  are universally quantified over an arbitrary `V`, which the raw axioms
  cannot constrain).  The end-to-end `additiveRep_nonempty_from_thin_frontier`
  route bypasses those by using the
  `Stage4MatchedAllPairsAdditivityData`-specialized chain and coverage
  seams instead.

* **Axiom 11 (one-step extensibility) was retired** via the topology
  architectural decision in `RawAxiomDischargersTopology`: the smaller
  Wakker III.4.2 IVT/connectedness content lives as a single named
  axiom there, and the rest is theorem-backed in this file under the
  topology bundle.

* **Axiom 18 (chain existence) was retired** via the
  `[Fact (3 ≤ Fintype.card ι)]` regime, routing through axiom 17.

* **Axioms 7 and 8 were retired** as compatibility cleanups (axiom 7
  was dead code after the topology adoption; axiom 8 was discharged
  under `[Nontrivial ι]`).

If any axiom appears in the audit below that is **not** in the
documented thin-frontier list, the skeleton's structural plumbing (not
the math) leaked an extra obligation — that should be tracked and
removed in a follow-up. -/
-- [Option A excision] audit removed (pairwiseFiniteCutCoverageCertificate_from_raw_axioms retired)
-- [Option A excision] audit removed (sharedPivotAllPairsStep4MachineryCertificate_from_raw_axioms retired)
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.nonPivotPairAdditivityCertificate_from_raw_axioms
-- Obligations 4 and 5 (`wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms`
-- and `wakkerStep5CoordinateImageCoverageResidualAtPivot_from_raw_axioms`) were
-- RETIRED in Phase 14: the original consumer now delegates to the thin route,
-- so these overstrong arbitrary-`V` axioms are deleted.  See the audit of
-- `additiveRep_nonempty_from_raw_axioms` below, which no longer lists them.
-- [Option A excision] `additiveRep_nonempty_from_raw_axioms` retired (rested on
-- the unsound base-transport reach axioms).

-- Audit of the **partial discharge** of obligation 1 via the explicit
-- base-transport residual: should report only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseFiniteCutCoverageCertificate_from_raw_axioms_of_baseTransport

-- Audit of the **surjective-grid fragment** of obligation 1: should report
-- only foundational axioms, with no `_from_raw_axioms` dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseFiniteCutCoverageCertificate_from_raw_axioms_of_surjectiveStandardSequences

-- Audit of the **grid-reachability + surjective second-coordinate fragment**
-- of obligation 1.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseFiniteCutCoverageCertificate_from_raw_axioms_of_gridReachability_and_surjectiveSecondCoord

-- Audit of the **grid-reachability + surjective first-coordinate fragment**
-- of obligation 1.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseFiniteCutCoverageCertificate_from_raw_axioms_of_gridReachability_and_surjectiveFirstCoord

-- Audit of the **exact cut-construction fragment** of obligation 1.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseFiniteCutCoverageCertificate_from_raw_axioms_of_pairwiseCutConstructionCertificate

-- Audit of the **partial discharge** of obligation 2 in the singleton
-- coordinate case: should report only
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotAllPairsStep4MachineryCertificate_from_raw_axioms_of_card_eq_one

-- Audit of the **shared-pivot hexagon-family fragment** of obligation 2:
-- should report only foundational axioms, with no `_from_raw_axioms`
-- dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotAllPairsStep4MachineryCertificate_from_raw_axioms_of_sharedPivotHexagonFamily

-- Audit of the **shared-pivot magnitude/bracketing fragment** of obligation
-- 2: should report only foundational axioms, with no `_from_raw_axioms`
-- dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotAllPairsStep4MachineryCertificate_from_raw_axioms_of_sharedPivotMagnitudeBracketingFamily

-- Audit of the **global-gluing fragment** of obligation 3: should report only
-- foundational axioms, with no `_from_raw_axioms` dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.nonPivotPairAdditivityCertificate_from_raw_axioms_of_globalGluingCertificate

-- Audit of the **all-pairs restriction** of obligation 3: should report only
-- foundational axioms, with no `_from_raw_axioms` dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.nonPivotPairAdditivityCertificate_from_raw_axioms_of_allPairsAdditivityCertificate

-- Audit of the **coverage-residual capstone** of obligation 3 (Phase 40): the
-- non-pivot cross-pair additivity certificate is theorem-backed from the unified
-- pivot coordinate-image coverage residual, with NO §IV.6 transport axiom.
-- Should report only `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.nonPivotPairAdditivityCertificate_of_coverageResidual

-- Audit of the **§IV.5+§IV.6 unifying capstone** (Phase 62): obligation 3 from
-- the single representation family + the single coverage residual.  Foundational
-- axioms only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.nonPivotPairAdditivityCertificate_of_gridAdditiveRepresentationFamily_and_coverage

-- Audit of the **surjective-pivot obligation-3 discharge** (Phase 63): obligation
-- 3 from the representation family ALONE when the common pivot utility is
-- surjective (coverage automatic).  Foundational axioms only, no `sorryAx`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.nonPivotPairAdditivityCertificate_of_gridAdditiveRepresentationFamily_surjectivePivot

-- Audit of the **Stage-4-data bridge** (Phase 64): the §IV.5 representation
-- family directly supplies `WakkerStage4PivotSliceRepresentationData`, the
-- end-to-end closure-ladder input.  Foundational axioms only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStage4PivotSliceRepresentationData_of_gridAdditiveRepresentationFamily

-- Audit of the **partial discharge** of obligation 3: should report only
-- `[propext, Classical.choice, Quot.sound]` (no `_from_raw_axioms` axiom).
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.nonPivotPairAdditivityCertificate_of_card_le_two

-- Audit of the **raw-axiom-form low-cardinality discharge** of obligation 3:
-- should report only foundational axioms, with no `_from_raw_axioms` axiom.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.nonPivotPairAdditivityCertificate_from_raw_axioms_of_card_le_two

-- Audit of the **global-certificate restriction** of obligation 4: should
-- report only foundational axioms, with no `_from_raw_axioms` dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5StrictMonotonicityResidualAtPivot_of_strictMonotonicityCertificate

-- Audit of the **global-gluing fragment** of obligation 4: should report only
-- foundational axioms, with no `_from_raw_axioms` dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5StrictMonotonicityResidualAtPivot_of_globalGluingCertificate

-- Audit of the **partial discharge** of obligation 4: should report only
-- `[propext, Classical.choice, Quot.sound]` (no `_from_raw_axioms` axiom).
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5StrictMonotonicityResidualAtPivot_of_card_eq_two

-- Audit of the **raw-axiom-form two-coordinate discharge** of obligation 4:
-- should report only foundational axioms, with no `_from_raw_axioms` axiom.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_card_eq_two

-- Audit of the **global-gluing fragment** of obligation 5: should report only
-- foundational axioms, with no `_from_raw_axioms` dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5CoordinateImageCoverageResidualAtPivot_of_globalGluingCertificate

-- Audit of the **global-certificate restriction** of obligation 5: should
-- report only foundational axioms, with no `_from_raw_axioms` dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5CoordinateImageCoverageResidualAtPivot_of_coordinateImageCoverageCertificate

-- [Option A excision] Audits for the retired (unsound) base-transport reach
-- axioms and their assembly removed.  The surjective-grid fragments below are
-- sound and retained.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseArchimedeanBaseTransportUpperReachCertificate_from_raw_axioms_of_surjectiveStandardSequences

#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseArchimedeanBaseTransportLowerReachCertificate_from_raw_axioms_of_surjectiveStandardSequences

-- Audit of the **surjective-grid fragment** of axiom 6:
-- should report only foundational axioms.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseArchimedeanBaseTransportCertificate_from_raw_axioms_of_surjectiveStandardSequences

-- Audit of the **exact cut-construction fragment** of axiom 6:
-- should report only foundational axioms.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseArchimedeanBaseTransportCertificate_from_raw_axioms_of_pairwiseCutConstructionCertificate

-- Audit of the **grid-reachability + surjective second-coordinate fragment**
-- of axiom 6: should report only foundational axioms.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseArchimedeanBaseTransportCertificate_from_raw_axioms_of_gridReachability_and_surjectiveSecondCoord

-- Audit of the **grid-reachability + surjective first-coordinate fragment**
-- of axiom 6: should report only foundational axioms.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseArchimedeanBaseTransportCertificate_from_raw_axioms_of_gridReachability_and_surjectiveFirstCoord

-- Audit of the **escape-residual discharge** of axiom 6 (Phase 43): the full
-- base-transport certificate and both reach halves are theorem-backed from the
-- single two-axis escape residual via completeness, with NO reach half-axiom.
-- Each should report only `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseArchimedeanBaseTransportCertificate_of_escapeResidual
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseArchimedeanBaseTransportUpperReachCertificate_of_escapeResidual
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseArchimedeanBaseTransportLowerReachCertificate_of_escapeResidual

-- Audit of the theorem-backed strict-pair reduction below the pivot seed seam:
-- should report only foundational axioms.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotStrictPreferenceSeedPairData_of_essential

-- Audit of the **thin frontier 2a.1a.i** seam (now theorem-backed under
-- `[Nontrivial ι]`): should expose only foundational axioms.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotReferenceCoordinateAtPivotData_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.i** derived wrapper: should report only
-- the pivot-level coordinate-choice seam above plus theorem-backed glue.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotReferenceCoordinateOnStrictPreferenceSeedPairData_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.ii** derived pivot-level reference-
-- exchange layer: should report only `Classical.choice` plus the pivot-level
-- coordinate-choice seam above.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotReferenceExchangeAtPivotData_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.ii** pair-attached wrapper: should
-- report only theorem-backed glue over the pivot-level reference-exchange
-- layer above.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotReferenceExchangeOnStrictPreferenceSeedPairData_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.iii** seam (now theorem-backed via
-- the topology compensated reference exchange; was an axiom before
-- Phase 5): should expose only the smaller analytic axioms in
-- `RawAxiomDischargersTopology` (coordinateOneStepBracket and
-- compensating_reference_value_distinct).
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotDescendingSeedWeakPreferenceForwardOnSeedProfileAndReferenceExchangeCertificate_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.iii** derived wrapper: should expose
-- only the smaller canonical forward weak-preference seam above.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotDescendingSeedWeakPreferenceForwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.iv** seam (now theorem-backed via
-- the topology compensated reference exchange): should expose only the
-- same smaller analytic axioms above.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotDescendingSeedWeakPreferenceBackwardOnSeedProfileAndReferenceExchangeCertificate_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.iv** derived wrapper: should expose
-- only the smaller canonical backward weak-preference seam above.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotDescendingSeedWeakPreferenceBackwardOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.v** derived theorem: should expose only
-- the two smaller canonical weak-preference seams above.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotDescendingSeedIndifferenceOnStrictPreferenceSeedPairAndReferenceExchangeCertificate_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.vi** derived theorem: should expose the
-- pivot-level non-pivot-coordinate seam and the two smaller canonical
-- descending weak-preference seams above, but not the theorem-backed strict-
-- pair/reference-value steps.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotStandardSequenceSeedData_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.vii** seam (now theorem-backed under
-- the topology architectural decision; was an axiom before Phase 3): should
-- expose only the smaller analytic seam
-- `coordinateOneStepBracket_of_wakkerCoordinateTopology` from
-- `RawAxiomDischargersTopology.lean`, plus foundational axioms.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotOneStepExtensibleOnSeedProfileAndReferenceExchangeCertificate_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.vii** derived wrapper: should expose
-- only the smaller one-step-extensibility seam above.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotStandardSequenceExtensionOnSeedCertificate_from_raw_axioms

-- Audit of the **thin frontier 2a.1a.viii** obligation 12: now a THEOREM
-- (Phase 17) assembled from the two strictly-weaker half-seams below.  Should
-- expose those two half-seams, not a monolithic injectivity axiom.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotGridInjectiveOnSeedDataCertificate_from_raw_axioms
-- The two strictly-weaker half-seams of obligation 12 (each a primitive axiom):
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotGridWeakDescendingOnSeedDataCertificate_from_raw_axioms
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotGridReverseStrictOnSeedDataCertificate_from_raw_axioms

-- Audit of the **reference-direction discharge** of axiom 12a (Phase 48): the
-- weak-descending half is theorem-backed from the §III.4 reference-direction +
-- cancellation residual via engine B §7, the SAME primitive that discharges the
-- reach/crossing frontier.  Should report only `[propext, Classical.choice,
-- Quot.sound]`, with NO `_from_raw_axioms` dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotGridWeakDescendingOnSeedDataCertificate_of_referenceDirection_and_cancel

-- Audit of the **cancellation-free discharge** of axiom 12a (Phase 53): the
-- cancellation is supplied by the Phase-52 weak-independence topology axiom, so
-- 12a follows from the reference-direction comparison alone.  Should expose the
-- weak-independence topology axiom plus foundational + canonical-construction
-- axioms, NO per-step cancellation seam and NO 12a axiom.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotGridWeakDescendingOnSeedDataCertificate_of_referenceDirection

-- Audit of the **separability discharge** of axiom 12b (Phase 59): the
-- reverse-strict half on the canonical sequence from the separability topology
-- axiom + `spaced`.  Should expose `coordinateWeakSeparable_of_wakkerCoordinateTopology`
-- + canonical-construction axioms, NO 12b axiom.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotGridReverseStrictOnSeedDataCertificate_of_separability

-- Audit of the **escape-route strictness residual** (Phase 67): the Stage-5
-- strictness corridor from the descending-seeded escape residual + solvability,
-- bypassing axiom 17.  Should expose foundational axioms only (the escape
-- residual is a hypothesis), NO axiom-17 bracket dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_of_descendingSeededEscape

-- Audit of the **B1 discharge** (Phase 72): the descending-seeded escape residual
-- from the leaner strict-seeded-above residual + coordinate weak separability.
-- Should expose foundational axioms only (separability + the leaner residual are
-- hypotheses).
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotGridDescendingSeededAboveAtTarget_of_strictSeededAboveData

-- Audit of the **partial discharge** of axiom 12 in the Subsingleton (X j₀) regime.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_subsingleton

-- Audit of the **raw-axiom-form** discharge of axiom 12 in the Subsingleton (X j₀) regime.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotGridInjectiveOnSeedDataCertificate_from_raw_axioms_of_subsingleton

-- Audit of the **thin frontier 2a.1a** derived theorem: should expose exactly
-- the non-pivot-coordinate choice, descending weak-preference, extension, and
-- injective-grid seams above.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotStandardSequenceData_from_raw_axioms

-- Audit of the **thin frontier 2a.1b** axiom 13: RETIRED (Phase 13).  The
-- primitive axiom `sharedPivotNonpivotStandardSequenceFamilyCertificate_from_raw_axioms`
-- was deleted as dead code; the non-pivot family is now discharged from axiom
-- 12 alone via `..._via_pivotData` (audited below).

-- Audit of the **axiom 13 → axiom 12 reduction**: should expose only axiom 12
-- (`sharedPivotPivotGridInjectiveOnSeedDataCertificate_from_raw_axioms`) plus
-- the foundational axioms, and NOT axiom 13 itself.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotNonpivotStandardSequenceFamilyCertificate_from_raw_axioms_via_pivotData

-- Audit of the **thin frontier 2a.1b** derived wrapper: now routed through the
-- axiom 13 → axiom 12 reduction, so it should expose only axiom 12 plus the
-- foundational axioms (no axiom 13).
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotNonpivotStandardSequenceFamilyOnPivotDataCertificate_from_raw_axioms

-- Audit of the **thin frontier 2a.1** derived theorem: should expose exactly
-- the pivot-side sequence-data seam and the smaller pivot-free non-pivot
-- family seam above.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotStandardSequenceFamilyData_from_raw_axioms

-- Audit of the **thin frontier 2a.2a** obligation 14: the hexagon family is now
-- a THEOREM (Phase 20) derived from the strictly-leaner Step-4 order-calibration
-- core (the new primitive).  Should expose the Step-4 family seam, not a hexagon
-- axiom.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms

-- Audit of the **thin frontier 2a.2** derived theorem: should expose only the
-- stronger direct hexagon-family seam above on the same canonical data.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotFiniteCutHexagonTransportFamilyOnDataCertificate_from_raw_axioms

-- Audit of the **thin frontier 2a.2a intermediary bridge**:
-- should expose only theorem-backed glue from the canonical direct
-- hexagon-family seam plus the 2a.3 finite-cut/tradeoff ingredients.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_surjectiveGrids

-- Audit of the **thin frontier 2a.2a canonical-data intermediary**:
-- should expose only theorem-backed glue over the same canonical shared-pivot
-- data ingredients.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotHexagonFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_finiteCutInterpolation_and_transport

-- Audit of the **thin frontier 2a.3a** obligation 14: the Step-4
-- order-calibration family is now a THEOREM (endpoint-1 restate) consuming the
-- named input `SharedPivotGridAdditiveRepresentationFamily`.  Should expose only
-- `[propext, Classical.choice, Quot.sound]` + the accepted topology bracket-reach
-- seams (from the standard-sequence construction) — NO `_from_raw_axioms`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotStep4TradeoffFamilyOnDataCertificate_from_raw_axioms

-- Audit of the **representation ⟹ Step-4** bridges (Phase 50): the per-slice
-- and family Step-4 certificates from a grid-normalized slice representation,
-- connecting the §IV.5 Step-4 seam to engine C's GridAdditiveSliceRep core.
-- Should report only `[propext]` / foundational axioms, NO `_from_raw_axioms`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pairwiseStep4TradeoffMachineryCertificate_of_gridNormalized_representation
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotStep4TradeoffFamilyOnDataCertificate_of_representationFamily

-- Audit of the **shared-pivot grid-additive representation family** capstone
-- (Phase 61): the single §IV.5 representation residual discharges BOTH the Step-4
-- core and the A1 pivot-slice matches.  Foundational axioms only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotStep4TradeoffFamilyOnDataCertificate_of_gridAdditiveRepresentationFamily
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotSliceMatch_of_gridAdditiveRepresentationFamily

-- Audit of the **thin frontier 2a.3b** obligation 15: RETIRED as an independent
-- axiom (Phase 16).  It is now a THEOREM whose entire content reduces to the
-- base-transport obligation 6 (coverage half) plus a fully theorem-backed
-- interpolation/extension step (`z := target`).  The audit should therefore
-- expose the two base-transport half-axioms (6) and the shared-data
-- ingredients, but NO dedicated interpolation axiom.
-- [Option A excision] audit removed (sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_from_raw_axioms retired)
-- The interpolation/extension seam itself is theorem-backed (no axiom):
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotInterpolationExtensionFamilyOnDataCertificate_from_raw_axioms

-- Audit of the **thin frontier 2a.3** derived theorem: should expose only the
-- canonical direct hexagon-family seam and the finite-cut interpolation seam
-- on that same canonical data.
-- [Option A excision] audit removed (sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms retired)

-- Audit of the **thin frontier 2a.3 canonical-data intermediary**:
-- should expose only the canonical step-4 tradeoff and finite-cut
-- interpolation seams on the same shared-pivot data.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotMagnitudeFiniteCutFamilyOnDataCertificate_from_raw_axioms_of_step4Tradeoff_and_finiteCutInterpolation

-- Audit of the **thin frontier 2a** derived theorem: should expose the
-- canonical direct hexagon-family seam, the finite-cut interpolation seam,
-- and the previously thinned shared-data ingredients above.
-- [Option A excision] audit removed (sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms retired)

-- Audit of the **thin frontier 2a canonical-data intermediary**:
-- should expose only theorem-backed transport glue over canonical
-- shared-pivot data.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotMagnitudeFiniteCutTransportFamily_from_raw_axioms_of_magnitudeFiniteCutFamily_and_transportOnData

-- Audit of the **thin frontier 3** obligation 16: now a THEOREM (Phase 18)
-- assembled from the two strictly-weaker directional half-axioms below.  Should
-- expose those two half-seams, not a monolithic conjunctive transport axiom.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.twoPivotSliceTransportCertificate_from_raw_axioms
-- The two strictly-weaker directional half-seams of obligation 16:
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.twoPivotSliceTransportForwardCertificate_from_raw_axioms
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.twoPivotSliceTransportBackwardCertificate_from_raw_axioms

-- Audit of the **partial discharge** of axiom 16 in low cardinality:
-- should report only `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.twoPivotSliceTransportCertificate_of_card_le_two

-- Audit of the **raw-axiom-form low-cardinality discharge** of axiom 16:
-- should report only foundational axioms, with no `_from_raw_axioms` axiom.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.twoPivotSliceTransportCertificate_from_raw_axioms_of_card_le_two

-- Audit of the **directional half-seam discharges** of obligation 16 (Phase 18)
-- in low cardinality: each should report only foundational axioms.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.twoPivotSliceTransportForwardCertificate_of_card_le_two
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.twoPivotSliceTransportBackwardCertificate_of_card_le_two

-- Audit of the **coverage-residual discharge** of obligation 16 (Phase 39):
-- the full transport and both directional halves are theorem-backed from the
-- single pivot coordinate-image coverage residual, via the engine-C transport.
-- Each should report only `[propext, Classical.choice, Quot.sound]`, with NO
-- `_from_raw_axioms` dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.twoPivotSliceTransportCertificate_of_coverageResidual
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.twoPivotSliceTransportForwardCertificate_of_coverageResidual
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.twoPivotSliceTransportBackwardCertificate_of_coverageResidual

-- Audit of the **partial discharge** of axiom 17 in `card ι = 1` regime.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotCoordinateRetargetingBracketAtPivotCertificate_of_card_eq_one

-- Audit of the **escape-residual discharge** of axiom 17 (Phase 42): the
-- pivot-retargeting bracket is theorem-backed from the single two-sided pivot
-- grid escape residual via engine B's Archimedean reach, with NO bracket axiom.
-- Should report only `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotCoordinateRetargetingBracketAtPivotCertificate_of_pivotGridEscapes

-- Audit of the **one-sided descending-seeded discharge** of axiom 17 (Phase 44):
-- the two-sided escape residual and the bracket are theorem-backed from a single
-- one-sided seed condition on a descending grid (lower escape automatic via
-- engine B).  Should report only `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotGridEscapesAtTarget_of_descendingSeededAbove
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotCoordinateRetargetingBracketAtPivotCertificate_of_descendingSeededAbove

-- Audit of the **one-sided ascending-seeded discharge** of axiom 17 (Phase 45):
-- symmetric dual; upper escape automatic via engine B's ascending escape.
-- Should report only `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotGridEscapesAtTarget_of_ascendingSeededBelow
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotCoordinateRetargetingBracketAtPivotCertificate_of_ascendingSeededBelow

-- Audit of the **end-to-end retargeting interface** from the minimal escape
-- residual (Phase 49): the full pivot-compensated retargeting interface from the
-- monotone-seeded escape residual + Archimedean + restricted solvability, no
-- bracket axiom.  Should report only `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotCoordinateRetargetingAtPivotCertificate_of_descendingSeededAbove
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotCoordinateRetargetingAtPivotCertificate_of_ascendingSeededBelow

-- Audit of the **raw-axiom-form** discharge of axiom 17 in `card ι = 1` regime.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_of_card_eq_one

-- Audit of the **partial discharge** of axiom 13 in `card ι = 1` regime.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotNonpivotStandardSequenceFamilyCertificate_of_card_eq_one

-- Audit of the **raw-axiom-form** discharge of axiom 13 in `card ι = 1` regime.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotNonpivotStandardSequenceFamilyCertificate_from_raw_axioms_of_card_eq_one

-- Audit of the **partial discharge** of axiom 14 in `card ι = 1` regime.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotHexagonFamilyOnDataCertificate_of_card_eq_one

-- Audit of the **partial discharge** of axiom 15 in `card ι = 1` regime.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotFiniteCutInterpolationFamilyOnDataCertificate_of_card_eq_one

-- Audit of the **thin frontier 3** derived wrapper: should expose only that
-- smaller local transport seam.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotHexagonTransportCertificate_from_raw_axioms

-- Audit of the **thin frontier 3→A1 compatibility bridge**:
-- should expose only the smaller local transport seam plus theorem-backed
-- stage glue.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.nonPivotPairAdditivityCertificate_from_raw_axioms_of_pivotHexagonTransport

-- Audit of the **thin frontier 4** primitive seam (now theorem-backed under
-- `[Fact (3 ≤ Fintype.card ι)]`): only the smaller pivot-retargeting bracket
-- seam (axiom 17) remains as the actual residual.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms

-- Audit of the **thin frontier 4A→4 compatibility bridge**:
-- should expose only theorem-backed glue over the pivot-retargeting bracket
-- seam.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_pivotCoordinateRetargetingBracket

-- Audit of the **thin frontier 4** derived wrapper: the chosen-A1 strictness
-- residue should expose only the smaller chain seam above.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms

-- Audit of the **all-pairs-driven → broad Step-5 strictness bridge**:
-- should expose only theorem-backed glue above the all-pairs strictness
-- certificate layer.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_allPairsAdditivityDrivenFrontier

-- Audit of the **thin frontier 5** axiom: coverage only on that same chosen
-- Stage-4-matched A1 package.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms

-- Audit of the **global-gluing partial discharge** of axiom 19: should report
-- only foundational axioms, with no `_from_raw_axioms` dependency.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_of_globalGluingCertificate
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms_of_globalGluingCertificate

-- Audit of the **strictly-weaker forward-gluing partial discharge** of axiom 19
-- (Phase 21): uses only the forward `∑V(y) ≤ ∑V(x) → x ≽ y` direction; should
-- report only foundational axioms.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_of_forwardGluing
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.allPairsAdditivityDrivenCoordinateImageCoverageResidualAtPivotCertificate_from_raw_axioms_of_forwardGluing

-- Audit of the **all-pairs-driven → broad Step-5 coverage bridge**:
-- should expose only theorem-backed glue above the all-pairs coverage
-- certificate layer.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_allPairsAdditivityDrivenFrontier

-- Audit of the **stage-matched `_from_raw_axioms_of_...` wrapper ladder**:
-- each entry should expose only the already-audited thin-frontier seams plus
-- theorem-backed assembly glue (no skipped interfaces).
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotHexagonTransportCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotCoordinateRetargetingBracketAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotCoordinateRetargetingAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.allPairsAdditivityDrivenPivotTouchingChainAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.allPairsAdditivityDrivenStrictMonotonicityResidualAtPivotCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.nonPivotPairAdditivityCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5StrictMonotonicityResidualAtPivot_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5CoordinateImageCoverageResidualFamily_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5StrictMonotonicityCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5CoordinateImageCoverageCertificate_from_raw_axioms_of_stage4MatchedAllPairsAdditivityData

-- [Option A excision] `additiveRep_nonempty_from_thin_frontier` retired (rested
-- on the unsound base-transport reach axioms).

-- Audit of the **§IV.5 representation-family end-to-end capstone** (Phase 65):
-- Nonempty (AdditiveRep P) from the single §IV.5 representation residual + the
-- raw/topology/Stage-5 inputs.  The representation family is the single pivot-side
-- entry point; the residual axioms it routes through are exactly the Stage-5
-- coverage/strictness seams plus the topology bundle.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_of_gridAdditiveRepresentationFamily

-- Audit of the **surjective-pivot end-to-end capstone** (Phase 66): axiom-16-free
-- pivot side.  Should expose only the Stage-5 coverage/strictness seams (obl. 5
-- coverage, axiom 17) — NOT axiom 16, 6, 12, or 14.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_of_surjectivePivotRepresentationFamily

-- Audit of the **named-residuals end-to-end capstone** (Phase 68): the additive
-- representation from the §IV.5 surjective-pivot representation family + the
-- escape residual (strictness) + the coverage residual family.  Should expose
-- ONLY `[propext, Classical.choice, Quot.sound]` — NO `_from_raw_axioms` seam
-- (no axiom 6/12/14/16/17, no obl-5 raw seam): all residuals are hypotheses.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_of_namedResiduals

-- Audit of the **bundled-residuals capstone** (Phase 69): the one-hypothesis form
-- (single `WakkerAdditiveRepNamedResiduals` structure).  Should also expose ONLY
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_of_bundledResiduals

-- Audit of the **C2 surjectivity discharge** (Phase 73): the common pivot utility
-- is surjective from connectedness + continuity + two-sided unboundedness (engine-A
-- IVT).  Should expose ONLY `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotUtilitySurjective_of_continuous_unbounded

-- Audit of the **C2 end-to-end capstone** (Phase 73): the additive representation
-- with pivot surjectivity replaced by the analytic inputs (connectedness +
-- continuity + unboundedness).  Should expose ONLY
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_of_namedResiduals_continuousPivot

-- Audit of the **B2 coverage discharge** (Phase 73): the Step-5 coordinate-image
-- coverage residual is theorem-backed from all-pairs additivity + a surjective
-- pivot utility + the leaner equal-additive-score faithfulness residual.  Should
-- expose ONLY `[propext, Classical.choice, Quot.sound]` — NO `_from_raw_axioms`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerStep5CoordinateImageCoverageResidualAtPivot_of_surjectivePivot_and_equalScore

-- Audit of the **WP-B2 equal-score discharge**: the equal-additive-score
-- faithfulness residual is immediate from any additive representation.  Should
-- expose ONLY `[propext, Classical.choice, Quot.sound]` — NO `_from_raw_axioms`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.equalAdditiveScoreWeakPreference_of_additiveRep

-- Audit of the **C1 common-scale compatibility closer** (Phase 74): the §IV.5
-- representation family from the shared-pivot Step-4 tradeoff family + continuity
-- of per-slice pivot utilities + pivot-grid density, with the common-scale
-- compatibility mechanized by the M5 density extension.  Should expose ONLY
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotGridAdditiveRepresentationFamily_of_step4Family_continuous_dense

-- Audit of the **C1 end-to-end capstone** (Phase 74): the additive representation
-- from the Step-4 family + continuity + density.  The C1 closer (above) is the
-- clean deliverable; this composition routes through the Phase-65 capstone and so
-- inherits exactly its documented Stage-5 `_from_raw_axioms` seams (the
-- C1-constructed V₀ is not asserted surjective).  For a seam-free route use the
-- surjective-pivot/named-residuals capstones (Phases 66/68).
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_of_step4Family_continuous_dense

-- Audit of the **B1 §IV.2 standard-sequence existence discharge** (Phase 75): the
-- strict seeded-above grid data from the per-target seed germ + the topology
-- one-step-extensibility (the §III.4.2 IVT/connectedness content) + restricted
-- solvability.  Exposes `[propext, Classical.choice, Quot.sound]` plus the smaller
-- topology analytic seams `coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology`
-- (the documented §III.4.2 frontier carried by the topology bundle) — NO
-- `_from_raw_axioms` seam, no `sorryAx`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotStrictSeededAboveGridData_of_seedDataFamily

-- Audit of the **B1 consolidated descending-escape discharge** (Phases 72 + 75):
-- the descending-seeded escape residual directly from the per-target seed germ +
-- §III.4 separability + topology + solvability.  Exposes
-- `[propext, Classical.choice, Quot.sound]` + the §III.4.2 topology IVT seams.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotGridDescendingSeededAboveAtTarget_of_seedDataFamily

-- Audit of the **maximally-reduced end-to-end capstone** (Phase 76): the additive
-- representation from the B1 seed germ + C2 analytic surjectivity inputs, with C1
-- slices + B2 coverage as the explicit remaining residuals.  Exposes
-- `[propext, Classical.choice, Quot.sound]` plus the documented topology/§IV seams
-- inherited from `additiveRep_nonempty_of_namedResiduals`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_of_seedGerm_and_analyticPivot

-- WP0 (Option B): the unified canonical target and its bridge to the public
-- Wakker IV.2.7 wrapper.  Coordinate independence enters only via htop.separable.
-- Should expose `[propext, Classical.choice, Quot.sound]` + the two §III.4.2
-- topology IVT seams `coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology`,
-- and NONE of: `*_from_raw_axioms`, `sorryAx`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_from_structural_axioms_and_coordinateIndependence
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.wakkerConstruction_of_structural_axioms_and_coordinateIndependence

-- WP-T: the reach-axiom-free B1 discharge.  Should expose ONLY
-- `[propext, Classical.choice, Quot.sound]` — NO coordinateOneStepBracket* axiom,
-- no sorryAx.  The §IV.2.6 escape grid is carried in the enriched seed germ.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.pivotStrictSeededAboveGridData_of_seedDataWithEscapeFamily

-- WP-T: the reach-axiom-free canonical target.  Should expose ONLY
-- `[propext, Classical.choice, Quot.sound]` — NO coordinateOneStepBracket* axiom,
-- NO _from_raw_axioms seam, no sorryAx.  This is the WP-T endpoint: the §III.4.2
-- topology IVT seams are eliminated from the canonical Option-B target.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.additiveRep_nonempty_from_structural_axioms_reachAxiomFree

-- §IV.2.6 injectivity halves (axiom 12a/12b) — now THEOREMS, not axioms.
-- Both should report only `[propext, Classical.choice, Quot.sound]`:
-- the weak-descending half via `weaklyDescending_of_separable_and_isStrict`
-- (reference direction derived from step-0 strictness + separability), the
-- reverse-strict half via `reverseStrict_family_of_wakkerCoordinateTopology`.
-- NO `_from_raw_axioms` seam, no `sorryAx`.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotGridWeakDescendingOnSeedDataCertificate_from_raw_axioms
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotGridReverseStrictOnSeedDataCertificate_from_raw_axioms
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargers.sharedPivotPivotGridInjectiveOnSeedDataCertificate_from_raw_axioms
