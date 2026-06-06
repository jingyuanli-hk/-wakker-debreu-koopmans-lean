/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — Candidate D: the cardinal-grid companion (the wall is ordinal-specific)

> **STATUS: `sorry`-free companion theorem.  Demonstrates that the C1.a cross-pair wall
> is FREE given a cardinal grid datum — i.e. the wall is specific to the *ordinal*
> axiom set.**
> Not in the umbrella import.

This file executes **Candidate D** of `OptionB_AlternativeAxiomScoping.md`, the one
alternative axiom set the scoping found genuinely worth building. It is a **companion**
result, **not** Wakker IV.2.7: it shows that on a *cardinal* grid — where the slice
already carries an explicit grid-additive order (the coordinate metric), packaged as
`GridAdditiveSliceRep` — the grid Thomsen closure (the irreducible C1.a wall in the
ordinal setting) is **free**.

## What this demonstrates (and what it honestly does not)

The seven C1.a findings proved the cross-pair Thomsen content is irreducible from
Wakker's *ordinal* axioms. Candidate D confirms the complementary fact: that
irreducibility is **specific to the ordinal axiom set**. Given a *cardinal* grid datum
(the grid order IS the index-sum order, via the coordinate metric), the grid Thomsen
closure and the diagonal step are immediate — `concreteDiagonalStep_of_rep` /
`gridIndiff_iff_eqSum_of_rep`, both already free from `GridAdditiveSliceRep`.

**This is NOT a proof of Wakker IV.2.7**: the cardinal grid datum *assumes the cardinal
scale* (the grid metric) that the ordinal theorem is meant to *construct* from ordinal
preference. Per the scoping discipline (gates 3,4), Candidate D is "free" only by
assuming more — it is the honest cardinal companion, clearly distinguished from the
ordinal claim. Its value: it pins down exactly where the ordinal difficulty lives (in
constructing the scale), by showing everything downstream is free once the scale is given.

## What this file delivers (all machine-checked, no `sorry`)

* `CardinalGridSliceStructure P base j k` — the cardinal datum: explicit grids + a
  grid-additive representation `GridAdditiveSliceRep` with the index-sum score (the grid
  order is the metric index-sum order).
* `concreteDiagonalStep_free_of_cardinalGrid` — **the probe (gate 3 passes)**: the
  diagonal step (the C1.a wall) is FREE from the cardinal datum.
* `gridThomsenClosure_free_of_cardinalGrid` — equal-index-sum grid indifference is free
  from the cardinal datum.
* `cardinalGridSliceStructure_of_additiveRep` — **the soundness gate (gate 2)**: a rep
  with a strictly-increasing, equal-spaced, normalized grid supplies the cardinal datum
  (rep-necessary on the grid).

## Honest scope

Candidate D is sound (gate 2 ✓) and the wall is free given the datum (gate 3 ✓), but it
assumes the cardinal scale (gate 4: it is a *different, weaker* theorem than the ordinal
Wakker IV.2.7). It is recorded as the companion that localizes the ordinal difficulty:
the §IV.5 construction's entire job is producing `GridAdditiveSliceRep` from ordinal
data, and Candidate D shows that once it is given (cardinally), the rest is free. The
ordinal theorem remains gated on the §6 fallback / the §IV.5 construction.

Imports `OptionB_EqualSpacingSliceRep` (G4.a: `gridIndexSumScore`,
`gridAdditiveSliceRep_of_additiveRep`; transitively `RawAxiomDischargersHexagon` for
`GridAdditiveSliceRep`, `concreteDiagonalStep_of_rep`, `gridIndiff_iff_eqSum_of_rep`).
Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_EqualSpacingSliceRep

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

/-! ## §A.  The cardinal grid slice structure (the cardinal datum)

A cardinal grid slice structure packages the data that, in a *cardinal* setting, comes
for free from the coordinate metric: explicit grids `vⱼ, vₖ` and coordinate metrics
`Vⱼ, Vₖ` whose index-sum score `gridIndexSumScore j k Vⱼ Vₖ` grid-additively represents
the preference on the grid (`GridAdditiveSliceRep`).  This is exactly the C1.a output
(`GridAdditiveSliceRep`) — but taken as a **given** (the metric), not constructed from
ordinal data. -/

/-- **Cardinal grid slice structure** over a base profile and a coordinate pair `(j,k)`.

The grid order is the index-sum order via the coordinate metric.  In the cardinal
setting (`X i = ℝ`/`ℚ` with the coordinate value carrying metric meaning) this holds
definitionally; here it is the named cardinal datum. -/
structure CardinalGridSliceStructure (P : ProductPref X) (base : Profile X) (j k : ι) where
  /-- The `j`-coordinate grid. -/
  vⱼ   : ℕ → X j
  /-- The `k`-coordinate grid. -/
  vₖ   : ℕ → X k
  /-- The `j`-coordinate metric (cardinal utility). -/
  Vⱼ   : X j → ℝ
  /-- The `k`-coordinate metric (cardinal utility). -/
  Vₖ   : X k → ℝ
  /-- The grid-additive representation: the grid order IS the index-sum order. -/
  rep  : GridAdditiveSliceRep P base j k vⱼ vₖ (gridIndexSumScore j k Vⱼ Vₖ)

/-! ## §B.  The probe (gate 3): the C1.a wall is FREE on the cardinal grid -/

/-- **The diagonal step (the C1.a wall) is FREE from the cardinal datum (PROVED).**

`ConcreteDiagonalStep` — the grid diagonal step that, in the ordinal setting, is the
irreducible C1.a wall (seven findings) — follows immediately from the cardinal grid
slice structure via `concreteDiagonalStep_of_rep`.  This is the Candidate-D probe: the
wall vanishes once the cardinal grid order is given.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem concreteDiagonalStep_free_of_cardinalGrid
    [ProductPref.IsWeakOrder P] {base : Profile X} {j k : ι}
    (G : CardinalGridSliceStructure P base j k) :
    ConcreteDiagonalStep P base j k G.vⱼ G.vₖ :=
  concreteDiagonalStep_of_rep P base j k G.vⱼ G.vₖ
    (gridIndexSumScore j k G.Vⱼ G.Vₖ) G.rep

/-- **Equal-index-sum grid indifference is FREE from the cardinal datum (PROVED).**

The full grid Thomsen content `g n m ∼ g n' m' ↔ n + m = n' + m'` follows from the
cardinal grid slice structure via `gridIndiff_iff_eqSum_of_rep`.  So the entire
equal-spacing closure — the §IV.5 grid target — is free on the cardinal grid.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem gridThomsenClosure_free_of_cardinalGrid
    [ProductPref.IsWeakOrder P] {base : Profile X} {j k : ι}
    (G : CardinalGridSliceStructure P base j k) (n m n' m' : ℕ) :
    P.indiff (concreteGrid base j k G.vⱼ G.vₖ n m)
             (concreteGrid base j k G.vⱼ G.vₖ n' m') ↔ n + m = n' + m' :=
  gridIndiff_iff_eqSum_of_rep P base j k G.vⱼ G.vₖ
    (gridIndexSumScore j k G.Vⱼ G.Vₖ) G.rep n m n' m'

/-! ## §C.  The soundness gate (gate 2): the cardinal datum is rep-necessary -/

/-- **Soundness gate (PROVED): a representation supplies the cardinal grid datum.**

Under an additive representation `R` with a strictly-increasing, equal-spaced, normalized
grid (the hypotheses of G4.a's `gridAdditiveSliceRep_of_additiveRep`), the cardinal grid
slice structure holds with metrics `Vⱼ, Vₖ` the grid-normalized utilities.  So the
cardinal datum is necessary under a rep — carrying it hides nothing false (it is exactly
the cardinal scale a representation provides on the grid).  Audit `[propext,
Classical.choice, Quot.sound]`. -/
noncomputable def cardinalGridSliceStructure_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k : ι} (hjk : j ≠ k)
    {σⱼ : StandardSequence P j} {σₖ : StandardSequence P k}
    {Vⱼ : X j → ℝ} {Vₖ : X k → ℝ}
    (hgrid : WakkerRoadmap.CertificateChecklist.PairwiseGridNormalizationWitness σⱼ σₖ Vⱼ Vₖ)
    (base : Profile X)
    (hjmono : ∀ n, R.V j (σⱼ.α n) < R.V j (σⱼ.α (n + 1)))
    (hkmono : ∀ m, R.V k (σₖ.α m) < R.V k (σₖ.α (m + 1)))
    (hspace : ∀ n m,
      R.V j (σⱼ.α (n + 1)) + R.V k (σₖ.α m) = R.V j (σⱼ.α n) + R.V k (σₖ.α (m + 1))) :
    CardinalGridSliceStructure P base j k where
  vⱼ  := σⱼ.α
  vₖ  := σₖ.α
  Vⱼ  := Vⱼ
  Vₖ  := Vₖ
  rep := gridAdditiveSliceRep_of_additiveRep R hjk hgrid base hjmono hkmono hspace

end ProductPref
end WakkerInfra

/-! ## Candidate D (cardinal-grid companion) audit

* §A: `CardinalGridSliceStructure` — the cardinal datum (the grid order IS the index-sum
  order via the coordinate metric).
* §B (gate 3, the probe — PASSES): `concreteDiagonalStep_free_of_cardinalGrid`,
  `gridThomsenClosure_free_of_cardinalGrid` — the C1.a wall (the diagonal step / grid
  Thomsen closure) is FREE given the cardinal datum.
* §C (gate 2): `cardinalGridSliceStructure_of_additiveRep` — the cardinal datum is
  necessary under a rep with a strict, equal-spaced, normalized grid.

**Honest scope.**  Candidate D is sound (gate 2 ✓) and the C1.a wall is free given the
cardinal datum (gate 3 ✓) — but it **assumes the cardinal scale** (gate 4: a different,
weaker theorem than ordinal Wakker IV.2.7).  It is the companion that localizes the
ordinal difficulty: the §IV.5 construction's entire job is producing
`GridAdditiveSliceRep` from ordinal data, and Candidate D shows everything downstream is
free once that scale is given cardinally.  The ordinal theorem remains gated on the §6
fallback / the §IV.5 construction.  Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.concreteDiagonalStep_free_of_cardinalGrid
#print axioms WakkerInfra.ProductPref.gridThomsenClosure_free_of_cardinalGrid
#print axioms WakkerInfra.ProductPref.cardinalGridSliceStructure_of_additiveRep
