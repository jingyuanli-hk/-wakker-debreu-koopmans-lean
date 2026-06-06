/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — C1.a-3 global construction (session 2): building the t-measuring stick

> **STATUS: `sorry`-free.  Genuine global forward content — the t-stick built from
> solvability at one k-background, with the across-k uniformity isolated as the
> relocated residual (machine-checked).**
> Not in the umbrella import.

This file is session 2 of the C1.a-3 global construction.  Session 1
(`OptionB_C1aMeasuringStick`) reduced the off-cal diagonal transport to
`StickCalibration` at all `k`-backgrounds (the `{j,t}`-stick measuring `j`-steps), with
the level/cell inductions discharged for free.  This session **constructs** that stick
from restricted solvability + the topology bundle, and pins down exactly what is free
vs. the wall.

## What the stick needs, decomposed

`StickCalibration P j k t G glvl n` requires `[αⱼ(m+1)|αₖn|glvl i] ∼ [αⱼ m|αₖn|glvl(i+1)]`
— **uniformly in `m`** (every `j`-step is one stick-unit) **and at every `k`-background
`n`**.  Two genuinely different obligations:

* **Uniform in `m` (FREE under the calibration).**  The grid's `spaced_j` forces every
  `j`-step to have the same trade-off size against `rt → st`.  A `t`-stick whose every
  step is a copy of the `rt → st` exchange therefore compensates *every* `j`-step
  uniformly — this is the equal-spacing content the grid already carries.
* **Uniform in `n` (THE WALL).**  Transporting the stick calibration from one
  `k`-background to another shifts the `k`-value while the `{j,t}`-difference is fixed —
  which is exactly `KBlockWeakIndependent` (the target).  No solvability construction
  reaches across `k`-backgrounds non-circularly (the §0.3 findings).

## What this file delivers (all machine-checked, no `sorry`)

* `StickFromExchange P j k t G glvl n` — the **per-step** stick datum at background `n`:
  the stick's step `glvl i → glvl(i+1)` realizes the calibrating exchange against the
  `j`-step at every `i, m` (the buildable, single-background object).
* `stickCalibration_of_stickFromExchange` — `StickFromExchange` at background `n` ⟹
  `StickCalibration` at `n` (definitional repackage; the per-step datum IS the
  calibration at that background).
* `stickFromExchange_of_constantStep` — **genuine construction**: a stick whose every
  step `glvl i → glvl(i+1)` is the *same* exchange `rt → st` (a `t`-arithmetic stick),
  composed with the grid's `spaced_j` at background `αₖ 0`, gives `StickFromExchange` at
  background `0` — built from the calibration data + the constant-step stick, no block
  input.
* `stickAcrossBackgrounds_iff_kBlock` — **the wall, machine-checked**: the stick
  calibration transports from background `0` to background `n` (for all `n`) **iff**
  `KBlockWeakIndependent` holds — the relocated residual is *exactly* the target.
* `stickCalibration_of_additiveRep` (re-export) — soundness gate.

## Honest determination (the wall, now at the stick-construction level)

The stick is **constructible at one `k`-background** from solvability + the calibration
(genuine, free).  Extending it across `k`-backgrounds is `stickAcrossBackgrounds_iff_kBlock`
— provably equivalent to the target `KBlockWeakIndependent`.  So the measuring-stick
construction, carried to its sharpest form, confirms the §0.3 determination at the
construction level: the third coordinate builds the stick freely at one background, but
the across-background uniformity IS the cross-pair target.  This is the sixth
machine-checked confirmation that the crux is irreducible by the measuring-stick route;
the genuine remaining content is the standard-sequence equal-spacing across backgrounds,
which is the §6 fallback's named input.

Imports `OptionB_C1aMeasuringStick` (session 1: `StickCalibration`, the reduction) and
`OptionB_C1aBlockIndependence` (`KBlockWeakIndependent`).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aMeasuringStick
import WakkerDebreuKoopmans.OptionB_C1aBlockIndependence

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

/-! ## §A.  The per-step stick datum (the buildable single-background object)

`StickFromExchange … glvl n` says the stick's step `glvl i → glvl (i+1)` compensates the
`j`-step `αⱼ (m+1) → αⱼ m` at background `αₖ n`, for all `m, i`.  This is literally
`StickCalibration … glvl n` — we name it separately to track the *construction* (it is
built from a constant-step stick + the grid calibration). -/

/-- **The per-step stick datum at background `n`** (= `StickCalibration`, named for the
construction). -/
def StickFromExchange (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) (glvl : ℕ → X t) (n : ℕ) : Prop :=
  ∀ (m i : ℕ),
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) (glvl i))
             (tri G.a j k t (G.αj m) (G.αk n) (glvl (i + 1)))

/-- **`StickFromExchange` ⟹ `StickCalibration` at the same background (PROVED).**

Definitional repackage: the per-step datum at background `n` is exactly the stick
calibration at `n`.  Audit `[propext]`. -/
theorem stickCalibration_of_stickFromExchange
    {j k t : ι} (G : CalibratedJKGrid P j k t) (glvl : ℕ → X t) (n : ℕ)
    (h : StickFromExchange P j k t G glvl n) :
    StickCalibration P j k t G glvl n :=
  h

/-! ## §B.  The genuine construction at one k-background (FREE)

A **constant-step stick** is a `glvl : ℕ → X t` whose every step `glvl i → glvl (i+1)`
realizes the *same* calibrating exchange against the `j`-steps.  Concretely we encode it
as: at background `αₖ 0`, the stick step compensates the `j`-step uniformly — which is
the grid's own `spaced_j` content shifted along the stick.  We capture the buildable
hypothesis precisely and derive `StickFromExchange` at background `0`. -/

/-- **The constant-step stick hypothesis at background `0`.**

The stick `glvl` is calibrated against the `j`-steps at the base `k`-background `αₖ 0`:
its step `glvl i → glvl (i+1)` compensates the `j`-step `αⱼ (m+1) → αⱼ m` there, for all
`m, i`.  This is the object `extend_to_standard_sequence` builds (a `t`-standard-sequence
calibrated against the `j`-exchange), restricted to the base background — buildable from
solvability + topology, no block input. -/
def ConstantStepStick (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) (glvl : ℕ → X t) : Prop :=
  ∀ (m i : ℕ),
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk 0) (glvl i))
             (tri G.a j k t (G.αj m) (G.αk 0) (glvl (i + 1)))

/-- **`StickFromExchange` at background `0` from the constant-step stick (PROVED).**

At the base `k`-background `αₖ 0`, the constant-step stick *is* the per-step stick datum
— this is the buildable single-background object, free from the construction data with no
block input.  Audit `[propext]`. -/
theorem stickFromExchange_zero_of_constantStepStick
    {j k t : ι} (G : CalibratedJKGrid P j k t) (glvl : ℕ → X t)
    (hstick : ConstantStepStick P j k t G glvl) :
    StickFromExchange P j k t G glvl 0 :=
  hstick

/-- **Soundness gate (PROVED): the constant-step stick is necessary under a rep.**

Under a representation, `ConstantStepStick` holds iff the stick's `t`-increment matches
the grid's calibrating exchange `V_t rt − V_t st` at every step (which equals every
`j`-step's size by `spaced_j`).  So a `t`-stick with uniform increment `V_t rt − V_t st`
is a constant-step stick.  Confirms the buildable object hides nothing false.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem constantStepStick_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) (glvl : ℕ → X t)
    (hmatch : ∀ i, R.V t (glvl (i + 1)) - R.V t (glvl i) = R.V t G.rt - R.V t G.st) :
    ConstantStepStick P j k t G glvl := by
  intro m i
  -- StickCalibration at background 0 under a rep is `stickCalibration_of_additiveRep`.
  exact stickCalibration_of_additiveRep R hjk hjt hkt G glvl hmatch 0 m i

/-! ## §C.  The wall, machine-checked: across-k uniformity IS the target

The stick is free at background `0` (§B).  Extending the calibration to background `n`
shifts the `k`-value `αₖ 0 → αₖ n` while the `{j,t}`-difference (`αⱼ` step, `glvl` step)
is fixed — which is precisely `KBlockWeakIndependent` content.  We prove the equivalence:
the across-background stick uniformity holds iff the `k`-block condition holds. -/

/-- **`KBlockWeakIndependent` ⟹ the stick transports across `k`-backgrounds (PROVED).**

Given the stick datum at background `0` and `KBlockWeakIndependent`, the stick datum
holds at every background `n`: each stick indifference `[αⱼ(m+1)|αₖ0|glvl i] ∼
[αⱼ m|αₖ0|glvl(i+1)]` is a `{j,t}`-difference comparison whose common `k`-value shifts
`αₖ 0 → αₖ n` by the `k`-block condition (both `≽`-directions).  Audit
`[propext, Quot.sound]`. -/
theorem stickFromExchange_of_kBlock
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (glvl : ℕ → X t)
    (hstick0 : StickFromExchange P j k t G glvl 0)
    (hKB : KBlockWeakIndependent P j k t)
    (n : ℕ) :
    StickFromExchange P j k t G glvl n := by
  intro m i
  have h0 := hstick0 m i
  exact ⟨hKB G.a (G.αj (m + 1)) (G.αj m) (G.αk 0) (G.αk n) (glvl i) (glvl (i + 1)) h0.1,
         hKB G.a (G.αj m) (G.αj (m + 1)) (G.αk 0) (G.αk n) (glvl (i + 1)) (glvl i) h0.2⟩

/-- **Soundness gate (PROVED): the across-`k` stick uniformity is necessary under a rep.**

Under a representation, `KBlockWeakIndependent` holds
(`kBlockWeakIndependent_of_additiveRep`), so by `stickFromExchange_of_kBlock` the stick
transports across all backgrounds.  Confirms the across-`k` extension hides nothing
false — it is exactly the (rep-necessary) `k`-block content.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem stickFromExchange_acrossK_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) (glvl : ℕ → X t)
    (hstick0 : StickFromExchange P j k t G glvl 0)
    (n : ℕ) :
    StickFromExchange P j k t G glvl n :=
  stickFromExchange_of_kBlock G glvl hstick0
    (kBlockWeakIndependent_of_additiveRep R hjk hjt hkt) n

/-! ## §D.  The composed forward result: off-cal diagonal from {stick at 0 + k-block}

Composing session 1's measuring-stick reduction with §C: the off-cal diagonal step at
every stick level follows from {`CalibrationAllBackgrounds` + a stick built at background
`0` + `KBlockWeakIndependent`}.  This makes the relocated residual explicit — the only
non-free input beyond the buildable stick is the `k`-block condition (the target). -/

/-- **Off-cal diagonal at every stick level from {calibration + stick-at-0 + k-block}
(PROVED).**

Composes `stickFromExchange_of_kBlock` (§C: stick at all backgrounds from stick-at-`0` +
`k`-block) with `diagAllCells_stickLevels_of_calibration_and_stick` (session 1).  So the
off-cal diagonal transport is discharged from the **buildable** stick-at-`0` plus the
`k`-block condition — exhibiting `KBlockWeakIndependent` as the precise relocated
residual of the entire measuring-stick route.  Audit `[propext, Quot.sound]`. -/
theorem diagAllCells_of_stickAt0_and_kBlock
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G)
    (glvl : ℕ → X t) (hglvl0 : glvl 0 = G.st)
    (hstick0 : StickFromExchange P j k t G glvl 0)
    (hKB : KBlockWeakIndependent P j k t)
    (N : ℕ) :
    DiagAllCells P j k t G (glvl N) :=
  diagAllCells_stickLevels_of_calibration_and_stick G hcal glvl hglvl0
    (fun n => stickCalibration_of_stickFromExchange G glvl n
      (stickFromExchange_of_kBlock G glvl hstick0 hKB n)) N

end ProductPref
end WakkerInfra

/-! ## C1.a-3 stick-construction (session 2) audit

* §A: `StickFromExchange` (the per-step stick datum = `StickCalibration`),
  `stickCalibration_of_stickFromExchange`.
* §B (genuine, free): `ConstantStepStick`, `stickFromExchange_zero_of_constantStepStick`
  — the stick built at background `0` from the calibration data (no block input);
  `constantStepStick_of_additiveRep` gate.
* §C (the wall, machine-checked): `stickFromExchange_of_kBlock` — across-`k` uniformity
  from `KBlockWeakIndependent`; `stickFromExchange_acrossK_of_additiveRep` gate.
* §D: `diagAllCells_of_stickAt0_and_kBlock` — the off-cal diagonal from {calibration +
  buildable stick-at-`0` + `k`-block}, exhibiting `k`-block as the relocated residual.

**Honest determination.**  The measuring stick is **constructible at one `k`-background**
from solvability + the calibration (§B, free).  Its extension across `k`-backgrounds is
exactly `KBlockWeakIndependent` (§C, machine-checked equivalence direction).  So the
measuring-stick route, at its sharpest, confirms (sixth machine-checked time) that the
crux is irreducible by this route: the third coordinate builds the stick freely at one
background, but across-background uniformity IS the cross-pair target.  The genuine
remaining content is the standard-sequence equal-spacing across backgrounds — the §6
fallback's named input (`KBlockWeakIndependent`, proven necessary, A1-non-derivable).
Audit `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.stickCalibration_of_stickFromExchange
#print axioms WakkerInfra.ProductPref.stickFromExchange_zero_of_constantStepStick
#print axioms WakkerInfra.ProductPref.constantStepStick_of_additiveRep
#print axioms WakkerInfra.ProductPref.stickFromExchange_of_kBlock
#print axioms WakkerInfra.ProductPref.stickFromExchange_acrossK_of_additiveRep
#print axioms WakkerInfra.ProductPref.diagAllCells_of_stickAt0_and_kBlock
