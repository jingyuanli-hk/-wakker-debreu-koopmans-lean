/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — G1.b: propagate the calibrated cell to the full grid Thomsen closure

> **STATUS: `sorry`-free forward brick on the §IV.5 grid construction (G1.b).**
> Not in the umbrella import.

This file executes **G1.b** of `OptionB_SectionIV5GridConstructionRoadmap.md`:
*propagate* the single-cell calibration delivered by G1.a
(`OptionB_EqualSpacingThomsenCell.calibrationAllBackgrounds_of_blockIndependence`)
to the **full grid Thomsen closure** `GridThomsenClosure` — equal-index-sum
indifference at *every* grid point and *every* `t`-level — through the standard
**KLST block separability** vocabulary, the non-circular route.

## The two propagation moves (both non-circular)

G1.a gave `CalibrationAllBackgrounds`: the `j`/`k` calibrating exchanges `rt → st`
are indifferences at *every* grid background `(αⱼ m, αₖ n)`.  By
`interiorDiagonalStep_st_of_allBackgrounds` (free weak order) this already gives the
diagonal step at the **single** calibration level `st`, for **all** `(m,n)`.  Two
things remain to reach the full closure:

1. **Level propagation** `st → c` (all `t`-levels).  This is exactly the `t`-block
   separability move.  We use the canonical KLST condition
   `TBlockWeakIndependent` — necessary under a rep
   (`tBlockWeakIndependent_of_additiveRep`), not A1-derivable (the strip probe) —
   **not** the §D.2b-circular `TBlockDiagonalResidue`.  This is the non-circular
   analog of `diagonalStepLevelMove_of_tBlockDiagonalResidue`.

2. **Order-theory closure** (all `(m,n,m',n')` with equal index sum).  Free:
   `gridThomsenClosure_of_gridDiagonalStep` (pure weak order, no §IV.5 content).

## What this file delivers (all machine-checked, no `sorry`)

* `gridDiagonalStepLevelMove_of_tBlockWeakIndependent` — the `st → c` level
  propagation of the interior diagonal step from `TBlockWeakIndependent` (the
  non-circular level move).
* `gridDiagonalStep_of_calibration_and_tBlock` — the full `GridDiagonalStep` (all
  `(m,n)`, all `c`) from `CalibrationAllBackgrounds` + `TBlockWeakIndependent`.
* `gridDiagonalStep_of_blockIndependence` — chaining G1.a: the full diagonal step
  straight from the **three** KLST block conditions `{T,K,J}`-block.
* `gridThomsenClosure_of_blockIndependence` — **the G1.b target**: the full grid
  Thomsen closure from the three block conditions (the `gridThomsenClosure_of_…`
  promised by the G1.a file, now delivered).
* soundness gates (`gridDiagonalStep_of_additiveRep`, the block necessities
  re-exported) confirming the propagation hides nothing false.

## Honest scope

G1.a reduced the *calibration* to block separability; G1.b now shows the calibration
**propagates** to the entire grid closure through the *same* standard block
vocabulary — the `t`-block move is `TBlockWeakIndependent`, the closure is free order
theory.  So the §IV.5 grid Thomsen closure is fully reduced to Wakker's three KLST
block-independence conditions, each proved necessary and A1-non-derivable.
Discharging those three from bare restricted solvability is the remaining G1 / §IV.5
content (the genuine `n ≥ 3` cancellation crux the five impossibility findings pin).

Imports `OptionB_EqualSpacingThomsenCell` (G1.a calibration) and its transitive
imports (`OptionB_C1aGridThomsen`, `OptionB_C1aBlockIndependence`).  Not in the
umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_EqualSpacingThomsenCell
import WakkerDebreuKoopmans.OptionB_C1aBlockIndependence

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

/-! ## §A.  Level propagation `st → c` from `t`-block separability

`interiorDiagonalStep_st_of_allBackgrounds` gives the diagonal step
`(αⱼ (m+1), αₖ n, st) ∼ (αⱼ m, αₖ (n+1), st)` at the single calibration level `st`.
The two profiles differ in `{j,k}` (and share the common `t`-value `st`), so shifting
the common `t`-value `st → c` is exactly `TBlockWeakIndependent`, applied in both
`≽`-directions.  This is the **non-circular** level move: it uses the canonical KLST
`t`-block separability, not the §D.2b-circular `TBlockDiagonalResidue`. -/

/-- **Level move of the interior diagonal step from `t`-block separability (PROVED).**

From all-background calibration (interior step at level `st`) plus the canonical KLST
`TBlockWeakIndependent`, the diagonal step transports to *every* `t`-level `c`:
`(αⱼ (m+1), αₖ n, c) ∼ (αⱼ m, αₖ (n+1), c)`.  This is the non-circular analog of
`diagonalStepLevelMove_of_tBlockDiagonalResidue` (it consumes the weakPref block
separability, not the circular diagonal residue).  Audit `[propext, Quot.sound]`. -/
theorem gridDiagonalStepLevelMove_of_tBlockWeakIndependent
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G)
    (hTB : TBlockWeakIndependent P j k t)
    (m n : ℕ) (c : X t) :
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n)     c)
             (tri G.a j k t (G.αj m)       (G.αk (n + 1)) c) := by
  have hstep := interiorDiagonalStep_st_of_allBackgrounds G hcal m n
  rcases hstep with ⟨hfwd, hbwd⟩
  refine ⟨?_, ?_⟩
  · -- shift the common `t`-value `st → c` (forward direction).
    exact hTB G.a (G.αj (m + 1)) (G.αj m) (G.αk (n + 1)) (G.αk n) G.st c hfwd
  · -- backward direction (swap `(x,r) ↔ (z,p)`).
    exact hTB G.a (G.αj m) (G.αj (m + 1)) (G.αk n) (G.αk (n + 1)) G.st c hbwd

/-! ## §B.  The full grid diagonal step, then the closure -/

/-- **Full grid diagonal step from calibration + `t`-block separability (PROVED).**

Packages §A over all `(m,n)` and all `c`: the entire `GridDiagonalStep` from
`CalibrationAllBackgrounds` + `TBlockWeakIndependent`.  Audit `[propext,
Quot.sound]`. -/
theorem gridDiagonalStep_of_calibration_and_tBlock
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G)
    (hTB : TBlockWeakIndependent P j k t) :
    GridDiagonalStep P j k t G :=
  fun m n c => gridDiagonalStepLevelMove_of_tBlockWeakIndependent G hcal hTB m n c

/-- **Full grid diagonal step from the three KLST block conditions (PROVED).**

Chains G1.a (`calibrationAllBackgrounds_of_blockIndependence`, from `{K,J}`-block)
with the §A level move (from `T`-block).  So the entire grid diagonal step follows
from the **three** standard KLST block-independence conditions — the non-circular
route end-to-end (no diagonal residues).  Audit `[propext, Quot.sound]`. -/
theorem gridDiagonalStep_of_blockIndependence
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hTB : TBlockWeakIndependent P j k t)
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t) :
    GridDiagonalStep P j k t G :=
  gridDiagonalStep_of_calibration_and_tBlock G
    (calibrationAllBackgrounds_of_blockIndependence G hKB hJB) hTB

/-- **G1.b target: the full grid Thomsen closure from the three KLST block
conditions (PROVED).**

The final propagate step: compose `gridDiagonalStep_of_blockIndependence` with the
free order-theory reduction `gridThomsenClosure_of_gridDiagonalStep`.  This is the
`gridThomsenClosure_of_blockIndependence` promised by the G1.a file (now delivered):
the entire `GridThomsenClosure` (equal-index-sum indifference at every grid point and
every `t`-level) from Wakker's three KLST block-independence conditions, through the
non-circular block-separability route.  Audit `[propext, Quot.sound]`. -/
theorem gridThomsenClosure_of_blockIndependence
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hTB : TBlockWeakIndependent P j k t)
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t) :
    GridThomsenClosure P j k t G :=
  gridThomsenClosure_of_gridDiagonalStep G
    (gridDiagonalStep_of_blockIndependence G hTB hKB hJB)

/-! ## §C.  Soundness gates -/

/-- **Soundness gate (PROVED): the propagated diagonal step is necessary under a
rep.**

Re-export of `gridDiagonalStep_of_additiveRep`.  Confirms the level-propagated
diagonal step hides nothing false.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem gridDiagonalStep_necessary
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) :
    GridDiagonalStep P j k t G :=
  gridDiagonalStep_of_additiveRep R hjk hjt hkt G

/-- **Soundness gate (PROVED): the grid Thomsen closure is necessary under a rep.**

Re-export of `gridThomsenClosure_of_additiveRep`.  Confirms the G1.b target hides
nothing false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridThomsenClosure_necessary
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) :
    GridThomsenClosure P j k t G :=
  gridThomsenClosure_of_additiveRep R hjk hjt hkt G

/-- **Soundness gate (PROVED): `TBlockWeakIndependent` is necessary under a rep.**

Re-export of the proved necessity (`OptionB_C1aBlockIndependence`).  So the level
move via `t`-block separability hides nothing false.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem tBlockWeakIndependent_necessary
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    TBlockWeakIndependent P j k t :=
  tBlockWeakIndependent_of_additiveRep R hjk hjt hkt

end ProductPref
end WakkerInfra

/-! ## G1.b audit

* §A: `gridDiagonalStepLevelMove_of_tBlockWeakIndependent` — the `st → c` level
  propagation from KLST `t`-block separability (the non-circular level move).
* §B: `gridDiagonalStep_of_calibration_and_tBlock`,
  `gridDiagonalStep_of_blockIndependence`, `gridThomsenClosure_of_blockIndependence`
  — the full diagonal step and the G1.b closure target from the three block
  conditions.
* §C: necessity gates (`gridDiagonalStep_necessary`, `gridThomsenClosure_necessary`,
  `tBlockWeakIndependent_necessary`).

**Honest scope.**  G1.a reduced the calibration to `{K,J}`-block separability; G1.b
propagates it to the full grid Thomsen closure through the *same* standard block
vocabulary (the level move is `TBlockWeakIndependent`, the closure is free order
theory).  So the §IV.5 grid Thomsen closure is fully reduced to Wakker's three KLST
block-independence conditions — each proved necessary, A1-non-derivable.  Discharging
those three from bare restricted solvability is the remaining G1 content. -/

#print axioms WakkerInfra.ProductPref.gridDiagonalStepLevelMove_of_tBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_of_calibration_and_tBlock
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_of_blockIndependence
#print axioms WakkerInfra.ProductPref.gridThomsenClosure_of_blockIndependence
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_necessary
#print axioms WakkerInfra.ProductPref.gridThomsenClosure_necessary
#print axioms WakkerInfra.ProductPref.tBlockWeakIndependent_necessary
