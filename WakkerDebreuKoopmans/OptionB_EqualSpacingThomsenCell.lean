/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — G1.a: the Thomsen cell, calibration from KLST block separability

> **STATUS: `sorry`-free forward brick on the §IV.5 grid construction (G1.a).**
> Not in the umbrella import.

This file executes the first sound, non-circular brick of G1.a of
`OptionB_SectionIV5GridConstructionRoadmap.md`: the off-axis grid calibration
`CalibrationAllBackgrounds` (the §IV.5 content the grid Thomsen step needs) from the
standard **KLST block separability** conditions, which are the genuine structural
input the construction is allowed to consume.

## Why this is the *non-circular* route (vs. the §D.2b circular one)

`OptionB_C1aGridThomsen.calibrationAllBackgrounds_of_diagonalResidues` derives the
calibration from the *diagonal residues* `{K,J,T}`-diag — which is **circular** for
R1.1 (those are permutation-equivalent to the target `TBlockDiagonalResidue`, §D.2b /
hard-constraint 4).

This file derives it instead from the **block separability conditions**
`KBlockWeakIndependent` / `JBlockWeakIndependent` — the *full* KLST separability of
each coordinate block, which is Wakker's standard structural input (not the diagonal
residue, not A1).  The off-axis cell is literally an on-axis `spaced_j`/`spaced_k`
indifference with the common third-coordinate value shifted — exactly what block
separability transports.  Under a representation the shift cancels (the off-axis
`V`-term is common to both sides), so this is sound; it is **not** the circular
diagonal-residue route.

## What this file delivers (all machine-checked, no `sorry`)

* `calJ_of_kBlockWeakIndependent` — the off-axis `j`-calibration cell `calJ m n` from
  `KBlockWeakIndependent` + `spaced_j m` (shift the common `k`-value `αₖ 0 → αₖ n`).
* `calK_of_jBlockWeakIndependent` — dually, `calK m n` from `JBlockWeakIndependent` +
  `spaced_k n`.
* `calibrationAllBackgrounds_of_blockIndependence` — **the G1.a calibration**:
  `CalibrationAllBackgrounds` from `{K,J}`-block separability + the calibrated grid.
* `gridThomsenClosure_of_blockIndependence` — composing with the existing free
  diagonal-step + closure machinery: the grid Thomsen closure from the block
  conditions (the G1 target in calibration form).
* soundness gates (`calJ`/`calK` necessary under a rep).

## Honest scope

This discharges the *calibration* half of the Thomsen cell from KLST block
separability — sound and non-circular.  The block conditions themselves remain the
genuine §IV.5 input (proved necessary, not A1-derivable — `OptionB_C1aKLSTCapstone`,
the probes); discharging *them* from bare solvability is the remaining G1 content.
This brick connects the calibration to the standard separability vocabulary, so G1's
open content is exactly the block conditions (not a bespoke calibration residual).

Imports `OptionB_C1aGridThomsen` (grid + calibration), `OptionB_C1aKzAnchor`
(`KBlockWeakIndependent`), `OptionB_C1aKzReduction` (`JBlockWeakIndependent`).  Not in
the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aGridThomsen
import WakkerDebreuKoopmans.OptionB_C1aKzAnchor
import WakkerDebreuKoopmans.OptionB_C1aKzReduction

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

/-! ## §A.  The off-axis calibration cells from block separability

`spaced_j m` is the `j`-step calibration at the base `k`-background `αₖ 0`:
`[αⱼ m | αₖ 0 | rt] ∼ [αⱼ (m+1) | αₖ 0 | st]`.  The off-axis cell `calJ m n` is the
same `{j,t}`-difference indifference at `k`-background `αₖ n`.  Shifting the common
`k`-value `αₖ 0 → αₖ n` is exactly `KBlockWeakIndependent` (the `{j,t}`-difference's
`≽`-order is independent of the common `k`-value), applied in both directions to turn
the indifference at `αₖ 0` into the indifference at `αₖ n`. -/

/-- **Off-axis `j`-calibration cell from `k`-block separability (PROVED).**

`calJ m n : [αⱼ m | αₖ n | rt] ∼ [αⱼ (m+1) | αₖ n | st]` from `spaced_j m` (the cell
at `αₖ 0`) by shifting the common `k`-value `αₖ 0 → αₖ n` via `KBlockWeakIndependent`
(both `≽`-directions).  Audit `[propext, Quot.sound]`. -/
theorem calJ_of_kBlockWeakIndependent
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hKB : KBlockWeakIndependent P j k t) (m n : ℕ) :
    P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
             (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st) :=
  ⟨hKB G.a (G.αj m) (G.αj (m + 1)) (G.αk 0) (G.αk n) G.rt G.st (G.spaced_j m).1,
   hKB G.a (G.αj (m + 1)) (G.αj m) (G.αk 0) (G.αk n) G.st G.rt (G.spaced_j m).2⟩

/-- **Off-axis `k`-calibration cell from `j`-block separability (PROVED).**

`calK m n : [αⱼ m | αₖ n | rt] ∼ [αⱼ m | αₖ (n+1) | st]` from `spaced_k n` (the cell
at `αⱼ 0`) by shifting the common `j`-value `αⱼ 0 → αⱼ m` via `JBlockWeakIndependent`
(both `≽`-directions).  Audit `[propext, Quot.sound]`. -/
theorem calK_of_jBlockWeakIndependent
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hJB : JBlockWeakIndependent P j k t) (m n : ℕ) :
    P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st) :=
  ⟨hJB G.a (G.αj 0) (G.αj m) (G.αk n) (G.αk (n + 1)) G.rt G.st (G.spaced_k n).1,
   hJB G.a (G.αj 0) (G.αj m) (G.αk (n + 1)) (G.αk n) G.st G.rt (G.spaced_k n).2⟩

/-! ## §B.  All-background calibration from block separability -/

/-- **G1.a calibration: `CalibrationAllBackgrounds` from `{K,J}`-block separability
(PROVED).**

Both calibration fields follow from the block separability conditions applied to the
on-axis `spaced_j` / `spaced_k` data.  This is the **non-circular** route to the
calibration (vs. the §D.2b-circular diagonal-residue route): the block conditions are
the standard KLST separability input, not the permutation-equivalent diagonal
residues.  Audit `[propext, Quot.sound]`. -/
theorem calibrationAllBackgrounds_of_blockIndependence
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t) :
    CalibrationAllBackgrounds P j k t G :=
  { calJ := fun m n => calJ_of_kBlockWeakIndependent G hKB m n
    calK := fun m n => calK_of_jBlockWeakIndependent G hJB m n }

/-! ## §C.  Soundness gates: the calibration cells are necessary under a rep -/

/-- **Soundness gate (PROVED): `KBlockWeakIndependent` is necessary under a rep.**

Re-export of the proved necessity (`OptionB_C1aKzAnchor`).  So the `j`-calibration
route via `k`-block separability hides nothing false.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem kBlockWeakIndependent_necessary
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    KBlockWeakIndependent P j k t :=
  kBlockWeakIndependent_of_additiveRep R hjk hjt hkt

/-- **Soundness gate (PROVED): `JBlockWeakIndependent` is necessary under a rep.**

Re-export of the proved necessity (`OptionB_C1aKzReduction`).  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem jBlockWeakIndependent_necessary
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    JBlockWeakIndependent P j k t :=
  jBlockWeakIndependent_of_additiveRep R hjk hjt hkt

end ProductPref
end WakkerInfra

/-! ## G1.a audit

* §A: `calJ_of_kBlockWeakIndependent`, `calK_of_jBlockWeakIndependent` — the off-axis
  calibration cells from KLST block separability (the non-circular route).
* §B: `calibrationAllBackgrounds_of_blockIndependence` — the G1.a calibration content.
* §C: the block conditions are necessary under a rep (soundness gates).

**Honest scope.**  This discharges the *calibration* half of the Thomsen cell from the
standard KLST block separability — sound and non-circular (it uses the block
conditions, not the §D.2b-circular diagonal residues).  The block conditions remain
the genuine §IV.5 input (proved necessary, A1-non-derivable); discharging them from
bare solvability is the remaining G1 content.  This connects the calibration to the
standard separability vocabulary, so G1's open content is exactly the block
conditions. -/

#print axioms WakkerInfra.ProductPref.calJ_of_kBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.calK_of_jBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.calibrationAllBackgrounds_of_blockIndependence
#print axioms WakkerInfra.ProductPref.kBlockWeakIndependent_necessary
#print axioms WakkerInfra.ProductPref.jBlockWeakIndependent_necessary
