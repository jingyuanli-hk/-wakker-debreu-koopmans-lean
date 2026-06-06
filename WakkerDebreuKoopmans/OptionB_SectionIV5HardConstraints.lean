/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — §IV.5 roadmap §0: the five hard constraints, machine-checked in one place

> **STATUS: `sorry`-free verification surface.**  Not in the umbrella import.

This file *executes* §0 ("Hard constraints") of
`OptionB_SectionIV5GridConstructionRoadmap.md`: it imports the five
machine-checked findings the roadmap depends on, re-states each as a named
`theorem` (so the constraint is a checked fact in this file, not just a cross-
reference), and `#print axioms` each to confirm the clean audit profile.

Any future §IV.5 construction attempt that contradicts one of these is unsound;
gathering them here gives a single `lake build` that re-verifies the design
constraints before work begins.

## The five constraints

1. **A1 ⇏ the hexagon** — single-coordinate independence does not imply
   `DoubleCancellation` (the residual is genuine cross-pair content).
2. **The matching kernel ⟸ KLST `t`-block separability** — the equal-spacing
   matching is the indifference shadow of `KBlockWeakIndependent` (no weaker target).
3. **The 1-D second-sequence reformulation is circular** — `SecondSequenceData`
   existence is equivalent to the shifted calibration it was meant to reduce.
4. **The 3-coordinate layer transport relocates, not discharges** — the aligned
   ruler's `diagAtC'` field already *is* the off-cal level move.
5. **Archimedean + solvability + tradeoff are insufficient for a dense grid** — a
   single strict standard sequence is an arithmetic progression (not dense); density
   needs a refinement-mesh family.

This file imports the five source modules and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aHexagonProbe
import WakkerDebreuKoopmans.OptionB_EqualSpacingProbe
import WakkerDebreuKoopmans.OptionB_EqualSpacingSecondSequence
import WakkerDebreuKoopmans.OptionB_EqualSpacingLayerTransport
import WakkerDebreuKoopmans.M2Frontier

set_option autoImplicit false
set_option linter.unusedVariables false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBSectionIV5HardConstraints

open WakkerInfra
open WakkerInfra.ProductPref

/-! ## Constraint 1 — A1 does not imply the hexagon -/

/-- **Constraint 1 (re-export).**  There is an `n = 3` weak order satisfying
single-coordinate independence (A1) on every coordinate yet violating
`DoubleCancellation` — so the hexagon residual is genuine cross-pair content, not an
A1 consequence. -/
theorem constraint1_a1_does_not_imply_hexagon :
    (∃ (Y : Fin 3 → Type) (Q : ProductPref Y),
      ProductPref.IsWeakOrder Q ∧
      (∀ i, CoordinateOrderIndependent Q i) ∧
      ¬ DoubleCancellation Q 0 1) :=
  OptionBC1aHexagonProbe.a1_does_not_imply_doubleCancellation

/-! ## Constraint 2 — the matching kernel ⟸ KLST `t`-block separability -/

/-- **Constraint 2 (re-export).**  The equal-spacing matching kernel
`CompensationMatch` follows from the KLST `k`-block separability
`KBlockWeakIndependent` — i.e. it is no weaker than the standard separability
condition (no weaker forward target exists). -/
theorem constraint2_matchingKernel_of_kBlockSeparability
    {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    {P : ProductPref X} [ProductPref.IsWeakOrder P] {j k t : ι}
    (hKB : KBlockWeakIndependent P j k t) :
    OptionBEqualSpacingProbe.CompensationMatch P j k t :=
  OptionBEqualSpacingProbe.compensationMatch_of_kBlockWeakIndependent hKB

/-! ## Constraint 3 — the 1-D second-sequence reformulation is circular -/

/-- **Constraint 3 (re-export).**  The shifted-background second-sequence interface
`SecondSequenceData` exists **iff** the shifted calibration it was meant to reduce
holds — i.e. the 1-D reformulation is logically equivalent to its target, not a
reduction.  The genuine escape must be the 2-D Thomsen configuration. -/
theorem constraint3_secondSequence_is_circular
    {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    {P : ProductPref X} [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (n : ℕ) :
    (Nonempty (SecondSequenceData P j k t G n)) ↔
      (∀ m, ShiftedCalibration P j k t G m n) :=
  secondSequenceData_iff_shiftedCalibration G n

/-! ## Constraint 4 — the 3-coordinate layer transport relocates, not discharges -/

/-- **Constraint 4 (re-export).**  The aligned-ruler layer transport derives the
layer-`(m+1)` diagonal from the bundle's `diagAtC'` field (the diagonal at the fresh
`t`-level `c'`) — i.e. the bundle already contains an off-cal diagonal step, so the
`t`-stick *relocates* the residual onto the stick rather than discharging it. -/
theorem constraint4_layerTransport_relocates
    {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    {P : ProductPref X} [ProductPref.IsWeakOrder P] {j k t : ι}
    (base : Profile X) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) (m : ℕ)
    (R : AlignedRulerTransport P base j k t vⱼ vₖ m) (n : ℕ) :
    P.indiff (tri base j k t (vⱼ (n + 1)) (vₖ (m + 1)) (base t))
             (tri base j k t (vⱼ n) (vₖ (m + 2)) (base t)) :=
  layerStep_of_alignedRuler base vⱼ vₖ m R n

/-! ## Constraint 5 — Archimedean + solvability + tradeoff ⇏ a dense grid -/

/-- **Constraint 5 (re-export).**  The additive-real `Bool` model satisfies weak
order, restricted solvability, tradeoff consistency, and the Archimedean axiom, yet
admits no selected refined dense grid (on either coordinate) — a single strict
standard sequence is an arithmetic progression (not dense).  So density genuinely
requires a refinement-mesh family, not one sequence.  Bound as a direct alias of the
source theorem (type inferred) so the conclusion matches exactly. -/
theorem constraint5_archimedean_insufficient_for_denseGrid :
    (∀ j : Bool, ProductPref.Archimedean WakkerRoadmap.CertificateChecklist.additiveRealBoolPref j) ∧
    ProductPref.RestrictedSolvability WakkerRoadmap.CertificateChecklist.additiveRealBoolPref ∧
    ProductPref.IsWeakOrder WakkerRoadmap.CertificateChecklist.additiveRealBoolPref ∧
    ProductPref.TradeoffConsistency WakkerRoadmap.CertificateChecklist.additiveRealBoolPref ∧
    ¬ WakkerRoadmap.CertificateChecklist.SelectedRefinedDenseGridCertificate
        WakkerRoadmap.CertificateChecklist.additiveRealBoolPref true ∧
    ¬ WakkerRoadmap.CertificateChecklist.SelectedRefinedDenseGridCertificate
        WakkerRoadmap.CertificateChecklist.additiveRealBoolPref false :=
  WakkerRoadmap.CertificateChecklist.additiveRealBool_archimedean_tradeoff_solvability_insufficient_for_selectedRefinedDenseGrid

end OptionBSectionIV5HardConstraints
end CertificateChecklist
end WakkerRoadmap

/-! ## §0 hard-constraints audit

All five constraints re-verified here as named theorems.  Each should expose only
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`,
no project axioms — confirming the §IV.5 roadmap's design constraints are
machine-checked facts. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBSectionIV5HardConstraints.constraint1_a1_does_not_imply_hexagon
#print axioms WakkerRoadmap.CertificateChecklist.OptionBSectionIV5HardConstraints.constraint2_matchingKernel_of_kBlockSeparability
#print axioms WakkerRoadmap.CertificateChecklist.OptionBSectionIV5HardConstraints.constraint3_secondSequence_is_circular
#print axioms WakkerRoadmap.CertificateChecklist.OptionBSectionIV5HardConstraints.constraint4_layerTransport_relocates
#print axioms WakkerRoadmap.CertificateChecklist.OptionBSectionIV5HardConstraints.constraint5_archimedean_insufficient_for_denseGrid
