/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — G1.c: the end-to-end grid step (existence + closure)

> **STATUS: `sorry`-free forward brick on the §IV.5 grid construction (G1.c).**
> Not in the umbrella import.

This file executes **G1.c** of `OptionB_SectionIV5GridConstructionRoadmap.md`: the
**end-to-end grid step**.  G1.a reduced the calibration to KLST block separability;
G1.b propagated it to the full `GridThomsenClosure` on a *given* calibrated grid.
G1.c bundles that closure with the grid's **existence** from the structural axioms +
topology, producing the §IV.5 grid step as a single statement:

> from the structural axioms (`RestrictedSolvability`, A1-`t`, the
> `WakkerCoordinateTopology` bundle) + a strict seed exchange + the three KLST block
> conditions, **there exists** a calibrated `{j,k,t}` grid on which the full grid
> Thomsen closure holds (equal-index-sum indifference at every grid point and every
> `t`-level), with both grid sequences injective.

## What this file delivers (all machine-checked, no `sorry`)

* `gridStep_of_structuralAxioms_and_blockIndependence` — **the G1.c endpoint**: grid
  existence (`calibratedJKGrid_of_structuralAxioms_and_topology`) ∧ the G1.b closure
  (`gridThomsenClosure_of_blockIndependence`) on that grid.
* `gridDiagonalStepExists_of_structuralAxioms_and_blockIndependence` — the same with
  the diagonal-step primitive (the leaner consequence).
* `gridStep_of_structuralAxioms_via_additiveRep` — soundness gate: under a
  representation the block conditions hold (`*_of_additiveRep`), so the whole grid
  step is necessary; nothing false is hidden.

## Axiom note (the documented topology seams)

Unlike G1.a/G1.b (which audit at the foundational `[propext, ...]` set), G1.c invokes
the grid-existence theorem and therefore inherits the two **documented** §III.4.2
bracket-reach IVT seams
`coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology` (the standard
topology input every Option B existence theorem carries — see
`OptionB_C1aGridThomsen.lean` §E.4 and `OptionB_AxiomCheck.lean`).  This is the
expected, acceptable seam: it is *not* a `_from_raw_axioms` bypass and *not* a
`sorry`; it is the project-wide §III.4.2 topology interface.

## Honest scope

G1.c closes out work package G1 *modulo the block conditions*: it shows the §IV.5
grid step is a one-line composition of {grid existence from the axioms} + {closure
from the three KLST block conditions}.  The single remaining G1 obligation is
discharging `TBlockWeakIndependent` / `KBlockWeakIndependent` / `JBlockWeakIndependent`
from bare restricted solvability — the genuine `n ≥ 3` cancellation crux the five
impossibility findings pin (each is proved necessary and A1-non-derivable).  Once that
lands, `gridStep_of_structuralAxioms_and_blockIndependence` becomes the unconditional
§IV.5 grid step.

Imports `OptionB_EqualSpacingGridPropagate` (G1.b closure) and its transitive imports
(`OptionB_C1aGridThomsen` for grid existence).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_EqualSpacingGridPropagate

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

/-! ## §A.  The end-to-end grid step -/

/-- **G1.c endpoint: the §IV.5 grid step from the structural axioms + the three KLST
block conditions (PROVED, mod the documented §III.4.2 topology seams).**

Bundles grid **existence** with the G1.b **closure**:

* `calibratedJKGrid_of_structuralAxioms_and_topology` builds an injective calibrated
  `{j,k,t}` grid from `RestrictedSolvability` + A1-`t` + the `WakkerCoordinateTopology`
  bundle + a strict seed exchange `(j0,k0,rt) ≻ (j0,k0,st)`;
* `gridThomsenClosure_of_blockIndependence` (G1.b) closes the full Thomsen grid on
  *that* grid from the three KLST block-independence conditions `{T,K,J}`-block.

So the entire §IV.5 grid step is: there exists a calibrated grid (both sequences
injective) on which equal-index-sum indifference holds at every grid point and every
`t`-level.

Audit: `[propext, Classical.choice, Quot.sound]` **plus** the two documented §III.4.2
bracket-reach seams inherited from grid existence — the standard Option B topology
interface, not a `_from_raw_axioms` bypass and not a `sorry`. -/
theorem gridStep_of_structuralAxioms_and_blockIndependence
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hsolv : RestrictedSolvability P)
    (hA1t : CoordinateOrderIndependent P t)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (a : Profile X) (rt st : X t) (j0 : X j) (k0 : X k)
    (hrs : rt ≠ st)
    (hseed : P.strict (tri a j k t j0 k0 rt) (tri a j k t j0 k0 st))
    (hTB : TBlockWeakIndependent P j k t)
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t) :
    ∃ G : CalibratedJKGrid P j k t,
      (Function.Injective G.αj ∧ Function.Injective G.αk) ∧
      GridThomsenClosure P j k t G := by
  obtain ⟨G, hinj⟩ :=
    calibratedJKGrid_of_structuralAxioms_and_topology
      hjk hjt hkt hsolv hA1t htop a rt st j0 k0 hrs hseed
  exact ⟨G, hinj, gridThomsenClosure_of_blockIndependence G hTB hKB hJB⟩

/-- **G1.c, diagonal-step form (PROVED, mod the documented §III.4.2 topology seams).**

The same end-to-end statement with the diagonal-step primitive
`(αⱼ (m+1), αₖ n, c) ∼ (αⱼ m, αₖ (n+1), c)` (the leaner consequence underneath the
closure).  Audit as `gridStep_of_structuralAxioms_and_blockIndependence`. -/
theorem gridDiagonalStepExists_of_structuralAxioms_and_blockIndependence
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hsolv : RestrictedSolvability P)
    (hA1t : CoordinateOrderIndependent P t)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (a : Profile X) (rt st : X t) (j0 : X j) (k0 : X k)
    (hrs : rt ≠ st)
    (hseed : P.strict (tri a j k t j0 k0 rt) (tri a j k t j0 k0 st))
    (hTB : TBlockWeakIndependent P j k t)
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t) :
    ∃ G : CalibratedJKGrid P j k t,
      (Function.Injective G.αj ∧ Function.Injective G.αk) ∧
      GridDiagonalStep P j k t G := by
  obtain ⟨G, hinj⟩ :=
    calibratedJKGrid_of_structuralAxioms_and_topology
      hjk hjt hkt hsolv hA1t htop a rt st j0 k0 hrs hseed
  exact ⟨G, hinj, gridDiagonalStep_of_blockIndependence G hTB hKB hJB⟩

/-! ## §B.  Soundness gate -/

/-- **Soundness gate (PROVED): the grid step holds under a representation.**

Under an additive representation `R`, the three KLST block conditions all hold
(`tBlockWeakIndependent_of_additiveRep`, `kBlockWeakIndependent_of_additiveRep`,
`jBlockWeakIndependent_of_additiveRep`), so the G1.c grid step follows for free.  This
confirms the grid step hides nothing false: it is necessary for any preference with an
additive representation.  Audit as `gridStep_of_structuralAxioms_and_blockIndependence`
(it routes through the same existence theorem). -/
theorem gridStep_of_structuralAxioms_via_additiveRep
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    (R : AdditiveRep P)
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hsolv : RestrictedSolvability P)
    (hA1t : CoordinateOrderIndependent P t)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (a : Profile X) (rt st : X t) (j0 : X j) (k0 : X k)
    (hrs : rt ≠ st)
    (hseed : P.strict (tri a j k t j0 k0 rt) (tri a j k t j0 k0 st)) :
    ∃ G : CalibratedJKGrid P j k t,
      (Function.Injective G.αj ∧ Function.Injective G.αk) ∧
      GridThomsenClosure P j k t G :=
  gridStep_of_structuralAxioms_and_blockIndependence
    hjk hjt hkt hsolv hA1t htop a rt st j0 k0 hrs hseed
    (tBlockWeakIndependent_of_additiveRep R hjk hjt hkt)
    (kBlockWeakIndependent_of_additiveRep R hjk hjt hkt)
    (jBlockWeakIndependent_of_additiveRep R hjk hjt hkt)

end ProductPref
end WakkerInfra

/-! ## G1.c audit

* §A: `gridStep_of_structuralAxioms_and_blockIndependence` (closure form) and
  `gridDiagonalStepExists_of_structuralAxioms_and_blockIndependence` (diagonal-step
  form) — the end-to-end §IV.5 grid step: grid existence ∧ G1.b closure.
* §B: `gridStep_of_structuralAxioms_via_additiveRep` — soundness gate (the grid step
  is necessary under any representation).

**Axiom note.**  These inherit the two documented §III.4.2 bracket-reach seams
`coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology` from grid
existence — the standard Option B topology interface, not a `_from_raw_axioms` bypass
and not a `sorry`.  G1.a/G1.b remain foundational-only; G1.c is where the
already-carried topology existence seam enters.

**Honest scope.**  G1.c closes work package G1 *modulo the block conditions*: the
§IV.5 grid step is a one-line composition of grid existence + the G1.b closure.  The
single remaining G1 obligation is discharging the three KLST block conditions from
bare restricted solvability (the genuine `n ≥ 3` crux). -/

#print axioms WakkerInfra.ProductPref.gridStep_of_structuralAxioms_and_blockIndependence
#print axioms WakkerInfra.ProductPref.gridDiagonalStepExists_of_structuralAxioms_and_blockIndependence
#print axioms WakkerInfra.ProductPref.gridStep_of_structuralAxioms_via_additiveRep
