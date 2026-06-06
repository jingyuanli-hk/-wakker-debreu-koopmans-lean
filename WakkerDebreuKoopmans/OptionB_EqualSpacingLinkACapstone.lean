/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — Link A capstone: the hexagon from the KLST block conditions (Link A done)

> **STATUS: `sorry`-free assembly brick realizing the "Link A done" node of the
> §IV.5 roadmap dependency graph.**
> Not in the umbrella import.

This file realizes the **"Link A done"** node of §6 of
`OptionB_SectionIV5GridConstructionRoadmap.md`: assemble the classical hexagon
`DoubleCancellation P j k` from the standard **KLST block-separability** conditions, the
structural A1 inputs, and the §IV.2.6 J2 escape grid — mirroring how
`OptionB_EqualSpacingSliceFamily` (G4.c) closed Link B.

## The assembly (using the G3 guard-drop finding)

G3 (`OptionB_EqualSpacingMeshDensity`) established that `TBlockDiagonalResidue P j k t`
is **definitionally** `TBlockWeakIndependent P j k t` with two disequality guards, so
the residue is free from the block condition (`tBlockDiagonalResidue_of_tBlockWeakIndependent`).
Applying this at the **three coordinate-role assignments** `(j,k,t)`, `(j,t,k)`,
`(t,k,j)` builds the named `HexagonThomsenResidual` directly from three block
conditions.  Then:

* `OptionB_HexagonCapstone.doubleCancellation_of_a1_and_thomsenResidual` reaches the
  hexagon from {A1 on `j,k,t` + `HexagonThomsenResidual` + a J2 supplier};
* `OptionB_C1aGridTransport.j2Supplier_of_escapeData` discharges the J2 supplier from
  the §IV.2.6 `J2EscapeData` escape grid (so J2 is not a bare hypothesis).

So `DoubleCancellation P j k` follows from {three KLST block conditions at the three
triples + A1 + the J2 escape grid} — the honest Link-A endpoint in the
block-separability vocabulary.

## What this file delivers (all machine-checked, no `sorry`)

* `hexagonThomsenResidual_of_blockIndependence` — `HexagonThomsenResidual` from the
  three KLST `t`-block conditions at the three coordinate-role assignments (the
  guard-drop at three triples).
* `doubleCancellation_of_blockIndependence_and_escapeJ2` — **the Link-A endpoint**:
  `DoubleCancellation P j k` from {three block conditions + A1 + J2 escape grid}.
* `doubleCancellation_of_blockIndependence_and_J2supplier` — the variant taking a bare
  J2 supplier (for routes that supply J2 directly).
* `hexagonThomsenResidual_of_additiveRep` (re-export) and
  `blockIndependence_necessary` — soundness gates: a representation supplies the three
  block conditions, hence the residual and the hexagon.

## Honest scope

This is pure assembly — no new §IV.5 content.  The genuine open input is the three KLST
block-separability conditions from bare restricted solvability (the G1 crux, proved
necessary and A1-non-derivable by the probes); the J2 escape grid is the standard
§IV.2.6 Archimedean density content (proved a non-independent residual,
`OptionB_C1aJ2Escape`); A1 is the structural coordinate-independence input.  With both
Link A (this) and Link B (`OptionB_EqualSpacingSliceFamily`) assembled, the §IV.5
construction is closed end-to-end modulo exactly that single block-separability crux.

Imports `OptionB_EqualSpacingMeshDensity` (the guard-drop), `OptionB_HexagonCapstone`
(`HexagonThomsenResidual`, the A1+residual→hexagon capstone),
`OptionB_C1aGridTransport` (`J2EscapeData`, the J2 supplier),
`OptionB_C1aBlockIndependence` (`TBlockWeakIndependent`).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_EqualSpacingMeshDensity
import WakkerDebreuKoopmans.OptionB_HexagonCapstone
import WakkerDebreuKoopmans.OptionB_C1aGridTransport
import WakkerDebreuKoopmans.OptionB_C1aBlockIndependence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open WakkerInfra
open WakkerDebreuKoopmans
open Function

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-! ## §A.  The named residual from the three KLST block conditions -/

/-- **`HexagonThomsenResidual` from the three KLST `t`-block conditions (PROVED).**

Applies the G3 guard-drop `tBlockDiagonalResidue_of_tBlockWeakIndependent` at the three
coordinate-role assignments `(j,k,t)`, `(j,t,k)`, `(t,k,j)`: each KLST `t`-block
separability condition yields the corresponding Thomsen diagonal residue, and the three
package into `HexagonThomsenResidual`.  This is the **non-circular** route to the named
residual — it consumes the standard KLST block-separability vocabulary (proved
necessary, A1-non-derivable), not the §D.2b-circular diagonal residues.  Audit
`[propext, Quot.sound]`. -/
theorem hexagonThomsenResidual_of_blockIndependence
    {j k t : ι}
    (hTjkt : TBlockWeakIndependent P j k t)
    (hTjtk : TBlockWeakIndependent P j t k)
    (hTtkj : TBlockWeakIndependent P t k j) :
    HexagonThomsenResidual P j k t :=
  { tjkt := tBlockDiagonalResidue_of_tBlockWeakIndependent hTjkt
    tjtk := tBlockDiagonalResidue_of_tBlockWeakIndependent hTjtk
    ttkj := tBlockDiagonalResidue_of_tBlockWeakIndependent hTtkj }

/-! ## §B.  The Link-A endpoint: the hexagon from the block conditions -/

/-- **Link-A endpoint (PROVED): the hexagon from the three KLST block conditions + A1 +
a J2 supplier.**

Composes `hexagonThomsenResidual_of_blockIndependence` (§A) with the consolidation
headline `doubleCancellation_of_a1_and_thomsenResidual`.  So `DoubleCancellation P j k`
follows from {A1 on `j,k,t` + the three KLST `t`-block conditions at the three triples +
a J2 supplier}.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem doubleCancellation_of_blockIndependence_and_J2supplier
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (hTjkt : TBlockWeakIndependent P j k t)
    (hTjtk : TBlockWeakIndependent P j t k)
    (hTtkj : TBlockWeakIndependent P t k j)
    (hJ2 : ∀ (a : Profile X) (x y : X j) (r : X k),
      ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t))) :
    DoubleCancellation P j k :=
  doubleCancellation_of_a1_and_thomsenResidual hjk hjt hkt hA1j hA1k hA1t
    (hexagonThomsenResidual_of_blockIndependence hTjkt hTjtk hTtkj) hJ2

/-- **Link-A endpoint with J2 escape-discharged (PROVED): the hexagon from the three
KLST block conditions + A1 + the §IV.2.6 J2 escape grid.**

The fully-named-input form: J2 is no longer a bare hypothesis but is discharged from the
§IV.2.6 `J2EscapeData` escape grid via `j2Supplier_of_escapeData` (the same density
content the grid-route capstone uses).  So the classical hexagon on `{j,k}` follows from
exactly: A1 on `j,k,t`, the three KLST `t`-block separability conditions (the genuine
cross-pair crux, proved necessary / A1-non-derivable), and the J2 escape grid (standard
§IV.2.6 Archimedean density).  This is the honest **Link-A endpoint** in the
block-separability vocabulary, parallel to G4.c's Link-B endpoint.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem doubleCancellation_of_blockIndependence_and_escapeJ2
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    [ConnectedSpace (X t)]
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (hTjkt : TBlockWeakIndependent P j k t)
    (hTjtk : TBlockWeakIndependent P j t k)
    (hTtkj : TBlockWeakIndependent P t k j)
    (esc : J2EscapeData P j k t) :
    DoubleCancellation P j k :=
  doubleCancellation_of_blockIndependence_and_J2supplier hjk hjt hkt hA1j hA1k hA1t
    hTjkt hTjtk hTtkj (j2Supplier_of_escapeData esc)

/-! ## §C.  Soundness gates -/

/-- **Soundness gate (PROVED): a representation supplies the three KLST block conditions
at the three triples.**

Each is necessary under a rep (`tBlockWeakIndependent_of_additiveRep` at the three
role-assignments).  So the Link-A block-condition input hides nothing false.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem blockIndependence_necessary
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    TBlockWeakIndependent P j k t ∧ TBlockWeakIndependent P j t k ∧
      TBlockWeakIndependent P t k j :=
  ⟨tBlockWeakIndependent_of_additiveRep R hjk hjt hkt,
   tBlockWeakIndependent_of_additiveRep R hjt hjk (Ne.symm hkt),
   tBlockWeakIndependent_of_additiveRep R (Ne.symm hkt) (Ne.symm hjt) (Ne.symm hjk)⟩

/-- **Sanity capstone (PROVED): the block route recovers the hexagon under a rep.**

Under a representation with adequate `t`-coverage (the honest J2 solvability residual,
`htlevel`), A1 is theorem-backed, the three block conditions hold
(`blockIndependence_necessary`), and J2 follows from coverage — so the block route
recovers `DoubleCancellation`, confirming the Link-A assembly is exactly the right
strength.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem doubleCancellation_of_additiveRep_via_blockIndependence
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hJ2 : ∀ (a : Profile X) (x y : X j) (r : X k),
      ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t))) :
    DoubleCancellation P j k := by
  obtain ⟨hTjkt, hTjtk, hTtkj⟩ := blockIndependence_necessary R hjk hjt hkt
  exact doubleCancellation_of_blockIndependence_and_J2supplier hjk hjt hkt
    (coordinateOrderIndependent_of_additiveRep R j)
    (coordinateOrderIndependent_of_additiveRep R k)
    (coordinateOrderIndependent_of_additiveRep R t)
    hTjkt hTjtk hTtkj hJ2

end ProductPref
end WakkerInfra

/-! ## Link-A capstone audit

* §A: `hexagonThomsenResidual_of_blockIndependence` — the named residual from the three
  KLST `t`-block conditions (guard-drop at three triples).
* §B: `doubleCancellation_of_blockIndependence_and_J2supplier` (bare J2) /
  `doubleCancellation_of_blockIndependence_and_escapeJ2` (J2 escape-discharged) — **the
  Link-A endpoint**: `DoubleCancellation P j k` from {three block conditions + A1 + J2}.
* §C: `blockIndependence_necessary`, `doubleCancellation_of_additiveRep_via_blockIndependence`
  — soundness gates.

**Honest scope.**  Pure assembly (no new §IV.5 content): the genuine open input is the
three KLST block-separability conditions from bare restricted solvability (the G1 crux,
proved necessary / A1-non-derivable); J2 is the standard §IV.2.6 escape-grid content; A1
is the structural input.  Realizes the "Link A done" node parallel to G4.c's Link-B
endpoint, so the §IV.5 construction is closed end-to-end modulo exactly the single
block-separability crux. -/

#print axioms WakkerInfra.ProductPref.hexagonThomsenResidual_of_blockIndependence
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_blockIndependence_and_J2supplier
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_blockIndependence_and_escapeJ2
#print axioms WakkerInfra.ProductPref.blockIndependence_necessary
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep_via_blockIndependence
