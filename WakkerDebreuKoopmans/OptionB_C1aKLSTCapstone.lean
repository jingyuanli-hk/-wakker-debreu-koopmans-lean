/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 capstone: `CrossPairCancellationData` from KLST block independence

This file closes the **structural reduction** of R1.1 (the §IV.5 cross-pair
cancellation crux) of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`: the entire
`CrossPairCancellationData = KzTransfer ∧ StripTransfer` is derived from the three
standard Krantz–Luce–Suppes–Tversky **block-independence** conditions, each proved
necessary under a representation.

## The reduction (assembled from the prior forward steps)

* `StripTransfer` ⟸ `TBlockWeakIndependent`        (`t`-block independence;
  `OptionB_C1aBlockIndependence.stripTransfer_of_tBlockWeakIndependent`);
* `KzTransfer` ⟸ `KBlockWeakIndependent` + `JBlockWeakIndependent`
  (`k`- and `j`-block independence;
  `OptionB_C1aKzAnchor.kzTransfer_of_kBlock_and_jBlock`).

So `CrossPairCancellationData` follows from the three block conditions
`{ TBlockWeakIndependent, KBlockWeakIndependent, JBlockWeakIndependent }`.

## What this file delivers (machine-checked, sound)

* `crossPairCancellationData_of_blockIndependence` — the **capstone**:
  `CrossPairCancellationData P j k t` from the three block-independence conditions.
* `crossPairCancellationData_of_additiveRep_via_blocks` — a sanity capstone: under
  a representation the three block conditions hold (each necessity already proved),
  so `CrossPairCancellationData` follows through this route too — confirming the
  block conditions are exactly the right strength.
* `doubleCancellation_of_blockIndependence_and_J2` — composing with
  `OptionB_C1aCrossPairFrontier.doubleCancellation_of_J2_and_crossPair`: the
  hexagon `DoubleCancellation` from a J2 supplier + the three block conditions.

## Net effect on R1.1 (honest)

R1.1's cross-pair residual is now **fully reduced to Wakker's coordinate-
independence input set** — KLST separability of every coordinate block (`j`, `k`,
`t`) from the others — with no remaining ad-hoc "transfer" or "anchor" residual,
and every block condition proved necessary.  This is the standard structural
hypothesis of the Wakker/KLST additive-representation theorems.

The genuinely-remaining §IV.5 content is now precisely: **derive the three block-
independence conditions from the bare structural axioms** (weak order + restricted
solvability + Archimedean + essentiality + connectedness/continuity, with the
single-coordinate A1 already a structural field).  The probes
(`OptionB_C1aHexagonProbe`, `OptionB_C1aStripProbe`, `OptionB_C1aKzProbe`) show the
*single-coordinate* A1 does not suffice — the block conditions are the genuine
`n ≥ 3` Thomsen content — so this is the real Wakker §IV.5 frontier, now stated in
exactly the standard separability vocabulary.

This file imports the Kz anchor, the block-independence file, and the cross-pair
frontier, and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aKzAnchor
import WakkerDebreuKoopmans.OptionB_C1aBlockIndependence
import WakkerDebreuKoopmans.OptionB_C1aCrossPairFrontier

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open WakkerDebreuKoopmans

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-- **R1.1 capstone: `CrossPairCancellationData` from the three KLST block-
independence conditions.**

`CrossPairCancellationData P j k t` (= `KzTransfer ∧ StripTransfer`) follows from:
* `TBlockWeakIndependent P j k t` (`t`-block) ⟹ `StripTransfer`;
* `KBlockWeakIndependent P j k t` (`k`-block) + `JBlockWeakIndependent P j k t`
  (`j`-block) ⟹ `KzTransfer`.

So the §IV.5 cross-pair residual is exactly Wakker's coordinate-independence input
set (KLST separability of every coordinate block).  Audit `[propext, Quot.sound]`. -/
theorem crossPairCancellationData_of_blockIndependence
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hTB : TBlockWeakIndependent P j k t)
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t) :
    CrossPairCancellationData P j k t :=
  { kz := kzTransfer_of_kBlock_and_jBlock hKB hJB
    strip := stripTransfer_of_tBlockWeakIndependent hTB }

/-- **Sanity capstone: the cross-pair data via the block conditions under a
representation.**

Under an additive representation, all three block-independence conditions hold
(each necessity already proved: `tBlockWeakIndependent_of_additiveRep`,
`kBlockWeakIndependent_of_additiveRep`, `jBlockWeakIndependent_of_additiveRep`), so
`CrossPairCancellationData` follows through the block route.  This confirms the
block conditions are exactly the right strength (sufficient for the residual, and
no stronger than what a representation supplies).  Audit foundational-only. -/
theorem crossPairCancellationData_of_additiveRep_via_blocks
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    CrossPairCancellationData P j k t :=
  crossPairCancellationData_of_blockIndependence
    (tBlockWeakIndependent_of_additiveRep R hjk hjt hkt)
    (kBlockWeakIndependent_of_additiveRep R hjk hjt hkt)
    (jBlockWeakIndependent_of_additiveRep R hjk hjt hkt)

/-- **Hexagon from a J2 supplier + the three block-independence conditions.**

Composes `crossPairCancellationData_of_blockIndependence` with
`doubleCancellation_of_J2_and_crossPair`
(`OptionB_C1aCrossPairFrontier.lean`): the hexagon `DoubleCancellation P j k`
(distinct `j,k,t`) from a J2 transfer-level supplier (escape-grid-dischargeable)
and the three KLST block-independence conditions.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem doubleCancellation_of_blockIndependence_and_J2
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjt : j ≠ t) (hkt : k ≠ t)
    (hJ2 : ∀ (a : Profile X) (x y : X j) (r : X k),
      ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t)))
    (hTB : TBlockWeakIndependent P j k t)
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t) :
    DoubleCancellation P j k :=
  doubleCancellation_of_J2_and_crossPair hjt hkt hJ2
    (crossPairCancellationData_of_blockIndependence hTB hKB hJB)

end ProductPref
end WakkerInfra

/-! ## R1.1 KLST capstone audit -/

#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_blockIndependence
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_additiveRep_via_blocks
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_blockIndependence_and_J2
