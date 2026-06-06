/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: the classical hexagon from A1 + one Thomsen residue + a J2 supplier

This file proves the **classical-vocabulary endpoint** of the R1.1 reduction:
the standard additive-conjoint hexagon / Thomsen `DoubleCancellation P j k`
follows from
* single-coordinate independence A1 on each of `j`, `k`, `t`, **plus**
* a single Thomsen-type residue `TBlockDiagonalResidue` instantiated at the
  three permuted coordinate triples `(j,k,t)`, `(j,t,k)`, `(t,k,j)`, **plus**
* a J2 transfer-level supplier (the `{j,t}`-compensation existence, which the
  §IV.2.6 escape grid discharges — `OptionB_C1aJ2Escape.lean`).

This is the cleanest connection between R1.1's reduced open content (the single
Thomsen residue) and the *classical* additive-conjoint vocabulary
(`DoubleCancellation`, the hexagon condition).  It composes:
* `crossPairCancellationData_of_a1_and_oneThomsenResidue`
  (`OptionB_C1aDiagonalUnifiedCapstone.lean`) — A1 + one Thomsen ⟹ cross-pair
  data, with
* `doubleCancellation_of_J2_and_crossPair`
  (`OptionB_C1aCrossPairFrontier.lean`) — J2 + cross-pair data ⟹ hexagon.

## What this file delivers (machine-checked, sound)

* `doubleCancellation_of_a1_and_oneThomsenResidue` — the hexagon `DoubleCancellation
  P j k` from A1 on `{j,k,t}`, the single Thomsen residue at three triples, and a
  J2 supplier.
* `doubleCancellation_of_additiveRep_via_oneThomsen` — sanity capstone: under a
  representation with adequate `t`-coverage, A1 holds (theorem-backed), the three
  T-diags hold (necessity), and J2 holds (from coverage), so the hexagon follows
  — confirming the strength is exactly right.

This is the natural classical-vocabulary capstone for the unified one-Thomsen
reduction: the genuinely-open content of the *entire* hexagon is now exactly the
single Thomsen residue (the J2 supplier being escape-grid-dischargeable and A1 a
structural field).

This file imports the unified one-Thomsen capstone and the cross-pair frontier,
and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalUnifiedCapstone
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

/-- **R1.1 classical-vocabulary capstone: the hexagon `DoubleCancellation` from
A1 + one Thomsen residue at three coordinate triples + a J2 supplier.**

Composes the unified one-Thomsen cross-pair capstone with the cross-pair-to-hexagon
reduction.  So the entire classical hexagon condition on `{j,k}` follows from:
* `CoordinateOrderIndependent P j/k/t` (A1, the structural input);
* `TBlockDiagonalResidue P j k t`, `… P j t k`, `… P t k j` (the single Thomsen
  residue at the three role-assignments — R1.1's genuinely-open content);
* a J2 supplier (escape-grid-dischargeable, `OptionB_C1aJ2Escape.lean`).
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem doubleCancellation_of_a1_and_oneThomsenResidue
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (hTjkt : TBlockDiagonalResidue P j k t)
    (hTjtk : TBlockDiagonalResidue P j t k)
    (hTtkj : TBlockDiagonalResidue P t k j)
    (hJ2 : ∀ (a : Profile X) (x y : X j) (r : X k),
      ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t))) :
    DoubleCancellation P j k :=
  doubleCancellation_of_J2_and_crossPair hjt hkt hJ2
    (crossPairCancellationData_of_a1_and_oneThomsenResidue
      hjk hjt hkt hA1j hA1k hA1t hTjkt hTjtk hTtkj)

/-- **Sanity capstone: under a representation the one-Thomsen route recovers the
hexagon.**

A1 is theorem-backed (`coordinateOrderIndependent_of_additiveRep`), each `T-diag`
is necessary (`tBlockDiagonalResidue_of_additiveRep` at the three triples), and
J2 follows from the rep's `t`-level coverage (`htlevel`, the honest solvability
residual).  So the one-Thomsen route recovers `DoubleCancellation` — confirming
the strength is exactly right.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem doubleCancellation_of_additiveRep_via_oneThomsen
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (htlevel : ∀ (a : Profile X) (x y : X j),
      ∃ w : X t, R.V t w = R.V t (a t) + (R.V j y - R.V j x)) :
    DoubleCancellation P j k := by
  -- The representation supplies the full `HexagonResidualData` (incl. J2).
  have H := hexagonResidualData_of_additiveRep R hjk hjt hkt htlevel
  exact doubleCancellation_of_a1_and_oneThomsenResidue
    hjk hjt hkt
    (coordinateOrderIndependent_of_additiveRep R j)
    (coordinateOrderIndependent_of_additiveRep R k)
    (coordinateOrderIndependent_of_additiveRep R t)
    (tBlockDiagonalResidue_of_additiveRep R hjk hjt hkt)
    (tBlockDiagonalResidue_of_additiveRep R hjt hjk (Ne.symm hkt))
    (tBlockDiagonalResidue_of_additiveRep R (Ne.symm hkt) (Ne.symm hjt) (Ne.symm hjk))
    H.j2

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-hexagon audit -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_a1_and_oneThomsenResidue
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep_via_oneThomsen
