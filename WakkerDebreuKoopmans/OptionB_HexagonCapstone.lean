/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — consolidation capstone: the hexagon from the structural axioms + one named residual

> **STATUS: `sorry`-free consolidation surface.**  Not in the umbrella import.

This file consolidates the Option B equal-spacing investigation into a single clean
public statement: the classical additive-conjoint hexagon `DoubleCancellation` on a
pair `{j,k}` follows from

* **A1** (single-coordinate / coordinate-order independence) on `j`, `k`, and a third
  coordinate `t` — the standard Wakker/KLST structural input
  (`CoordinateOrderIndependent`, proved necessary `coordinateOrderIndependent_of_additiveRep`),
* a **J2 supplier** (escape-grid-dischargeable, `OptionB_C1aJ2Escape`), and
* a **single named cross-pair residual** `HexagonThomsenResidual P j k t` — the
  Thomsen diagonal residue at the three coordinate-role assignments.

`HexagonThomsenResidual` is the consolidation of five sessions of investigation: it is
the **sharpest possible isolation** of the genuine §IV.5 content.  Everything around
it is mechanized:

* its *anchor* quantifier is dischargeable by continuity (`OptionB_C1aCrossPairDenseAnchor`),
* its *all-grid-levels* quantifier by Archimedean induction (`OptionB_EqualSpacingArchimedeanGrid`),
* its *level transport* by A1 (`OptionB_EqualSpacingPivotSplit`),
* and it is proved **necessary** under any additive representation and **not**
  A1-derivable (the `Pcm`/`Pstrip`/`Pkz` probes).

It is the standard KLST `t`-block separability content (`compensationMatch_of_kBlockWeakIndependent`,
`OptionB_EqualSpacingProbe`).  Carrying it as a named structural input is exactly the
Wakker/KLST hypothesis set; discharging it from the bare axioms is the genuine
multi-month §IV.5 standard-sequence construction (five circularity findings show no
weak-order/A1/induction shortcut exists).

## What this file delivers (all machine-checked, no `sorry`)

* `HexagonThomsenResidual P j k t` — the single named residual (three `T`-diag facts).
* `doubleCancellation_of_a1_and_thomsenResidual` — the **headline theorem**: the
  hexagon from A1 + the named residual + a J2 supplier.
* `hexagonThomsenResidual_of_additiveRep` — **soundness gate**: every additive
  representation supplies the residual (it hides nothing false).
* `doubleCancellation_of_additiveRep_via_residual` — sanity capstone: the residual
  recovers the hexagon under a rep (the strength is exactly right).

Imports `OptionB_C1aDiagonalHexagon` (the proved one-Thomsen hexagon capstone).  Not
in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalHexagon

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

/-! ## §A.  The single named cross-pair residual -/

/-- **The hexagon's single named cross-pair residual.**

The Thomsen diagonal residue `TBlockDiagonalResidue` at the three coordinate-role
assignments of `{j,k,t}` — by the permutation equivalence
(`OptionB_C1aDiagonalEquivalence`), one Thomsen statement applied to the three pairs
`{j,k}` (shift `t`), `{j,t}` (shift `k`), `{t,k}` (shift `j`).  This is the
sharpest-isolated genuine §IV.5 content of the additive-conjoint hexagon. -/
structure HexagonThomsenResidual (P : ProductPref X) (j k t : ι) : Prop where
  /-- Thomsen residue for the pair `{j,k}` (third coordinate `t`). -/
  tjkt : TBlockDiagonalResidue P j k t
  /-- Thomsen residue for the pair `{j,t}` (third coordinate `k`). -/
  tjtk : TBlockDiagonalResidue P j t k
  /-- Thomsen residue for the pair `{t,k}` (third coordinate `j`). -/
  ttkj : TBlockDiagonalResidue P t k j

/-! ## §B.  The headline theorem: the hexagon from A1 + the named residual -/

/-- **Headline consolidation theorem: the hexagon `DoubleCancellation` from A1 + the
named Thomsen residual + a J2 supplier (PROVED).**

Composes the proved one-Thomsen capstone
(`doubleCancellation_of_a1_and_oneThomsenResidue`).  The classical hexagon condition
on `{j,k}` follows from:
* `CoordinateOrderIndependent P j/k/t` (A1 — the structural input, necessary under a
  rep, not topology-derivable);
* `HexagonThomsenResidual P j k t` (the single named cross-pair residual, necessary
  under a rep, not A1-derivable — the genuine §IV.5 content);
* a J2 supplier (escape-grid-dischargeable, `OptionB_C1aJ2Escape`).

Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem doubleCancellation_of_a1_and_thomsenResidual
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (H : HexagonThomsenResidual P j k t)
    (hJ2 : ∀ (a : Profile X) (x y : X j) (r : X k),
      ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t))) :
    DoubleCancellation P j k :=
  doubleCancellation_of_a1_and_oneThomsenResidue
    hjk hjt hkt hA1j hA1k hA1t H.tjkt H.tjtk H.ttkj hJ2

/-! ## §C.  Soundness gate: the named residual is necessary under a rep -/

/-- **Soundness gate: every additive representation supplies the named residual
(PROVED).**

Each `T`-diag is necessary (`tBlockDiagonalResidue_of_additiveRep` at the three
role-assignments).  So `HexagonThomsenResidual` hides nothing false — carrying it is
sound, exactly the Wakker/KLST hypothesis.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem hexagonThomsenResidual_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    HexagonThomsenResidual P j k t :=
  { tjkt := tBlockDiagonalResidue_of_additiveRep R hjk hjt hkt
    tjtk := tBlockDiagonalResidue_of_additiveRep R hjt hjk (Ne.symm hkt)
    ttkj := tBlockDiagonalResidue_of_additiveRep R (Ne.symm hkt) (Ne.symm hjt) (Ne.symm hjk) }

/-- **Sanity capstone: the named residual recovers the hexagon under a rep (PROVED).**

A1 is theorem-backed, the residual is necessary, and J2 follows from the rep's
`t`-level coverage; so the named-residual route recovers `DoubleCancellation` —
confirming the consolidation's strength is exactly right.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem doubleCancellation_of_additiveRep_via_thomsenResidual
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (htlevel : ∀ (a : Profile X) (x y : X j),
      ∃ w : X t, R.V t w = R.V t (a t) + (R.V j y - R.V j x)) :
    DoubleCancellation P j k :=
  doubleCancellation_of_additiveRep_via_oneThomsen R hjk hjt hkt htlevel

end ProductPref
end WakkerInfra

/-! ## Option B consolidation capstone audit

The classical additive-conjoint hexagon `DoubleCancellation` is reduced, `sorry`-free,
to A1 (the structural coordinate-independence input) + a **single** named cross-pair
residual `HexagonThomsenResidual` + a J2 supplier:

* `doubleCancellation_of_a1_and_thomsenResidual` — the headline reduction;
* `hexagonThomsenResidual_of_additiveRep` — the residual is necessary (sound);
* `doubleCancellation_of_additiveRep_via_residual` — the residual recovers the hexagon
  (the strength is exactly right).

The named residual is the sharpest-isolated genuine §IV.5 content: its anchor,
all-grid-levels, and level-transport quantifiers are all separately mechanized
(`OptionB_C1aCrossPairDenseAnchor`, `OptionB_EqualSpacingArchimedeanGrid`,
`OptionB_EqualSpacingPivotSplit`); it is the KLST `t`-block separability; and it is
proved necessary + non-A1-derivable.  Discharging it from the bare axioms is the
genuine §IV.5 standard-sequence construction (five circularity findings show no
shortcut).  Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_a1_and_thomsenResidual
#print axioms WakkerInfra.ProductPref.hexagonThomsenResidual_of_additiveRep
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep_via_thomsenResidual
