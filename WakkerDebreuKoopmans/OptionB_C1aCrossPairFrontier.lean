/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-C1.a minimal frontier: the hexagon from the escape grid + a single
  named cross-pair cancellation residual

This file consolidates the WP-C1.a forward chain into its sharpest honest form.
After J2 transfer-level existence was discharged from the §IV.2.6 escape grid
(`OptionB_C1aJ2Escape.lean`), the only genuine remaining content of
`HexagonResidualData` is the **two cross-pair cancellation residuals**
`KzTransfer` and `StripTransfer` (both machine-checked non-A1-derivable in the
probes, both proved necessary under a representation).  This file bundles them
into a single named input and proves:

* the hexagon `DoubleCancellation` follows from {a J2 supplier + the cross-pair
  bundle} (sound reduction), and
* the cross-pair bundle is necessary under any additive representation.

## What this file delivers (all machine-checked)

* `CrossPairCancellationData P j k t` — the single named §IV.5 cross-pair
  cancellation residual = `KzTransfer ∧ StripTransfer`.
* `crossPairCancellationData_of_additiveRep` — **necessity**: every additive
  representation supplies both pieces (`kzTransfer_of_additiveRep`,
  `stripTransfer_of_additiveRep`).  So the bundle hides nothing false.
* `doubleCancellation_of_J2_and_crossPair` — the **sound reduction**: the hexagon
  from a J2-witness supplier + the cross-pair bundle (compose
  `thirdCoordinateTransfer_of_components` then
  `doubleCancellation_of_thirdCoordinateTransfer`).
* `hexagonResidualData_of_J2_and_crossPair` — repackages a J2 supplier + the
  bundle back into `HexagonResidualData` (showing the two presentations agree).
* `doubleCancellation_of_additiveRep_via_crossPair` — sanity capstone: the
  hexagon's own necessity factors through {J2 + cross-pair}, confirming the
  bundle is exactly the right strength.

## Honest WP-C1.a frontier (final form)

The hexagon reduces to: the §IV.2.6 escape grid (which supplies J2 via
`j2Exists_of_*`, and is proved necessary in `OptionB_EscapeGridNecessity.lean`)
plus the single named `CrossPairCancellationData` (proved necessary here).
Neither is A1-derivable; both are sound.  The full forward construction of
`CrossPairCancellationData` from restricted solvability is the genuine
multi-week Wakker §IV.5 frontier — pinned now to one named, necessary input.

This file imports `OptionB_C1aJ2Escape` and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aJ2Escape
import WakkerDebreuKoopmans.OptionB_C1aEndpoint

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

/-- **The single named §IV.5 cross-pair cancellation residual.**

After J2 transfer-level existence is discharged from the escape grid, this is the
*entire* genuine remaining content of the hexagon on the pair `{j,k}` with
measuring-stick coordinate `t`:

* `kz` — `KzTransfer P j k t` (the `{k,t}` tradeoff-transfer), and
* `strip` — `StripTransfer P j k t` (the `t`-block independence strip).

Both are machine-checked *not* A1-derivable (`a1_does_not_imply_stripTransfer`)
and proved necessary under a representation (`crossPairCancellationData_of_additiveRep`). -/
structure CrossPairCancellationData (P : ProductPref X) (j k t : ι) : Prop where
  /-- The `{k,t}` tradeoff-transfer residual. -/
  kz : KzTransfer P j k t
  /-- The `t`-block independence strip residual. -/
  strip : StripTransfer P j k t

/-- **Necessity of the cross-pair bundle (soundness witness).**

Every additive representation supplies both `KzTransfer` and `StripTransfer`
(`kzTransfer_of_additiveRep`, `stripTransfer_of_additiveRep`), so the bundle
hides nothing false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem crossPairCancellationData_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    CrossPairCancellationData P j k t :=
  ⟨kzTransfer_of_additiveRep R hjk hjt hkt,
   stripTransfer_of_additiveRep R hjk hjt hkt⟩

/-- **WP-C1.a minimal sound reduction: the hexagon from a J2 supplier + the
cross-pair bundle.**

`DoubleCancellation P j k` (distinct `j,k,t`) follows from a J2-witness supplier
(escape-grid-dischargeable, see `OptionB_C1aJ2Escape.lean`) and the single named
`CrossPairCancellationData`: assemble the third-coordinate transfer via
`thirdCoordinateTransfer_of_components`, then close the hexagon via
`doubleCancellation_of_thirdCoordinateTransfer`.  Audit foundational-only. -/
theorem doubleCancellation_of_J2_and_crossPair
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjt : j ≠ t) (hkt : k ≠ t)
    (hJ2 : ∀ (a : Profile X) (x y : X j) (r : X k),
      ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t)))
    (H : CrossPairCancellationData P j k t) :
    DoubleCancellation P j k :=
  doubleCancellation_of_thirdCoordinateTransfer hjt hkt
    (thirdCoordinateTransfer_of_components hJ2 H.kz H.strip)

/-- **A J2 supplier + the cross-pair bundle repackage as `HexagonResidualData`.**

Shows the consolidated {J2 + cross-pair} presentation agrees with the original
three-field `HexagonResidualData` (`OptionB_C1aEndpoint.lean`).  Audit
foundational-only. -/
theorem hexagonResidualData_of_J2_and_crossPair
    {j k t : ι}
    (hJ2 : ∀ (a : Profile X) (x y : X j) (r : X k),
      ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t)))
    (H : CrossPairCancellationData P j k t) :
    HexagonResidualData P j k t :=
  ⟨hJ2, H.kz, H.strip⟩

/-- **Sanity capstone: the hexagon's own necessity factors through {J2 +
cross-pair}.**

Under an additive representation `R` with adequate `t`-level coverage (`htlevel`,
the honest solvability residual that also supplies J2), the cross-pair bundle
holds (necessity), J2 holds (from `htlevel`), and the sound reduction recovers
`DoubleCancellation`.  Confirms the {J2 + cross-pair} frontier is exactly the
right strength.  Audit foundational-only. -/
theorem doubleCancellation_of_additiveRep_via_crossPair
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (htlevel : ∀ (a : Profile X) (x y : X j),
      ∃ w : X t, R.V t w = R.V t (a t) + (R.V j y - R.V j x)) :
    DoubleCancellation P j k := by
  -- The representation supplies the full `HexagonResidualData` (incl. J2).
  have H := hexagonResidualData_of_additiveRep R hjk hjt hkt htlevel
  exact doubleCancellation_of_J2_and_crossPair hjt hkt H.j2
    ⟨crossPairCancellationData_of_additiveRep R hjk hjt hkt |>.kz,
     crossPairCancellationData_of_additiveRep R hjk hjt hkt |>.strip⟩

end ProductPref
end WakkerInfra

/-! ## WP-C1.a minimal cross-pair frontier audit -/

#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_additiveRep
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_J2_and_crossPair
#print axioms WakkerInfra.ProductPref.hexagonResidualData_of_J2_and_crossPair
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep_via_crossPair
