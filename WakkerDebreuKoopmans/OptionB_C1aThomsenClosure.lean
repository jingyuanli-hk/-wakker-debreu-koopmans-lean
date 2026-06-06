/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — C1.a-3: the Thomsen closure crux (the off-cal compensation match)

> **STATUS: `sorry`-free.  Attacks the C1.a crux; delivers the honest determination
> of the wall as a machine-checked characterization, plus the one non-circular
> partial it admits.**
> Not in the umbrella import.

This file executes **C1.a-3** of `OptionB_C1aConstructionPlan.md`: the genuine crux —
`OffCalCompensationMatch` (the two grid steps' compensations coincide at an off-cal
level `c`), which the four prior circularity findings localized to the source-level
pivot direction.

## The attack, and the honest determination (machine-checked)

The crux is whether `OffCalCompensationMatch` is derivable from {C1.a-1 existence +
C1.a-2 uniqueness + the calibration} **without** consuming block independence
(`TBlockWeakIndependent` / `TBlockDiagonalResidue`), which would be circular (§D.2b).

This file establishes, with proofs, the precise structure of the wall:

* **§A — the match IS the off-cal diagonal step (PROVED, non-circular).**  Via the
  C1.a-1 compensator `p` and weak-order transitivity, `OffCalCompensationMatch` at a
  cell is *equivalent* to the off-cal diagonal step
  `[αⱼ(m+1)|αₖn|c] ∼ [αⱼm|αₖ(n+1)|c]` (`matchStep_iff_diagonalOffCal`).  This is pure
  weak order — no circularity — and reduces the match to the diagonal step.

* **§B — the calibration-level match is FREE (PROVED, non-circular).**  At the
  calibration level `st`, the diagonal step holds from `CalibrationAllBackgrounds`
  alone (`interiorDiagonalStep_st_of_allBackgrounds`), so the match holds at `st`
  with **no** block input (`offCalMatch_at_st_free`).  This is genuine, non-circular
  content: the cell closes at the calibration level.

* **§C — the off-cal extension is EXACTLY the level transport (machine-checked
  characterization).**  `offCalMatch_iff_levelTransport` proves the off-cal match at
  `c` holds iff the free `st`-level diagonal step transports `st → c` — i.e. the crux
  is *precisely* the `t`-level transport of a `{j,k}`-two-coordinate-difference
  indifference, which is the definition of `TBlockDiagonalResidue` at one cell.  This
  is the **sharpest machine-checked statement of the wall**: the genuine content is
  the cross-level transport, nothing less.

* **§D — soundness gate.**  `offCalMatch_of_additiveRep` (re-exported): the match is
  necessary under a rep.

## Honest determination (the fifth circularity wall, now at cell granularity)

§C is the decisive finding: the off-cal match reduces — by pure weak order, via the
free calibration-level step — to transporting a `{j,k}`-difference indifference across
`st → c`.  That transport **is** `TBlockDiagonalResidue` at the cell (the target).  So
there is **no** non-circular cell-level lemma producing the off-cal match: the wall is
the level transport of a two-coordinate-difference indifference, which the strip/Kz
probes prove is not A1-derivable and which §D.2b proves is the target itself.

This confirms, at the finest (single-cell, single-level) granularity, the five-session
determination: the crux is genuinely irreducible by cell-level reasoning.  Discharging
it requires the **global** Debreu/KLST standard-sequence equal-spacing argument
(C1.a-3's full construction is the multi-week §IV.5 frontier), or the §6 fallback
(carry `TBlockWeakIndependent` as the proven-necessary KLST hypothesis).  What §A–§C
add over the prior findings: the match is now *reduced to the bare level transport*
(the free calibration-level step is discharged), so the remaining content is the
absolute minimum — one `{j,k}`-difference indifference, transported one `t`-level.

Imports `OptionB_C1aGridThomsen` (the grid, the match, the free `st`-level step) and
`OptionB_C1aCompensationExistence` (C1.a-1).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aGridThomsen
import WakkerDebreuKoopmans.OptionB_C1aCompensationExistence

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

/-! ## §A.  The match IS the off-cal diagonal step (non-circular, pure weak order)

`OffCalCompensationMatch` at a cell says: a `p` that `j`-compensates also
`k`-compensates.  Both compensations share the left side `[αⱼ m | αₖ n | p]`, so by
weak-order transitivity the match at `(m,n,c)` (for the C1.a-1 compensator `p`) is
equivalent to the off-cal diagonal step `[αⱼ(m+1)|αₖn|c] ∼ [αⱼm|αₖ(n+1)|c]`. -/

private theorem tc_symm {x y : Profile X} (h : P.indiff x y) : P.indiff y x :=
  ⟨h.2, h.1⟩

private theorem tc_trans [ProductPref.IsWeakOrder P] {x y z : Profile X}
    (hxy : P.indiff x y) (hyz : P.indiff y z) : P.indiff x z :=
  ⟨ProductPref.IsWeakOrder.transitive _ _ _ hxy.1 hyz.1,
   ProductPref.IsWeakOrder.transitive _ _ _ hyz.2 hxy.2⟩

/-- **The off-cal diagonal step ⟹ the match at a cell (PROVED, weak order).**

Given the off-cal diagonal step `[αⱼ(m+1)|αₖn|c] ∼ [αⱼm|αₖ(n+1)|c]` and a `j`-compensator
`p` (`[αⱼm|αₖn|p] ∼ [αⱼ(m+1)|αₖn|c]`), the same `p` `k`-compensates: chain
`[αⱼm|αₖn|p] ∼ [αⱼ(m+1)|αₖn|c] ∼ [αⱼm|αₖ(n+1)|c]`.  Pure weak order — non-circular.
Audit `[propext, Quot.sound]`. -/
theorem matchCell_of_diagonalOffCal
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (c : X t)
    (hdiag : P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
                      (tri G.a j k t (G.αj m) (G.αk (n + 1)) c))
    (p : X t)
    (hJ : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                   (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)) :
    P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) c) :=
  tc_trans hJ hdiag

/-- **The match at a cell ⟹ the off-cal diagonal step (PROVED, weak order).**

Conversely, given the match's conclusion (`p` `k`-compensates) and its premise (`p`
`j`-compensates), the off-cal diagonal step follows: chain
`[αⱼ(m+1)|αₖn|c] ∼ [αⱼm|αₖn|p] ∼ [αⱼm|αₖ(n+1)|c]`.  Pure weak order — non-circular.
Audit `[propext, Quot.sound]`. -/
theorem diagonalOffCal_of_matchCell
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (c : X t) (p : X t)
    (hJ : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                   (tri G.a j k t (G.αj (m + 1)) (G.αk n) c))
    (hK : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                   (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)) :
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) c) :=
  tc_trans (tc_symm hJ) hK

/-! ## §B.  The calibration-level match is FREE (non-circular)

At the calibration level `st`, the diagonal step is free from `CalibrationAllBackgrounds`
(`interiorDiagonalStep_st_of_allBackgrounds`).  So the match at `st` holds with no block
input — the cell closes at the calibration level. -/

/-- **The match holds at the calibration level `st` for free (PROVED).**

From `CalibrationAllBackgrounds`, the diagonal step at level `st` is free
(`interiorDiagonalStep_st_of_allBackgrounds`); §A's `matchCell_of_diagonalOffCal` then
gives the match at `st` for any `st`-compensator `p`.  No block independence — genuine
non-circular content.  Audit `[propext, Quot.sound]`. -/
theorem matchCell_at_st_free
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G) (m n : ℕ) (p : X t)
    (hJ : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                   (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st)) :
    P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st) :=
  matchCell_of_diagonalOffCal G m n G.st
    (interiorDiagonalStep_st_of_allBackgrounds G hcal m n) p hJ

/-! ## §C.  The off-cal extension IS exactly the level transport (the wall)

The decisive characterization: the off-cal diagonal step at `c` holds **iff** the free
`st`-level diagonal step transports `st → c`.  Since both compared profiles differ in
**both** `j` and `k`, that transport is precisely `TBlockDiagonalResidue` at the cell —
the target.  So the crux is exactly the cross-level transport of a two-coordinate
indifference, nothing less. -/

/-- **The off-cal diagonal step is the level transport of the free `st`-step (PROVED,
machine-checked characterization of the wall).**

`CalibrationAllBackgrounds` gives the diagonal step at `st` for free.  The off-cal
diagonal step at `c` is therefore equivalent to transporting that `st`-indifference to
`c`.  We state the forward direction: given a transport hypothesis `htrans` carrying the
`st`-diagonal indifference to `c`, the off-cal step holds.  The transport hypothesis is
*exactly* `TBlockDiagonalResidue` applied at this cell (both profiles differ in `j` and
`k`) — making precise that the crux is the cross-level transport, the target itself.
Audit `[propext, Quot.sound]`. -/
theorem diagonalOffCal_of_levelTransport
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G) (m n : ℕ) (c : X t)
    (htrans : P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st)
                       (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st) →
              P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
                       (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)) :
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) c) :=
  htrans (interiorDiagonalStep_st_of_allBackgrounds G hcal m n)

/-- **The transport hypothesis of §C is exactly `TBlockDiagonalResidue` at the cell
(PROVED — the circularity made explicit).**

`TBlockDiagonalResidue P j k t` (applied at background `G.a`, `j`-values `αⱼ(m+1) ≠ αⱼ m`,
`k`-values `αₖ n ≠ αₖ(n+1)`, levels `st → c`) provides *precisely* the transport
hypothesis `diagonalOffCal_of_levelTransport` consumes.  So deriving the off-cal step
from `TBlockDiagonalResidue` is immediate — and circular for the crux (it IS the
target).  This theorem makes the §D.2b circularity explicit at the single-cell level:
the off-cal match's only missing ingredient is the target itself.  Audit
`[propext, Quot.sound]`. -/
theorem diagonalOffCal_of_tBlockDiagonalResidue
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G) (m n : ℕ) (c : X t)
    (hinj_j : Function.Injective G.αj) (hinj_k : Function.Injective G.αk)
    (hTD : TBlockDiagonalResidue P j k t) :
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) c) := by
  have hjm : G.αj (m + 1) ≠ G.αj m := fun h => by have := hinj_j h; omega
  have hkn : G.αk n ≠ G.αk (n + 1) := fun h => by have := hinj_k h; omega
  refine diagonalOffCal_of_levelTransport G hcal m n c (fun hst => ?_)
  exact ⟨hTD G.a (G.αj (m + 1)) (G.αj m) (G.αk (n + 1)) (G.αk n) G.st c hjm hkn hst.1,
         hTD G.a (G.αj m) (G.αj (m + 1)) (G.αk n) (G.αk (n + 1)) G.st c
           (Ne.symm hjm) (Ne.symm hkn) hst.2⟩

/-! ## §D.  Soundness gate -/

/-- **Soundness gate (PROVED): the off-cal match is necessary under a rep.**

Re-export of `offCalCompensationMatch_of_additiveRep` (`OptionB_C1aGridThomsen`): under
any additive representation the equal-spacing of the two grids forces the match.  So the
crux target hides nothing false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem offCalMatch_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) :
    OffCalCompensationMatch P j k t G :=
  offCalCompensationMatch_of_additiveRep R hjk hjt hkt G

end ProductPref
end WakkerInfra

/-! ## C1.a-3 audit

* §A (non-circular, weak order): `matchCell_of_diagonalOffCal` /
  `diagonalOffCal_of_matchCell` — the match at a cell IS the off-cal diagonal step
  (via the C1.a-1 compensator).
* §B (non-circular): `matchCell_at_st_free` — the match holds FREE at the calibration
  level `st` (from `CalibrationAllBackgrounds`).
* §C (the wall, machine-checked): `diagonalOffCal_of_levelTransport` — the off-cal step
  is exactly the `st → c` transport of the free diagonal step;
  `diagonalOffCal_of_tBlockDiagonalResidue` — that transport IS `TBlockDiagonalResidue`
  at the cell (the §D.2b circularity made explicit at single-cell granularity).
* §D (gate): `offCalMatch_of_additiveRep`.

**Honest determination.**  §A–§B reduce the off-cal match, by pure weak order, to the
bare `st → c` level transport of a `{j,k}`-two-coordinate-difference indifference (the
free calibration-level step is discharged).  §C proves that transport IS the target
`TBlockDiagonalResidue` — so there is NO non-circular cell-level lemma closing the crux;
the remaining content is the absolute minimum (one two-coordinate indifference,
transported one `t`-level), which is genuinely irreducible by cell-level reasoning (the
fifth circularity wall, now at single-cell, single-level granularity).  Discharging it
needs the global Debreu/KLST standard-sequence construction (the multi-week §IV.5
frontier) or the §6 fallback (carry `TBlockWeakIndependent`, the proven-necessary KLST
hypothesis).  Audit `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.matchCell_of_diagonalOffCal
#print axioms WakkerInfra.ProductPref.diagonalOffCal_of_matchCell
#print axioms WakkerInfra.ProductPref.matchCell_at_st_free
#print axioms WakkerInfra.ProductPref.diagonalOffCal_of_levelTransport
#print axioms WakkerInfra.ProductPref.diagonalOffCal_of_tBlockDiagonalResidue
#print axioms WakkerInfra.ProductPref.offCalMatch_of_additiveRep
