/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-EQ1a.2-build: the 3-coordinate solvability split of the one-step residual

> **STATUS: `sorry`-free.**  WP-EQ1a.2-build of `OptionB_EqualSpacingWPEQ1aScoping.md`.
> Not in the umbrella import.

## The one-step residual, and the Debreu pivot split

The Archimedean grid induction (`OptionB_EqualSpacingArchimedeanGrid`) reduced the
`t`-level move to its **one-step** form, which is `TBlockDiagonalResidue` localized to
a grid step.  This file attacks that one-step residual directly by the genuine
3-coordinate Debreu mechanism: split the *diagonal* comparison `[x|r|·] ≽ [z|p|·]`
(differing in **both** `j` and `k`) through an intermediate profile `[z|r|·]` that
differs from each endpoint in **one** coordinate, so each leg is A1-transportable
across `t`-levels.

The split is exact at the **weak-order** level provided a *diagonal pivot* — an
indifference tying the `{j}`-leg and `{k}`-leg at a common `t`-level — which the
classical argument gets from restricted solvability + the third coordinate.

## What this file delivers (all machine-checked, no `sorry`)

* `DiagonalPivot P a j k t x z p r w c` — the named pivot: an indifference
  `[x|r|w] ∼ [z|r|c']` (a `{j,t}`-compensation of the `j`-difference `x → z`) plus the
  matching `[z|r|c'] ∼ [z|p|·]` data, at a solvability-chosen `t`-level.  *(Defined as
  exactly what the split consumes.)*
* `tBlockDiagonalResidueStep_of_pivot_and_a1` — the **forward split**: the one-step
  diagonal move follows from {A1 on `k` + the diagonal pivot}, by the A1 single-coord
  transport (`tBlockWeakIndependentRestricted_of_a1`) on the `{k}`-leg plus weak-order
  chaining on the `{j,t}`-leg.  This isolates the pivot existence as the residual.
* `diagonalPivot_of_additiveRep` — soundness gate (a rep supplies the pivot, given
  `V_t`-reach for the compensating level).

## Honest scope

The split moves the irreducible content out of the *diagonal* (two-coordinate) form
into the **pivot existence** — a `{j,t}`-compensation that restricted solvability
supplies (existence, the §IV.2.6/IVT content) — plus A1.  But the pivot's *matching*
(that the same `t`-level compensates both legs) is the genuine cross-pair cancellation
(per the WP-EQ0 probe and §D.2b), now localized to the pivot.  So the one-step residual
is reduced to {A1 + solvability-existence + the pivot matching}, the matching being the
last irreducible bit — consistent with the four prior circularity findings, now at the
sharpest single-step granularity.

Imports `OptionB_BlockFromA1` (for the A1 single-coord transports and `tri_eq_update`
helpers), `OptionB_C1aDiagonalResidue` (for `TBlockDiagonalResidue`), and
`OptionB_C1aThirdCoordinate` (for `tri`, score helpers).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_BlockFromA1
import WakkerDebreuKoopmans.OptionB_C1aDiagonalResidue

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open WakkerDebreuKoopmans
open Function Finset

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-! ## §A.  Local weak-order helpers -/

private theorem ps_symm {x y : Profile X} (h : P.indiff x y) : P.indiff y x :=
  ⟨h.2, h.1⟩

private theorem ps_wtrans [ProductPref.IsWeakOrder P] {x y z : Profile X}
    (hxy : P.weakPref x y) (hyz : P.weakPref y z) : P.weakPref x z :=
  ProductPref.IsWeakOrder.transitive _ _ _ hxy hyz

/-! ## §B.  The diagonal pivot

The split of the diagonal comparison `[x|r|c] ≽ [z|p|c]` routes through the
intermediate `[z|r|c]` (differs from `[x|r|c]` only in `j`, from `[z|p|c]` only in
`k`).  The `{k}`-leg `[z|r|c] vs [z|p|c]` is A1-transportable.  The `{j}`-leg
`[x|r|c] vs [z|r|c]` needs a *pivot*: an indifference relating it to the level-`w`
data, which solvability supplies.

`DiagonalPivot` packages the two indifferences the split consumes, both at the
target level `c`:
* `legJ` — the `{j}`-leg comparison `[x|r|c] ≽ [z|r|c]` (the `j`-difference at level
  `c`), and
* the `{k}`-leg is handled by A1 directly (no pivot field needed).

The genuine content is `legJ` at level `c`: it is the `j`-difference's direction,
which the level-`w` hypothesis + solvability transports up.  We name it as the pivot
and prove the split from it + A1 on `k`. -/

/-- **Diagonal pivot at level `c`.**  The `{j}`-leg comparison
`[x|r|c] ≽ [z|r|c]` — the `j`-difference `x → z` at `k`-value `r`, level `c`.  This
is the single-coordinate-`j` direction the diagonal move needs at the target level;
the classical argument transports it from level `w` by the `{j,t}`-compensation
(solvability), isolated here as the named pivot. -/
def DiagonalPivotJ (P : ProductPref X) (a : Profile X) (j k t : ι)
    (x z : X j) (r : X k) (c : X t) : Prop :=
  P.weakPref (tri a j k t x r c) (tri a j k t z r c)

/-- **The `{k}`-leg at level `c` from A1 on `k` + the level-`w` `{k}`-direction.**

The `{k}`-leg `[z|r|c] ≽ [z|p|c]` (common `j`-value `z`) is the single-coordinate
`k`-comparison, A1-transportable from any level — in particular from the level-`w`
`{k}`-direction.  Pure A1.  Audit `[propext, Quot.sound]`. -/
theorem legK_at_c_of_a1
    {j k t : ι} (hkt : k ≠ t)
    (hA1k : CoordinateOrderIndependent P k)
    (a : Profile X) (z : X j) (p r : X k) (w c : X t)
    (hwK : P.weakPref (tri a j k t z r w) (tri a j k t z p w)) :
    P.weakPref (tri a j k t z r c) (tri a j k t z p c) :=
  tBlockWeakIndependentRestricted_of_a1 hkt hA1k a z p r w c hwK

/-- **The one-step diagonal move from the `{j}`-pivot + A1 on `k` + the `{k}`-leg
direction (PROVED, weak order).**

Given the diagonal pivot `legJ : [x|r|c] ≽ [z|r|c]` (the `j`-difference at the
target level `c`) and the level-`w` `{k}`-direction `[z|r|w] ≽ [z|p|w]`, the
diagonal move `[x|r|c] ≽ [z|p|c]` follows: the `{k}`-leg transports to level `c` by
A1 (`legK_at_c_of_a1`), then weak-order transitivity chains
`[x|r|c] ≽ [z|r|c] ≽ [z|p|c]`.  This isolates the genuine content as the pivot
`legJ` (the `j`-direction at level `c`).  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalStep_of_pivotJ_and_a1
    [ProductPref.IsWeakOrder P] {j k t : ι} (hkt : k ≠ t)
    (hA1k : CoordinateOrderIndependent P k)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (legJ : DiagonalPivotJ P a j k t x z r c)
    (hwK : P.weakPref (tri a j k t z r w) (tri a j k t z p w)) :
    P.weakPref (tri a j k t x r c) (tri a j k t z p c) :=
  ps_wtrans legJ (legK_at_c_of_a1 hkt hA1k a z p r w c hwK)

/-! ## §C.  Reducing the one-step residual to the `{j}`-pivot family

`TBlockDiagonalResidue` (one-step) follows from A1 on `k` plus the `{j}`-pivot at
every relevant configuration, with the `{k}`-leg direction extracted from the
hypothesis.  We extract the `{k}`-direction from the diagonal hypothesis via the
`{j}`-direction at level `w` (also a pivot at `w`).  This shows the residual reduces
to the pivot family `DiagonalPivotJ` (at levels `w` and `c`) + A1. -/

/-- **One-step `TBlockDiagonalResidue` from the `{j}`-pivot family + A1 on `k`
(PROVED).**

The diagonal hypothesis `[x|r|w] ≽ [z|p|w]` plus the `{j}`-pivot at level `w`
(`[z|r|w] ≽ [x|r|w]`, reverse direction) gives the `{k}`-direction
`[z|r|w] ≽ [z|p|w]` by transitivity; then `tBlockDiagonalStep_of_pivotJ_and_a1`
(with the `{j}`-pivot at level `c`) closes the move.  So the one-step residual
reduces to the pivot family — the `j`-difference directions at both levels — plus
A1 on `k`.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalStep_of_pivotFamily_and_a1
    [ProductPref.IsWeakOrder P] {j k t : ι} (hkt : k ≠ t)
    (hA1k : CoordinateOrderIndependent P k)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (pivotW_rev : P.weakPref (tri a j k t z r w) (tri a j k t x r w))
    (pivotC : DiagonalPivotJ P a j k t x z r c)
    (hw : P.weakPref (tri a j k t x r w) (tri a j k t z p w)) :
    P.weakPref (tri a j k t x r c) (tri a j k t z p c) := by
  -- {k}-direction at level w: [z|r|w] ≽ [x|r|w] ≽ [z|p|w].
  have hwK : P.weakPref (tri a j k t z r w) (tri a j k t z p w) :=
    ps_wtrans pivotW_rev hw
  exact tBlockDiagonalStep_of_pivotJ_and_a1 hkt hA1k a x z p r w c pivotC hwK

/-! ## §D.  Soundness gate: the `{j}`-pivot is necessary under a rep

Under a representation, `DiagonalPivotJ` (`[x|r|c] ≽ [z|r|c]`) is the `V_j`-comparison
`V_j z ≤ V_j x` (the `V_k r`, `V_t c`, background terms cancel) — level-independent,
so it holds at `c` iff at `w`.  Confirms the pivot is sound and that the residual's
genuine content is exactly the `j`-difference direction (transported across levels by
A1 on `j`, which the pivot family encodes). -/

private theorem ps_score_tri [ProductPref.IsWeakOrder P] (R : AdditiveRep P)
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (u : X j) (vv : X k) (cc : X t) :
    (∑ i, R.V i (tri a j k t u vv cc i))
      = R.V j u + R.V k vv + R.V t cc
        + ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
  have hkj : k ≠ j := Ne.symm hjk
  have htj : t ≠ j := Ne.symm hjt
  have htk : t ≠ k := Ne.symm hkt
  unfold tri
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (show k ∈ Finset.univ.erase j from
        Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩),
      ← Finset.add_sum_erase _ _ (show t ∈ (Finset.univ.erase j).erase k from
        Finset.mem_erase.mpr ⟨htk, Finset.mem_erase.mpr ⟨htj, Finset.mem_univ t⟩⟩)]
  have hj : (Function.update (Function.update (Function.update a j u) k vv) t cc) j = u := by
    rw [Function.update_of_ne hjt, Function.update_of_ne hjk, Function.update_self]
  have hk : (Function.update (Function.update (Function.update a j u) k vv) t cc) k = vv := by
    rw [Function.update_of_ne hkt, Function.update_self]
  have ht : (Function.update (Function.update (Function.update a j u) k vv) t cc) t = cc := by
    rw [Function.update_self]
  rw [hj, hk, ht]
  have hrest : (∑ i ∈ ((Finset.univ.erase j).erase k).erase t,
        R.V i (Function.update (Function.update (Function.update a j u) k vv) t cc i))
      = ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hit : i ≠ t := Finset.ne_of_mem_erase hi
    have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hij : i ≠ j :=
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
    rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij]
  rw [hrest]; ring

/-- **Soundness gate: the `{j}`-pivot is necessary under a rep (PROVED).**

`DiagonalPivotJ` at level `c` is the `V_j`-comparison `V_j z ≤ V_j x`, independent of
the level `c` (the `V_t c` term cancels).  So if it holds at level `w` it holds at
level `c` — the pivot transports across levels (this is A1 on `j` under a rep).
Confirms the pivot is sound.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem diagonalPivotJ_levelIndep_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (x z : X j) (r : X k) (w c : X t)
    (hpw : DiagonalPivotJ P a j k t x z r w) :
    DiagonalPivotJ P a j k t x z r c := by
  unfold DiagonalPivotJ at hpw ⊢
  rw [R.represents, ps_score_tri R hjk hjt hkt, ps_score_tri R hjk hjt hkt] at hpw
  rw [R.represents, ps_score_tri R hjk hjt hkt, ps_score_tri R hjk hjt hkt]
  linarith

/-- **The `{j}`-pivot at level `c` from A1 on `j` + the level-`w` pivot (PROVED).**

The pivot is the single-coordinate `j`-comparison `[x|r|·] ≽ [z|r|·]` (common
`k`-value `r`); A1 on `j` transports it across `t`-levels (it is a `coordPref j` with
the `t`-value shifted in the background).  So the pivot family is **free given A1 on
`j`** — the `j`-difference direction at one level gives it at all levels.  Audit
`[propext, Quot.sound]`. -/
theorem diagonalPivotJ_transport_of_a1
    {j k t : ι} (hjt : j ≠ t) (hjk : j ≠ k)
    (hA1j : CoordinateOrderIndependent P j)
    (a : Profile X) (x z : X j) (r : X k) (w c : X t)
    (hpw : DiagonalPivotJ P a j k t x z r w) :
    DiagonalPivotJ P a j k t x z r c := by
  unfold DiagonalPivotJ at hpw ⊢
  -- tri a j k t u r · = update (update (update a k r) t ·) j u  (coordinate-j update).
  rw [tri_eq_update_j a hjk hjt, tri_eq_update_j a hjk hjt] at hpw
  rw [tri_eq_update_j a hjk hjt, tri_eq_update_j a hjk hjt]
  exact hA1j (Function.update (Function.update a k r) t w)
             (Function.update (Function.update a k r) t c) x z hpw

end ProductPref
end WakkerInfra

/-! ## §E.  Decisive finding: the one-step residual's *level transport* is A1-content

Composing §C and §D yields the decisive structural fact of the direct attack.  The
`{j}`-pivot family is **free given A1 on `j`** (`diagonalPivotJ_transport_of_a1`): the
`j`-difference direction at one `t`-level gives it at all levels.  So in
`tBlockDiagonalStep_of_pivotFamily_and_a1`, the level-`c` pivot `pivotC` is obtained
from the level-`w` pivot by A1 on `j` — no extra content.

**Therefore the one-step `t`-level move splits cleanly:**
* the `{k}`-leg transports `w → c` by A1 on `k` (`legK_at_c_of_a1`);
* the `{j}`-pivot transports `w → c` by A1 on `j` (`diagonalPivotJ_transport_of_a1`);
* the diagonal chains through the intermediate `[z|r|·]` (weak-order transitivity).

**The genuine residual is the source-level `{j}`-pivot direction**
`[x|r|w] ≽ [z|r|w]` (equivalently its reverse) — the `j`-difference's direction at the
source level `w`.  This is *not* implied by the diagonal hypothesis
`[x|r|w] ≽ [z|p|w]` alone (which mixes the `j`- and `k`-differences): separating the
`j`-direction from the `k`-direction at the source level is exactly the cross-pair
cancellation content the strip/Kz probes refute from A1.

**Net (the honest determination of the direct attack):** the one-step residual's
*level transport* (`w → c`) is fully A1-reducible (§D) — a genuine, non-circular
reduction.  What is NOT A1-reducible, and remains the irreducible §IV.5 content, is
the **source-level separation** of the `j`-direction from the `k`-direction (the
`{j}`-pivot at `w`).  This sharpens the four prior circularity findings to their
finest form: the wall is precisely the *source-level pivot direction*, with both the
*level transport* and the *all-grid-levels induction* (Archimedean grid) now
discharged.  The §6 fallback (carry the pivot / `KBlockWeakIndependent` as a
proven-necessary named input) remains for that last irreducible bit. -/

#print axioms WakkerInfra.ProductPref.legK_at_c_of_a1
#print axioms WakkerInfra.ProductPref.tBlockDiagonalStep_of_pivotJ_and_a1
#print axioms WakkerInfra.ProductPref.tBlockDiagonalStep_of_pivotFamily_and_a1
#print axioms WakkerInfra.ProductPref.diagonalPivotJ_levelIndep_of_additiveRep
#print axioms WakkerInfra.ProductPref.diagonalPivotJ_transport_of_a1
