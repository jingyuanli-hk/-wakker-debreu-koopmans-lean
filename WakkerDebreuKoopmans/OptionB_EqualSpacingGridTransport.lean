/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — G2: transport the grid step to all profiles (the full `TBlockDiagonalResidue`)

> **STATUS: `sorry`-free forward brick on the §IV.5 grid construction (G2).**
> Not in the umbrella import.

This file executes **G2** of `OptionB_SectionIV5GridConstructionRoadmap.md`: lift the
G1 grid step (which holds at the discrete *grid points* `(αⱼ m, αₖ n)`) to the full
`TBlockDiagonalResidue P j k t` — `t`-level invariance of the `{j,k}`-comparison at
**all** `{j,k}`-values and **all** backgrounds.

## The non-circular block route (vs. the frontier route)

The existing transport capstone
`OptionB_C1aGridTransport.tBlockDiagonalResidue_of_frontier_and_stableCover` feeds the
grid-restricted residue from `GridThomsenForwardFrontier` (the bespoke forward-data
bundle, which carries topology + solvability + A1-`k` + matching residuals).  This
file instead feeds it from the **G1.b block-route closure**
`gridThomsenClosure_of_blockIndependence` — so the transport rests on exactly:

* the three **KLST block conditions** `{T,K,J}`-block (G1.b, non-circular);
* **A1 on `j`** (`CoordinateOrderIndependent P j`) — the single-coordinate
  independence the closure→residue bridge `gridTBlockDiagonalResidue_of_closure` uses;
* the **level-stable grid cover** `StableGridIndifferentCover` (the §IV.2.6 density
  content — the G3 input).

It needs **no topology bundle, no restricted solvability, no A1-`k`** — strictly
leaner than the frontier route, because the block conditions already discharge all the
cross-pair calibration content (G1.a/b).

## The transport chain (each link reused, no rebuilds)

1. `gridThomsenClosure_of_blockIndependence` (G1.b) — closure from `{T,K,J}`-block.
2. `gridTBlockDiagonalResidue_of_closure` — closure + A1-`j` ⟹ grid-restricted
   weakPref residue (collapse the `{j,k}`-comparison to a pure `j`-grid comparison,
   then A1-`j` moves the `t`-level).
3. `tBlockDiagonalResidue_of_gridRestricted_and_stableCover` — grid-restricted residue
   + stable cover ⟹ full residue over the grid's background (replace each value by
   its level-stable grid representative).
4. `tri_eq_of_agreeOff` — the background bridge (the residue is base-independent off
   `{j,k,t}`, so a per-background grid whose base agrees off `{j,k,t}` covers every
   background).

## What this file delivers (all machine-checked, no `sorry`)

* `gridRestrictedTBlock_of_blockIndependence` — step 1+2: the grid-restricted residue
  from the three block conditions + A1-`j`.
* `tBlockDiagonalResidue_fixedGrid_of_blockIndependence_and_cover` — steps 1–4 over a
  fixed background (the grid's base agreeing off `{j,k,t}`).
* `TBlockGridCoverData` + `tBlockDiagonalResidue_of_blockIndependence_and_coverData`
  — **the G2 target**: the full `TBlockDiagonalResidue P j k t` over *all* backgrounds
  from {three block conditions + A1-`j` + a background-indexed stable-cover family}.
* `tBlockDiagonalResidue_necessary` — soundness gate (the residue is necessary under a
  representation).

## Honest scope

G2 transports the grid step to all profiles through the *block-condition* route, so
the §IV.5 residue `TBlockDiagonalResidue` is reduced to {the three KLST block
conditions (G1, proved necessary, A1-non-derivable) + A1-`j` (theorem-backed) + the
level-stable grid cover (`StableGridIndifferentCover`)}.  The cover is the §IV.2.6
density content — the **G3** input (`OptionB_C1aGridTransport` §J–§K prove it is *not*
solvability-reachable and needs the continuity+density closure).  Discharging the
block conditions (G1 crux) and the cover (G3) are the remaining obligations; with both
in hand, this yields the unrestricted Thomsen residue, hence (via the existing
one-Thomsen hexagon capstone at the three coordinate triples) the classical
`DoubleCancellation`.

Imports `OptionB_EqualSpacingGridPropagate` (G1.b closure) and
`OptionB_C1aGridTransport` (the transport links + cover).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_EqualSpacingGridPropagate
import WakkerDebreuKoopmans.OptionB_C1aGridTransport

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

/-! ## §A.  Grid-restricted residue from the block conditions (steps 1+2) -/

/-- **Grid-restricted `t`-block residue from the three KLST block conditions + A1-`j`
(PROVED).**

Composes G1.b (`gridThomsenClosure_of_blockIndependence`) with the closure→residue
bridge (`gridTBlockDiagonalResidue_of_closure`).  On the calibrated grid, the
`{j,k}`-comparison between grid points is `t`-level invariant: if `(αⱼ m, αₖ n)` and
`(αⱼ m', αₖ n')` compare a certain way at level `w`, they compare the same way at any
level `c`.  This is the grid restriction of `TBlockDiagonalResidue`, derived through
the **non-circular** block route (no `GridThomsenForwardFrontier`, no topology, no
solvability).  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridRestrictedTBlock_of_blockIndependence
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (G : CalibratedJKGrid P j k t)
    (hTB : TBlockWeakIndependent P j k t)
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t)
    (m n m' n' : ℕ) (w c : X t)
    (hw : P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  w)
                     (tri G.a j k t (G.αj m') (G.αk n') w)) :
    P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  c)
               (tri G.a j k t (G.αj m') (G.αk n') c) :=
  gridTBlockDiagonalResidue_of_closure hjk hjt hkt hA1j G
    (gridThomsenClosure_of_blockIndependence G hTB hKB hJB) m n m' n' w c hw

/-! ## §B.  Full residue over a fixed background (steps 1–4) -/

/-- **Full `t`-block residue over a fixed background from the block conditions + a
stable cover (PROVED).**

For a background `a'` agreeing with the grid's base off `{j,k,t}`: feed the §A
grid-restricted residue and the level-stable cover into
`tBlockDiagonalResidue_of_gridRestricted_and_stableCover` (replace each `{j,k}`-value
by its grid representative at every level, move the level on the grid comparison,
substitute back), then bridge the arbitrary background `a'` to the grid's base via
`tri_eq_of_agreeOff`.  This is the non-circular analog of
`tBlockDiagonalResidue_of_frontier_and_stableCover` — but with no topology, no
solvability, no A1-`k`.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockDiagonalResidue_fixedGrid_of_blockIndependence_and_cover
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hTB : TBlockWeakIndependent P j k t)
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t)
    (G : CalibratedJKGrid P j k t)
    (cover : StableGridIndifferentCover P j k t G)
    (a' : Profile X)
    (hbg : ∀ i, i ≠ j → i ≠ k → i ≠ t → a' i = G.a i) :
    ∀ (x z : X j) (p r : X k) (w c : X t),
      x ≠ z → r ≠ p →
      P.weakPref (tri a' j k t x r w) (tri a' j k t z p w) →
      P.weakPref (tri a' j k t x r c) (tri a' j k t z p c) := by
  -- The grid-restricted residue (§A) packaged as the transport's hypothesis.
  have gridRestricted : ∀ (m n m' n' : ℕ) (w c : X t),
      P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  w)
                 (tri G.a j k t (G.αj m') (G.αk n') w) →
      P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  c)
                 (tri G.a j k t (G.αj m') (G.αk n') c) :=
    fun m n m' n' w c hw =>
      gridRestrictedTBlock_of_blockIndependence hjk hjt hkt hA1j G hTB hKB hJB
        m n m' n' w c hw
  intro x z p r w c hxz hrp hw
  -- Bridge the arbitrary background `a'` to the grid base `G.a` (base-independence).
  have hbridge : ∀ (u : X j) (vv : X k) (cc : X t),
      tri a' j k t u vv cc = tri G.a j k t u vv cc :=
    fun u vv cc => tri_eq_of_agreeOff a' G.a j k t hbg u vv cc
  rw [hbridge x r w, hbridge z p w] at hw
  have hfull := tBlockDiagonalResidue_of_gridRestricted_and_stableCover G cover
    gridRestricted x z p r w c hw
  rw [hbridge x r c, hbridge z p c]
  exact hfull

/-! ## §C.  The G2 target: full residue over all backgrounds -/

/-- **Background-indexed grid + stable-cover family (the per-background §IV.5 data).**

Mirrors `OptionB_C1aGridTransport.TBlockGridRouteData`, but — because the block-route
closure is global (the three block conditions and A1-`j` are properties of `P`, not of
a grid) — it carries only the per-background **grid** (whose base agrees with the
background off `{j,k,t}`) and the per-background **stable cover**.  No per-background
forward frontier is needed (the block conditions replace it). -/
structure TBlockGridCoverData (P : ProductPref X) (j k t : ι) where
  /-- The calibrated grid for each background. -/
  grid  : Profile X → CalibratedJKGrid P j k t
  /-- The grid's base agrees with the background off `{j,k,t}`. -/
  agree : ∀ (a : Profile X) (i : ι), i ≠ j → i ≠ k → i ≠ t → a i = (grid a).a i
  /-- The level-stable grid cover for each grid (the §IV.2.6 / G3 density content). -/
  cover : ∀ a : Profile X, StableGridIndifferentCover P j k t (grid a)

/-- **G2 target: the full `TBlockDiagonalResidue P j k t` from the three KLST block
conditions + A1-`j` + the background-indexed stable-cover family (PROVED).**

For each residue background `a`, instantiate the per-background grid (base agreeing
off `{j,k,t}`) and apply §B.  This is G2's endpoint: the grid step (grid points) is
transported to the **unrestricted** Thomsen residue over **every** background, through
the non-circular block route.  The only §IV.5/§IV.2.6 inputs are the three block
conditions (G1) and the stable covers (G3).  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem tBlockDiagonalResidue_of_blockIndependence_and_coverData
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hTB : TBlockWeakIndependent P j k t)
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t)
    (data : TBlockGridCoverData P j k t) :
    TBlockDiagonalResidue P j k t := by
  intro a x z p r w c hxz hrp hw
  exact tBlockDiagonalResidue_fixedGrid_of_blockIndependence_and_cover
    hjk hjt hkt hA1j hTB hKB hJB (data.grid a) (data.cover a) a (data.agree a)
    x z p r w c hxz hrp hw

/-! ## §D.  Soundness gate -/

/-- **Soundness gate (PROVED): the full residue is necessary under a rep.**

Re-export of `tBlockDiagonalResidue_of_additiveRep` (`OptionB_C1aDiagonalResidue`):
under any additive representation the common `V_t` term cancels, so the residue holds.
Confirms the G2 target hides nothing false — it is necessary for any preference with
an additive representation.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockDiagonalResidue_necessary
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    TBlockDiagonalResidue P j k t :=
  tBlockDiagonalResidue_of_additiveRep R hjk hjt hkt

end ProductPref
end WakkerInfra

/-! ## G2 audit

* §A: `gridRestrictedTBlock_of_blockIndependence` — the grid-restricted residue from
  the three block conditions + A1-`j` (closure → bridge), non-circular.
* §B: `tBlockDiagonalResidue_fixedGrid_of_blockIndependence_and_cover` — the full
  residue over a fixed background (grid-restricted + stable cover + background bridge).
* §C: `TBlockGridCoverData` + `tBlockDiagonalResidue_of_blockIndependence_and_coverData`
  — the G2 target: the full residue over all backgrounds.
* §D: `tBlockDiagonalResidue_necessary` — soundness gate.

**Honest scope.**  G2 transports the grid step to all profiles via the block route, so
`TBlockDiagonalResidue` is reduced to {three KLST block conditions (G1) + A1-`j`
(theorem-backed) + the level-stable grid cover (G3 §IV.2.6 density)}.  The block route
is strictly leaner than the frontier route (no topology, no solvability, no A1-`k`).
Discharging the block conditions (G1 crux) and the cover (G3) are the remaining
obligations. -/

#print axioms WakkerInfra.ProductPref.gridRestrictedTBlock_of_blockIndependence
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_fixedGrid_of_blockIndependence_and_cover
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_blockIndependence_and_coverData
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_necessary
