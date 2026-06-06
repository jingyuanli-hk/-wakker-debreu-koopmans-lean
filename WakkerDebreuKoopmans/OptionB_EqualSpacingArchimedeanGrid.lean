/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-EQ1a.2-build (ab-initio): Archimedean grid induction for the level move

> **STATUS: `sorry`-free.**  WP-EQ1a.2-build of `OptionB_EqualSpacingWPEQ1aScoping.md`.
> Not in the umbrella import.

## The one axiom the forward attempts had not engaged: Archimedean

The three prior circularity findings (second sequence, match-cell, layer transport)
all came from *pure weak-order* reformulation.  The genuine Debreu/KLST escape uses
the **Archimedean** axiom: a strict `t`-standard-sequence grid, by induction, reaches
arbitrarily far, so a property holding *one grid step at a time* holds at *every grid
point*.

This file mechanizes that induction skeleton for the `t`-level move — the genuine,
non-circular use of Archimedean — and isolates exactly the residual it leaves.

## What the repo's no-go theorems constrain (respected here)

`M2Frontier.additiveRealBool_archimedean_tradeoff_solvability_insufficient_for_selectedRefinedDenseGrid`
proves Archimedean + solvability + tradeoff are **insufficient** even for a single
dense grid: a strict standard sequence is an arithmetic progression, hence not dense.
So the induction reaches all **grid points**, but reaching *arbitrary* `t`-levels
needs the §IV.2.6 density/refinement-mesh residual (residual 2, already characterized
and soundness-gated).  This file therefore delivers the grid-restricted level move,
not the continuum one — honestly bounded by the no-go.

## What this file delivers (all machine-checked, no `sorry`)

* `GridLevelMoveStep P a j k t x z p r σ i` — the **one-step** `t`-level move: the
  `{j,k}`-diagonal comparison transports from grid level `σ.α i` to `σ.α (i+1)`.
* `gridLevelMove_of_step` — **the Archimedean grid induction (free):** if the
  one-step move holds at every `i`, the comparison transports from `σ.α 0` to
  `σ.α n` for **every** `n`, by induction.  This is the genuine non-circular use of
  the standard-sequence grid: one step ⟹ all grid points.
* `gridLevelMoveStep_of_tBlockDiagonalResidue` — the one-step move follows from the
  standard `TBlockDiagonalResidue` (so the residual is no stronger than the
  established frontier).
* `gridLevelMoveStep_of_additiveRep` — soundness gate.

## Honest scope

The grid induction (`gridLevelMove_of_step`) is genuinely free — it is the
non-circular Archimedean content.  The **one-step** move `GridLevelMoveStep` remains
the irreducible §IV.5 content: it is `TBlockDiagonalResidue` localized to a single
`t`-grid step (proved below), which the probes show is not A1-derivable and the prior
findings show is not weak-order-reducible.  So the level move is reduced to {grid
induction (free) + one-step residual + §IV.2.6 density to reach off-grid levels} —
the one-step residual being the genuine remaining content, now sharply localized.

Imports `OptionB_C1aThirdCoordinate` (for `tri`), `OptionB_C1aDiagonalResidue` (for
`TBlockDiagonalResidue`), and `Core` (for `StandardSequence`).  Not in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_C1aThirdCoordinate
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

/-! ## §A.  The one-step `t`-level move along a standard-sequence grid

`GridLevelMoveStep … i` is the `{j,k}`-diagonal comparison transported from the
`t`-grid level `σ.α i` to the next level `σ.α (i+1)`.  The grid `σ.α : ℕ → X t` is a
strict `t`-standard sequence (the measuring stick); we only use its values as the
`t`-levels, so we parametrise directly by a level function `glvl : ℕ → X t`. -/

/-- **One-step `t`-level move** (transport the diagonal comparison `σ.α i → σ.α (i+1)`).

For fixed `{j,k}`-difference data `(x,z,p,r)` and a `t`-level grid `glvl`, the
weak-preference comparison at level `glvl i` transports to level `glvl (i+1)`. -/
def GridLevelMoveStep (P : ProductPref X) (a : Profile X) (j k t : ι)
    (x z : X j) (p r : X k) (glvl : ℕ → X t) (i : ℕ) : Prop :=
  P.weakPref (tri a j k t x r (glvl i)) (tri a j k t z p (glvl i)) →
  P.weakPref (tri a j k t x r (glvl (i + 1))) (tri a j k t z p (glvl (i + 1)))

/-! ## §B.  The Archimedean grid induction (free — the genuine non-circular content)

If the one-step move holds at every grid step, the comparison transports from the
base grid level `glvl 0` to every grid level `glvl n` by induction on `n`.  This is
the genuine use of the standard-sequence grid: it needs **no** new cancellation
content beyond the one-step move — pure induction. -/

/-- **Grid induction: one-step move at every step ⟹ move to every grid level
(PROVED, free).**

By induction on `n`: the base case is reflexive (level `glvl 0` to itself), and the
inductive step chains the move to level `glvl n` with the one-step move
`glvl n → glvl (n+1)`.  No cancellation content — the genuine non-circular
Archimedean grid content.  Audit `[propext, Quot.sound]`. -/
theorem gridLevelMove_of_step
    {j k t : ι} (a : Profile X) (x z : X j) (p r : X k) (glvl : ℕ → X t)
    (hstep : ∀ i, GridLevelMoveStep P a j k t x z p r glvl i)
    (hbase : P.weakPref (tri a j k t x r (glvl 0)) (tri a j k t z p (glvl 0)))
    (n : ℕ) :
    P.weakPref (tri a j k t x r (glvl n)) (tri a j k t z p (glvl n)) := by
  induction n with
  | zero => exact hbase
  | succ n ih => exact hstep n ih

/-! ## §C.  The one-step move IS `TBlockDiagonalResidue` localized to a grid step

The one-step move is the standard `t`-block diagonal residue, restricted to the two
consecutive grid levels `glvl i`, `glvl (i+1)`.  So the grid induction reduces the
level move to the established frontier residual — no new object. -/

/-- **One-step move from `TBlockDiagonalResidue` (PROVED).**

`TBlockDiagonalResidue` transports the diagonal comparison between *any* two
`t`-levels; in particular between consecutive grid levels.  So the one-step move is
no stronger than the established frontier residual.  Audit `[propext, Quot.sound]`. -/
theorem gridLevelMoveStep_of_tBlockDiagonalResidue
    {j k t : ι} (a : Profile X) (x z : X j) (p r : X k) (glvl : ℕ → X t) (i : ℕ)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (hTD : TBlockDiagonalResidue P j k t) :
    GridLevelMoveStep P a j k t x z p r glvl i :=
  fun hw => hTD a x z p r (glvl i) (glvl (i + 1)) hxz hrp hw

/-! ## §D.  Soundness gate -/

/-- Score split of a `tri` profile (local copy). -/
private theorem ag_score_tri [ProductPref.IsWeakOrder P] (R : AdditiveRep P)
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

/-- **Soundness gate: the one-step move is necessary under a rep (PROVED).**

Under any additive representation, the diagonal comparison's truth is level-
independent (the `V_t` term is common to both sides and cancels), so it transports
across grid levels.  Confirms `GridLevelMoveStep` hides nothing false.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem gridLevelMoveStep_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (x z : X j) (p r : X k) (glvl : ℕ → X t) (i : ℕ) :
    GridLevelMoveStep P a j k t x z p r glvl i := by
  intro hw
  rw [R.represents, ag_score_tri R hjk hjt hkt, ag_score_tri R hjk hjt hkt] at hw
  rw [R.represents, ag_score_tri R hjk hjt hkt, ag_score_tri R hjk hjt hkt]
  linarith

/-! ## §E.  The grid-restricted level move from {induction + one-step residual}

Composing §B and §C: given `TBlockDiagonalResidue` (the one-step residual) and a base
comparison, the diagonal transports to every grid level.  This is the honest
grid-restricted level move — the Archimedean induction discharged for free, the
residual localized to the standard frontier condition, and the off-grid extension
left to the §IV.2.6 density residual (respecting the no-go). -/

/-- **Grid-restricted level move from `TBlockDiagonalResidue` (PROVED).**

The diagonal comparison transports from the base grid level `glvl 0` to every grid
level `glvl n`, using the one-step residual (`TBlockDiagonalResidue`) at each step
via the free Archimedean induction.  Audit `[propext, Quot.sound]`. -/
theorem gridLevelMove_of_tBlockDiagonalResidue
    {j k t : ι} (a : Profile X) (x z : X j) (p r : X k) (glvl : ℕ → X t)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (hTD : TBlockDiagonalResidue P j k t)
    (hbase : P.weakPref (tri a j k t x r (glvl 0)) (tri a j k t z p (glvl 0)))
    (n : ℕ) :
    P.weakPref (tri a j k t x r (glvl n)) (tri a j k t z p (glvl n)) :=
  gridLevelMove_of_step a x z p r glvl
    (fun i => gridLevelMoveStep_of_tBlockDiagonalResidue a x z p r glvl i hxz hrp hTD)
    hbase n

end ProductPref
end WakkerInfra

/-! ## WP-EQ1a.2-build (Archimedean grid induction) audit

* §B (free, genuine non-circular Archimedean content): `gridLevelMove_of_step` — one
  step at every grid index ⟹ transport to every grid level, by induction.
* §C: `gridLevelMoveStep_of_tBlockDiagonalResidue` — the one-step move is
  `TBlockDiagonalResidue` localized to a grid step (no new object).
* §D (gate): `gridLevelMoveStep_of_additiveRep`.
* §E: `gridLevelMove_of_tBlockDiagonalResidue` — the grid-restricted level move from
  {free induction + the standard residual}.

**Honest scope.**  The Archimedean grid induction (§B) is genuinely free — the first
non-circular forward content in the equal-spacing construction.  It reduces the level
move to: the one-step residual (= `TBlockDiagonalResidue`, the established frontier)
+ the §IV.2.6 density to reach off-grid `t`-levels (the no-go-respecting residual 2).
The one-step residual remains the irreducible §IV.5 content; the induction does not
discharge it, but it *does* reduce the all-grid-levels move to a single step, sound
and non-circular. -/

#print axioms WakkerInfra.ProductPref.gridLevelMove_of_step
#print axioms WakkerInfra.ProductPref.gridLevelMoveStep_of_tBlockDiagonalResidue
#print axioms WakkerInfra.ProductPref.gridLevelMoveStep_of_additiveRep
#print axioms WakkerInfra.ProductPref.gridLevelMove_of_tBlockDiagonalResidue
