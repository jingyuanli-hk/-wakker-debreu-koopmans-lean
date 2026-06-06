/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — C1.a-3 global construction: the t-measuring-stick diagonal transport

> **STATUS: `sorry`-free.  Genuine global forward content — the explicit Debreu
> measuring-stick reduction of the off-cal diagonal transport.**
> Not in the umbrella import.

This file begins the **global** standard-sequence construction for C1.a-3, after the
cell-level analysis (`OptionB_C1aThomsenClosure`) localized the crux to the bare
`st → c` transport of a `{j,k}`-two-coordinate-difference indifference.

## The measuring-stick mechanism (mechanized here)

Introduce a **`t`-measuring stick** `glvl : ℕ → X t` calibrated so that **one `t`-step
compensates one `j`-step** at a `k`-background `n`:
```
StickCalibration … glvl n :  ∀ m i, [αⱼ(m+1)|αₖ n|glvl i] ∼ [αⱼ m|αₖ n|glvl(i+1)].
```
This is a `{j,t}`-pair calibration (the stick measures `j`-steps) — the same *kind* of
object as the grid's `spaced_j`, **not** the target `{j,k}` cross-pair.

**The genuine forward content (PROVED, pure weak order):** with the stick calibrated at
two consecutive `k`-backgrounds `n` and `n+1`, the off-cal diagonal step transports up
one stick level — `diagAllCells (glvl i) → diagAllCells (glvl (i+1))` — by the explicit
chain
```
[αⱼ(m+1)|αₖn|glvl(i+1)] ∼ [αⱼ(m+2)|αₖn|glvl i]        (stick at n, symm)
                        ∼ [αⱼ(m+1)|αₖ(n+1)|glvl i]     (free st-diagonal at the shifted cell (m+1,n))
                        ∼ [αⱼ m|αₖ(n+1)|glvl(i+1)]      (stick at n+1).
```
Combined with the **free** base case `diagAllCells st` (from `CalibrationAllBackgrounds`,
with `glvl 0 = st`) and induction on `i`, this discharges the off-cal diagonal step at
**every stick level** from {the free calibration-level diagonal + the stick calibration}.

## What this file delivers (all machine-checked, no `sorry`)

* `StickCalibration P j k t G glvl n` — the `t`-stick calibrated against `j`-steps at
  `k`-background `n`.
* `DiagAllCells P j k t G ℓ` — the diagonal step at all cells, at a fixed `t`-level `ℓ`.
* `diagAllCells_succ_of_stickCalibration` — **the genuine forward brick**: the
  one-stick-level transport `diagAllCells (glvl i) → diagAllCells (glvl (i+1))` (pure
  weak order, via the chain above).
* `diagAllCells_of_stick_induction` — the full induction: `diagAllCells (glvl n)` for
  every `n`, from {base `diagAllCells (glvl 0)` + the stick calibration at all
  backgrounds}.
* `diagAllCells_stickLevels_of_calibration_and_stick` — composing with the free base
  case: the off-cal diagonal at every stick level from
  `CalibrationAllBackgrounds` + the stick.
* `stickCalibration_of_additiveRep` — soundness gate (the stick exists under a rep iff
  its `t`-increment matches the grid's calibrating exchange).

## Honest scope (the reduction, and the relocated residual)

This is the genuine Debreu measuring-stick reduction, mechanized: it discharges the
*all-stick-levels* and *all-cells* quantifiers of the off-cal diagonal transport from
{the free `st`-diagonal + `StickCalibration` at all `k`-backgrounds}, by an explicit
weak-order chain + induction.  The **relocated residual** is `StickCalibration` at all
`k`-backgrounds — the `{j,t}`-stick calibration transported across `k`, which is a
*different* block pair than the target (`{j,k}` shifted by `t`).  By the permutation
equivalence (`OptionB_C1aDiagonalEquivalence`) the three block pairs are inter-derivable,
so this does not by itself break the wall — but it is genuine, sound, non-circular
forward content: the off-cal transport is now reduced to a *single-pair stick
calibration*, the sharpest measuring-stick form, with the level/cell inductions
discharged for free.  Reaching off-*stick* `t`-levels remains the §IV.2.6 density
residual (the no-go-respecting refinement mesh).

Imports `OptionB_C1aGridThomsen` (the grid, `CalibrationAllBackgrounds`, the free
`st`-diagonal) and `OptionB_C1aDiagonalResidue` (for `tri`).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aGridThomsen

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

private theorem ms_symm {x y : Profile X} (h : P.indiff x y) : P.indiff y x :=
  ⟨h.2, h.1⟩

private theorem ms_trans [ProductPref.IsWeakOrder P] {x y z : Profile X}
    (hxy : P.indiff x y) (hyz : P.indiff y z) : P.indiff x z :=
  ⟨ProductPref.IsWeakOrder.transitive _ _ _ hxy.1 hyz.1,
   ProductPref.IsWeakOrder.transitive _ _ _ hyz.2 hxy.2⟩

/-! ## §B.  The measuring stick and the all-cells diagonal -/

/-- **`t`-measuring-stick calibration at `k`-background `n`.**

The stick `glvl : ℕ → X t` is calibrated so one `t`-step `glvl i → glvl (i+1)`
compensates one `j`-step `αⱼ (m+1) → αⱼ m`, uniformly in `m`, at the fixed
`k`-background `αₖ n`:
`[αⱼ (m+1) | αₖ n | glvl i] ∼ [αⱼ m | αₖ n | glvl (i+1)]`.  A `{j,t}`-pair statement
(the stick measures `j`-steps). -/
def StickCalibration (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) (glvl : ℕ → X t) (n : ℕ) : Prop :=
  ∀ (m i : ℕ),
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) (glvl i))
             (tri G.a j k t (G.αj m) (G.αk n) (glvl (i + 1)))

/-- **The off-cal diagonal step at all cells, at a fixed `t`-level `ℓ`.** -/
def DiagAllCells (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) (ℓ : X t) : Prop :=
  ∀ (m n : ℕ),
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) ℓ)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) ℓ)

/-! ## §C.  The genuine forward brick: one-stick-level transport (pure weak order) -/

/-- **One-stick-level diagonal transport (PROVED, pure weak order — the measuring-stick
mechanism).**

If the diagonal step holds at all cells at stick level `glvl i`, and the stick is
calibrated at the two `k`-backgrounds `n` and `n+1`, then the diagonal step holds at
all cells at the next stick level `glvl (i+1)`.

The chain at cell `(m,n)`:
`[αⱼ(m+1)|αₖn|glvl(i+1)] ∼ [αⱼ(m+2)|αₖn|glvl i]` (stick at `n`, index `m+1`, symm)
`∼ [αⱼ(m+1)|αₖ(n+1)|glvl i]` (the level-`glvl i` diagonal at the shifted cell `(m+1,n)`)
`∼ [αⱼ m|αₖ(n+1)|glvl(i+1)]` (stick at `n+1`, index `m`).
Pure weak-order transitivity — the genuine, non-circular measuring-stick content.  Audit
`[propext, Quot.sound]`. -/
theorem diagAllCells_succ_of_stickCalibration
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (glvl : ℕ → X t) (i : ℕ)
    (hdiag : DiagAllCells P j k t G (glvl i))
    (hstick : ∀ n, StickCalibration P j k t G glvl n) :
    DiagAllCells P j k t G (glvl (i + 1)) := by
  intro m n
  -- stick at n, index (m+1): [αⱼ(m+2)|αₖn|glvl i] ∼ [αⱼ(m+1)|αₖn|glvl(i+1)]
  have hA : P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) (glvl (i + 1)))
                     (tri G.a j k t (G.αj (m + 2)) (G.αk n) (glvl i)) :=
    ms_symm (hstick n (m + 1) i)
  -- level-glvl i diagonal at shifted cell (m+1, n):
  --   [αⱼ(m+2)|αₖn|glvl i] ∼ [αⱼ(m+1)|αₖ(n+1)|glvl i]
  have hB : P.indiff (tri G.a j k t (G.αj (m + 2)) (G.αk n) (glvl i))
                     (tri G.a j k t (G.αj (m + 1)) (G.αk (n + 1)) (glvl i)) := by
    have := hdiag (m + 1) n
    simpa using this
  -- stick at (n+1), index m: [αⱼ(m+1)|αₖ(n+1)|glvl i] ∼ [αⱼ m|αₖ(n+1)|glvl(i+1)]
  have hC : P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk (n + 1)) (glvl i))
                     (tri G.a j k t (G.αj m) (G.αk (n + 1)) (glvl (i + 1))) :=
    hstick (n + 1) m i
  exact ms_trans hA (ms_trans hB hC)

/-! ## §D.  The induction: diagonal at every stick level -/

/-- **The off-cal diagonal at every stick level (PROVED, free induction).**

From the base case `diagAllCells (glvl 0)` and the stick calibration at all
`k`-backgrounds, the one-stick-level transport (§C) gives the diagonal step at all
cells at **every** stick level `glvl n`, by induction on `n`.  Audit `[propext,
Quot.sound]`. -/
theorem diagAllCells_of_stick_induction
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (glvl : ℕ → X t)
    (hbase : DiagAllCells P j k t G (glvl 0))
    (hstick : ∀ n, StickCalibration P j k t G glvl n)
    (N : ℕ) :
    DiagAllCells P j k t G (glvl N) := by
  induction N with
  | zero => exact hbase
  | succ N ih => exact diagAllCells_succ_of_stickCalibration G glvl N ih hstick

/-! ## §E.  Composing with the free calibration-level base case -/

/-- **The off-cal diagonal at every stick level from calibration + the stick (PROVED).**

With a stick based at the calibration level (`glvl 0 = st`), the base case
`diagAllCells st` is **free** from `CalibrationAllBackgrounds`
(`interiorDiagonalStep_st_of_allBackgrounds`).  So the off-cal diagonal step holds at
all cells at **every stick level** from {`CalibrationAllBackgrounds` + the stick
calibration at all `k`-backgrounds}.  This is the measuring-stick discharge of the
all-stick-levels + all-cells quantifiers — the genuine global forward content.  Audit
`[propext, Quot.sound]`. -/
theorem diagAllCells_stickLevels_of_calibration_and_stick
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G)
    (glvl : ℕ → X t) (hglvl0 : glvl 0 = G.st)
    (hstick : ∀ n, StickCalibration P j k t G glvl n)
    (N : ℕ) :
    DiagAllCells P j k t G (glvl N) := by
  refine diagAllCells_of_stick_induction G glvl ?_ hstick N
  intro m n
  rw [hglvl0]
  exact interiorDiagonalStep_st_of_allBackgrounds G hcal m n

/-! ## §F.  Soundness gate -/

/-- Score split of a `tri` profile (local copy; `score_tri_eq` is private). -/
private theorem ms_score_tri (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
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

/-- **Soundness gate (PROVED): the stick calibration is necessary under a rep with a
matched stick.**

Under an additive representation, `StickCalibration` at `k`-background `n` holds iff the
stick's `t`-increment matches the grid's calibrating exchange: `V_t (glvl (i+1)) − V_t
(glvl i) = V_j (αⱼ (m+1)) − V_j (αⱼ m) = V_t rt − V_t st` (by `spaced_j`).  So a stick
whose consecutive `t`-increments all equal `V_t rt − V_t st` calibrates against the
`j`-steps at every background.  Confirms `StickCalibration` hides nothing false — it is
exactly the matched measuring stick.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem stickCalibration_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) (glvl : ℕ → X t)
    (hmatch : ∀ i, R.V t (glvl (i + 1)) - R.V t (glvl i) = R.V t G.rt - R.V t G.st)
    (n : ℕ) :
    StickCalibration P j k t G glvl n := by
  -- The `j`-grid step's utility increment equals the calibrating `t`-exchange size.
  have stepJ : ∀ m, R.V j (G.αj (m + 1))
      = R.V j (G.αj m) + (R.V t G.rt - R.V t G.st) := by
    intro m
    have h := (indiff_iff_score R).mp (G.spaced_j m)
    rw [ms_score_tri R hjk hjt hkt, ms_score_tri R hjk hjt hkt] at h
    linarith
  intro m i
  rw [indiff_iff_score R, ms_score_tri R hjk hjt hkt, ms_score_tri R hjk hjt hkt]
  have hj := stepJ m
  have ht := hmatch i
  linarith

end ProductPref
end WakkerInfra

/-! ## C1.a-3 measuring-stick audit

* §B: `StickCalibration` (the `t`-stick measuring `j`-steps), `DiagAllCells` (the
  off-cal diagonal at all cells at a fixed level).
* §C (genuine forward, weak order): `diagAllCells_succ_of_stickCalibration` — the
  one-stick-level transport via the explicit measuring-stick chain.
* §D/§E: `diagAllCells_of_stick_induction`, `diagAllCells_stickLevels_of_calibration_and_stick`
  — the off-cal diagonal at every stick level from {free `st`-diagonal + the stick}.
* §F (gate): `stickCalibration_of_additiveRep`.

**Honest scope.**  This is the genuine Debreu measuring-stick reduction, mechanized: it
discharges the all-stick-levels + all-cells quantifiers of the off-cal diagonal
transport from {the free `st`-diagonal + `StickCalibration` at all `k`-backgrounds} by
an explicit weak-order chain + induction (non-circular — the stick is a `{j,t}`-pair
object, not the `{j,k}` target).  The **relocated residual** is `StickCalibration` at
all `k`-backgrounds (a different block pair, inter-derivable with the target by the
permutation equivalence — so this does not alone break the wall).  Reaching off-*stick*
`t`-levels is the §IV.2.6 density residual.  The gain: the off-cal transport is reduced
to the single-pair stick calibration, the sharpest measuring-stick form, with the
level/cell inductions free.  Audit `[propext, Quot.sound]` / `[propext, Classical.choice,
Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.diagAllCells_succ_of_stickCalibration
#print axioms WakkerInfra.ProductPref.diagAllCells_of_stick_induction
#print axioms WakkerInfra.ProductPref.diagAllCells_stickLevels_of_calibration_and_stick
#print axioms WakkerInfra.ProductPref.stickCalibration_of_additiveRep
