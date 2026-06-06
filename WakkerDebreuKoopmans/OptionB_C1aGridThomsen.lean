/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 grid-Thomsen step  (`sorry`-free reduction to named §IV.5/§IV.2.6 inputs)

> **✅ STATUS: `sorry`-free forward-construction reduction for the R1.1 crux.**
> This module is **`sorry`-free** (`0` errors / `0` `sorry` / `0` `sorryAx`,
> verified by `lake env lean` on the single module).  It is deliberately **NOT**
> in the umbrella import and **NOT** yet merged into `OptionB_AxiomCheck.lean`
> (pending review).  The full per-declaration status is tabulated in
> `OptionB_C1aGridThomsenStatusTable.md`.
>
> Both former open obligations have been discharged by the genuine Wakker §IV.5 /
> §IV.2.6 measuring-stick construction, relocating their content to explicit,
> necessity-proven **named inputs** (not hidden gaps):
>
> 1. **Off-axis calibration one-step shift**
>    (`calibrationOffAxisOneStep_of_calibratedGrid`) — now a **theorem** delegating
>    to `calibrationOffAxisOneStep_of_topology_and_forwardData`.  Its content is
>    split into a theorem-backed continuum/IVT existence half (from the standard
>    `WakkerCoordinateTopology` bundle) plus the named `CalibrationOffAxisForwardData`
>    (the §IV.2.6 reach brackets + the two cross-pair *matching* residuals
>    `matchJ`/`matchK`); necessity: `calibrationOffAxisForwardData_of_additiveRep`.
> 2. **Off-cal diagonal level move** (`gridDiagonalStepOffCal_of_calibratedGrid`) —
>    now a **theorem** taking the genuine §IV.5/§IV.2.6 inputs explicitly (§D.3f–h):
>    * the continuum/IVT content is theorem-backed from the standard
>      `WakkerCoordinateTopology` bundle — connectedness of `X t` + preference
>      continuity discharge the crossing that produces the compensating reference
>      `t`-level (`offCalJHalf_of_IVT`, `offCalJHalf_of_topology_and_bracket`, audit
>      `[propext, Classical.choice, Quot.sound]`);
>    * the §IV.2.6 Archimedean reach enters as the named `OffCalJBracket`
>      (necessary under a rep, `offCalJBracket_of_additiveRep`; itself dischargeable
>      from an escape grid by pure order theory, `offCalJBracket_of_escapeGrid`);
>    * the **single** genuine cross-pair residual is `OffCalCompensationMatch` —
>      that the `j`-compensating level also compensates the `k`-step.  This is the
>      equal-spacing / double-cancellation content: necessary under a rep
>      (`offCalCompensationMatch_of_additiveRep`), not A1-derivable (the strip
>      probe), and not residue-derivable (§D.2b is circular).  It is characterized
>      as no stronger than canonical KLST `t`-block separability
>      (`offCalCompensationMatch_of_calibration_and_tBlock`).
>
> So the headline closure `gridThomsenClosure_of_calibratedGrid` (and its frontier
> form `gridThomsenClosure_of_frontier` / `gridTBlockDiagonalResidue_of_frontier`)
> is theorem-backed at `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**
> — modulo the named, proven-necessary §IV.5/§IV.2.6 inputs.  The genuinely-open
> research content is unchanged and is exactly those inputs: the cross-pair
> *matching* (equal-spacing / KLST `t`-block separability) residuals and the
> §IV.2.6 escape/density content — not derivable from single-coordinate A1 (the
> probes), and the full standard-sequence equal-spacing construction that would
> *eliminate* (rather than characterize + soundness-gate) the matching residuals
> remains the research crux.
>
> Earlier sharpening bricks (prior sessions) — still in force:
>
> 1. **All-background calibration** factors as {axis cases (free, `rfl`) +
>    interior cases (residual)}: `calJ m 0 = G.spaced_j m` and
>    `calK 0 n = G.spaced_k n` are *literally* the calibrated grid's own data, so
>    only the strictly-positive-off-axis cases need a forward proof.  Captured by
>    `CalibrationInteriorBackgrounds`; the composition theorem is
>    `calibrationAllBackgrounds_of_axisCases_and_interior` (proved).  The interior
>    cases then reduce further (§D.3a-onestep) to a single atomic *off-axis
>    one-step shift* `CalibrationOffAxisOneStep`: the arbitrary off-axis jump is
>    discharged by a free induction (`calibrationInteriorBackgrounds_of_offAxisOneStep`)
>    with `spaced_j`/`spaced_k` as the base case.
>
> 2. **Diagonal step level move** factors as {calibration-level case (free given
>    calibration, via `interiorDiagonalStep_st_of_allBackgrounds`) + level-move
>    residual}: at `c = G.st` the diagonal step holds by pure weak order; the
>    open content is only the move from `G.st` to other `t`-levels.  Captured by
>    `GridDiagonalLevelMoveResidual`; the composition theorem is
>    `gridDiagonalStep_of_calibration_and_levelMove` (proved).
>
> 3. **Diagonal step at level `rt` is also free, given interior calibration.**
>    The two halves of the interior calibration share their right-hand profile
>    `(αⱼ (m+1), αₖ (n+1), st)`, so symm + trans give the diagonal step at level
>    `rt` for *all* `(m, n)` indices (`interiorDiagonalStep_rt_of_interiorBackgrounds`,
>    proved).  Hence the level-move residual narrows further to a sharper *off-cal*
>    residual `GridDiagonalLevelMoveResidualOffCal` open only at `c ∉ {rt, st}`,
>    bridged by `gridDiagonalLevelMoveResidual_of_offCalResidual` (proved, uses
>    `Classical.em` for the level-decision case split).
>
> 4. **Level move premise-free relocation (prior session), now fully discharged
>    (this session).**  The premise-laden `gridDiagonalLevelMoveResidual_of_calibratedGrid`
>    and the packaged `diagonalStepLevelMove_of_calibratedGrid` were first reduced
>    (§D.3e-crux) to the premise-free `gridDiagonalStepOffCal_of_calibratedGrid`
>    via the proved bridge `gridDiagonalLevelMoveResidual_of_offCalStep`; this
>    session that residual is itself discharged (§D.3f–h), so the whole level-move
>    chain is `sorry`-free modulo the two named inputs (`OffCalJBracket`,
>    `OffCalCompensationMatch`).
>
> All new residuals are proved necessary under a representation
> (`calibrationOffAxisOneStep_of_additiveRep`,
> `gridDiagonalStepOffCal_of_additiveRep`, `offCalJBracket_of_additiveRep`,
> `offCalCompensationMatch_of_additiveRep`, `matchedOffCalCompensation_of_additiveRep`)
> — soundness gates clean.  No `sorry` remains anywhere in the module.
>
> **Honest finding (this session): the original "bare structural axioms ⟹
> calibrated grid" wrapper is unprovable as stated.**  `WakkerCoordinateTopology P`
> is *not* derivable from `Essential` + `RestrictedSolvability` + `Archimedean`
> alone (per `RawAxiomDischargersTopology.lean` §5: the project itself carries the
> topology bundle as an explicit data input).  The bare wrapper has been
> reformulated to take the topology bundle in its signature, matching the
> project-wide convention; it is now a theorem (no `sorry`).
>
> **Key honest finding (§D.2b).**  The grid-Thomsen route does **not** bypass the
> cross-pair content: `gridDiagonalStep_of_diagonalResidues` proves the grid
> diagonal step (hence the whole closure) is **inter-derivable** with the existing
> cross-pair diagonal residues `{K, J, T}`-diag.  Off-axis calibration *is* the
> `K`/`J`-diag content; the level move *is* `T`-diag.  Since those are
> permutation-equivalent to R1.1's target Thomsen residue, deriving the closure
> from them is **circular**.  So the grid route adds value only as a *repackaging*
> of the open content into the calibrated-grid vocabulary — the genuinely-open
> work (deriving one Thomsen residue from restricted solvability + the third
> coordinate, NOT from the other residues) is unchanged.
>
> **R1.1a reduction (§E).**  The calibrated-grid construction is reduced to a
> single named seed-data residual `CalibratedGridSeedData` (the two `t`-calibrated
> standard-sequence extenders).  The grid **assembly** (`calibratedJKGrid_of_seedData`)
> and **injectivity** (`gridJ/K_injective_of_strictSteps`, inline order theory) are
> fully theorem-backed; the extender shape is proved necessary under a rep
> (`calibratedGridSeedData_extenders_of_additiveRep`); the seam is discharged from
> `WakkerCoordinateTopology` + `RestrictedSolvability`
> (`calibratedOneStepSeam_of_topology`); and the structural-axioms-plus-topology
> wrapper is theorem-backed (`calibratedJKGrid_of_structuralAxioms_and_topology`,
> `calibratedJKGrid_of_structuralAxioms`).
>
> Both former `sorry`s are now discharged; the honest claim is the Option A⁺
> reduction of R1.1 to the named §IV.5/§IV.2.6 inputs (the cross-pair matching
> residuals + the escape/density content), each soundness-gated and
> non-A1-derivable.

## What this file is for

The whole Option B construction is now reduced (per
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`) to a **single**
Thomsen-type residue `TBlockDiagonalResidue P j k t` (at three coordinate-role
permutations), with everything else theorem-backed.  This file targets that
residue through Wakker's **§IV.5 standard-sequence grid Thomsen** route (Debreu
1960; KLST 1971 Thm 6.2): build two interlocking standard sequences in `j` and
`k`, both calibrated against the same reference exchange in the measuring-stick
coordinate `t`, and prove that on the resulting grid the {j,k}-comparison is
governed by the index sum — the *equal-spacing / double-cancellation closure*.

## The honest decomposition (matches the roadmap's R1.1a / R1.1b / R1.2)

1. **`CalibratedJKGrid`** — the data of the two interlocking standard sequences
   (Wakker's measuring-stick setup).
2. **`GridThomsenClosure`** — the precise grid-level target: the *anti-diagonal*
   grid indifference `(αⱼ m, αₖ n) ∼ (αⱼ m', αₖ n')` whenever `m + n = m' + n'`,
   at every `t`-level.  This is the genuine equal-spacing content.
3. **Soundness gate (PROVED): `gridThomsenClosure_of_additiveRep`** — the closure
   is *necessary* under any additive representation (the calibration forces equal
   utility steps in `j` and `k`, so the anti-diagonal sums match).  This is the
   mandatory gate: it confirms the forward target is true before any effort is
   spent, exactly as the §5 / WP-CI / WP-density discipline requires.
4. **Bridge (PROVED): `gridTBlockDiagonalResidue_of_closure`** — the closure plus
   single-coordinate independence A1 on `j` yields the *grid-restricted*
   `TBlockDiagonalResidue` (t-level invariance of the {j,k}-comparison on grid
   points).  This shows the closure is exactly the right target: it feeds the
   residue.
5. **R1.1b (theorem-backed mod named inputs): `gridThomsenClosure_of_calibratedGrid`**
   — the combinatorial crux: derive the closure from the calibrated grid + weak
   order + the named §IV.5/§IV.2.6 forward inputs, by double cancellation.  The
   order theory, free calibration cases, and continuum/IVT existence are all
   theorem-backed; the genuinely-irreducible Wakker §IV.5 content is isolated as
   the named cross-pair matching residuals (the probes confirm A1 alone is
   insufficient).
6. **R1.1a (theorem-backed mod topology bundle): `calibratedJKGrid_of_structuralAxioms`**
   — construct the calibrated grid from `Essential` + `RestrictedSolvability` +
   `Archimedean` + the `WakkerCoordinateTopology` bundle (the measuring-stick
   existence).  The grid assembly and injectivity are theorem-backed; the seam is
   discharged from the topology bundle + solvability.
7. **R1.2 (mechanized in `OptionB_C1aGridTransport.lean`): transport** — lift the
   grid-restricted residue to all profiles.  Reduced — by pure weak order — to a
   single named level-stable grid-coverage residual `StableGridIndifferentCover`
   (the §IV.2.6 density content), with the transport itself theorem-backed
   (`tBlockDiagonalResidue_of_gridRestricted_and_stableCover`).

Imports `OptionB_C1aDiagonalResidue` (for `tri`, `TBlockDiagonalResidue`,
`tBlockWeakIndependentRestrictedJ_of_a1`, `CoordinateOrderIndependent`) and
`OptionB_CoordinateIndependence` (for `indiff_iff_score`).
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalResidue
import WakkerDebreuKoopmans.OptionB_CoordinateIndependence
import WakkerDebreuKoopmans.RawAxiomDischargersTopology

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

/-! ## §A.  The calibrated {j,k,t} grid (Wakker's interlocking standard sequences) -/

/-- **Calibrated `{j,k}` grid against the measuring-stick coordinate `t`.**

Two standard sequences — `αⱼ : ℕ → X j` and `αₖ : ℕ → X k` — over a common
background `a`, both calibrated against the **same** reference exchange
`rt ↦ st` in the third coordinate `t`:

* `spaced_j n` : moving `j` one grid step (`αⱼ n → αⱼ (n+1)`) is compensated by
  moving `t` from `rt` to `st` (with `k` held at `αₖ 0`);
* `spaced_k n` : moving `k` one grid step (`αₖ n → αₖ (n+1)`) is compensated by
  the *same* `t`-exchange `rt → st` (with `j` held at `αⱼ 0`).

Because both sequences are calibrated against the **same** `t`-exchange, their
grid steps carry the same "tradeoff unit": under an additive representation this
is exactly the statement that `V_j` and `V_k` increase by the same amount
`V_t rt − V_t st` per grid step.  This is Wakker's measuring-stick construction
(the third coordinate `t` calibrates the `j`- and `k`-grids to a common scale). -/
structure CalibratedJKGrid (P : ProductPref X) (j k t : ι) where
  /-- Common background profile. -/
  a    : Profile X
  /-- The `j`-coordinate grid points. -/
  αj   : ℕ → X j
  /-- The `k`-coordinate grid points. -/
  αk   : ℕ → X k
  /-- Reference `t`-value (the "from" of the calibrating exchange). -/
  rt   : X t
  /-- Reference `t`-value (the "to" of the calibrating exchange). -/
  st   : X t
  /-- `j`-steps are calibrated against the `t`-exchange `rt → st`. -/
  spaced_j : ∀ n,
    P.indiff (tri a j k t (αj n)     (αk 0) rt)
             (tri a j k t (αj (n+1)) (αk 0) st)
  /-- `k`-steps are calibrated against the *same* `t`-exchange `rt → st`. -/
  spaced_k : ∀ n,
    P.indiff (tri a j k t (αj 0) (αk n)     rt)
             (tri a j k t (αj 0) (αk (n+1)) st)

/-- **Grid Thomsen closure (the precise R1.1 grid-level target).**

On a calibrated grid, the `{j,k}`-comparison is governed by the **index sum**:
any two grid profiles with equal `j`+`k` index sum are indifferent, at *every*
`t`-level `c`.  This is the equal-spacing / double-cancellation content — the
anti-diagonal indifference that closes the §IV.5 measuring-stick argument. -/
def GridThomsenClosure (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ (m n m' n' : ℕ) (c : X t), m + n = m' + n' →
    P.indiff (tri G.a j k t (G.αj m)  (G.αk n)  c)
             (tri G.a j k t (G.αj m') (G.αk n') c)

/-! ## §B.  Soundness gate (PROVED) — the closure is necessary under a rep

The mandatory derivability gate: before attempting the forward proof, confirm the
target is *true under a representation* (so the multi-week effort is not spent on
a false statement).  Here the calibration `spaced_j` / `spaced_k` forces the
per-step utility increments in `j` and `k` to equal the common `t`-exchange gap
`δ = V_t rt − V_t st`; hence `V_j (αⱼ m) = V_j (αⱼ 0) + m·δ` and
`V_k (αₖ n) = V_k (αₖ 0) + n·δ`, so equal index sums give equal scores. -/

/-- **Score of a `tri` profile** over a fixed background (additive split).

`∑ R.V i (tri a j k t u v c i) = R.V j u + R.V k v + R.V t c + (off-block rest)`.
Reusable engine for the necessity / soundness-gate proofs in this file. -/
private theorem score_tri_eq (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (u : X j) (v : X k) (c : X t) :
    (∑ i, R.V i (tri a j k t u v c i))
      = R.V j u + R.V k v + R.V t c
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
  have hj : (Function.update (Function.update (Function.update a j u) k v) t c) j = u := by
    rw [Function.update_of_ne hjt, Function.update_of_ne hjk, Function.update_self]
  have hk : (Function.update (Function.update (Function.update a j u) k v) t c) k = v := by
    rw [Function.update_of_ne hkt, Function.update_self]
  have ht : (Function.update (Function.update (Function.update a j u) k v) t c) t = c := by
    rw [Function.update_self]
  rw [hj, hk, ht]
  have hrest : (∑ i ∈ ((Finset.univ.erase j).erase k).erase t,
        R.V i (Function.update (Function.update (Function.update a j u) k v) t c i))
      = ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hit : i ≠ t := Finset.ne_of_mem_erase hi
    have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hij : i ≠ j :=
      Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
    rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij]
  rw [hrest]; ring

/-- **Soundness gate: `GridThomsenClosure` is necessary under any additive
representation.**  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridThomsenClosure_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) :
    GridThomsenClosure P j k t G := by
  -- The common per-step utility increment.
  set δ : ℝ := R.V t G.rt - R.V t G.st with hδ
  -- One `j`-step raises `V_j` by `δ` (from `spaced_j`).
  have stepJ : ∀ n, R.V j (G.αj (n+1)) = R.V j (G.αj n) + δ := by
    intro n
    have h := (indiff_iff_score R).mp (G.spaced_j n)
    rw [score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at h
    linarith
  -- One `k`-step raises `V_k` by the same `δ` (from `spaced_k`).
  have stepK : ∀ n, R.V k (G.αk (n+1)) = R.V k (G.αk n) + δ := by
    intro n
    have h := (indiff_iff_score R).mp (G.spaced_k n)
    rw [score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at h
    linarith
  -- Closed forms: arithmetic progressions in the grid index.
  have closedJ : ∀ m, R.V j (G.αj m) = R.V j (G.αj 0) + (m : ℝ) * δ := by
    intro m
    induction m with
    | zero => simp
    | succ n ih => rw [stepJ n, ih]; push_cast; ring
  have closedK : ∀ n, R.V k (G.αk n) = R.V k (G.αk 0) + (n : ℝ) * δ := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [stepK m, ih]; push_cast; ring
  -- Equal index sums ⇒ equal scores ⇒ indifference.
  intro m n m' n' c hmn
  have hcast : (m : ℝ) + n = (m' : ℝ) + n' := by exact_mod_cast hmn
  have key : (m : ℝ) * δ + (n : ℝ) * δ = (m' : ℝ) * δ + (n' : ℝ) * δ := by
    calc (m : ℝ) * δ + (n : ℝ) * δ = ((m : ℝ) + n) * δ := by ring
      _ = ((m' : ℝ) + n') * δ := by rw [hcast]
      _ = (m' : ℝ) * δ + (n' : ℝ) * δ := by ring
  rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt,
      closedJ m, closedK n, closedJ m', closedK n']
  linarith [key]

/-! ## §C.  Bridge (PROVED) — closure ⟹ grid-restricted `TBlockDiagonalResidue`

The closure feeds the residue: with single-coordinate independence A1 on `j`, the
anti-diagonal indifferences collapse the `{j,k}`-comparison to a pure `j`-grid
comparison, on which moving the `t`-level is an A1-absorbed background change.
This confirms the closure is exactly the right grid-level target. -/

/-- **Closure ⟹ grid-restricted diagonal residue.**

On the calibrated grid, the closure plus A1 on `j` gives the `t`-level invariance
of the `{j,k}`-comparison (the grid restriction of `TBlockDiagonalResidue`): if
the grid profiles `(αⱼ m, αₖ n)` and `(αⱼ m', αₖ n')` compare a certain way at
`t`-level `w`, they compare the same way at any other level `c`.

Proof: by the closure, `(αⱼ m, αₖ n, ·) ∼ (αⱼ (m+n), αₖ 0, ·)` and similarly for
the primed pair, at every `t`-level.  So the comparison reduces to the pure
`j`-grid comparison `(αⱼ (m+n), αₖ 0, ·)` vs `(αⱼ (m'+n'), αₖ 0, ·)`, which moves
across `t`-levels by A1 on `j` (`tBlockWeakIndependentRestrictedJ_of_a1`).  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem gridTBlockDiagonalResidue_of_closure
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (G : CalibratedJKGrid P j k t)
    (hcl : GridThomsenClosure P j k t G)
    (m n m' n' : ℕ) (w c : X t)
    (hw : P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  w)
                     (tri G.a j k t (G.αj m') (G.αk n') w)) :
    P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  c)
               (tri G.a j k t (G.αj m') (G.αk n') c) := by
  -- Collapse each pair to a pure `j`-grid profile via the closure, at level `w`.
  have e1w : P.indiff (tri G.a j k t (G.αj m) (G.αk n) w)
                      (tri G.a j k t (G.αj (m+n)) (G.αk 0) w) :=
    hcl m n (m+n) 0 w (by omega)
  have e2w : P.indiff (tri G.a j k t (G.αj m') (G.αk n') w)
                      (tri G.a j k t (G.αj (m'+n')) (G.αk 0) w) :=
    hcl m' n' (m'+n') 0 w (by omega)
  -- Transport `hw` to the pure `j`-grid comparison at level `w`.
  have hjw : P.weakPref (tri G.a j k t (G.αj (m+n)) (G.αk 0) w)
                        (tri G.a j k t (G.αj (m'+n')) (G.αk 0) w) :=
    ProductPref.IsWeakOrder.transitive _ _ _
      (ProductPref.IsWeakOrder.transitive _ _ _ e1w.2 hw) e2w.1
  -- Move the `t`-level `w → c` on the pure `j`-grid comparison by A1 on `j`.
  have hjc : P.weakPref (tri G.a j k t (G.αj (m+n)) (G.αk 0) c)
                        (tri G.a j k t (G.αj (m'+n')) (G.αk 0) c) :=
    tBlockWeakIndependentRestrictedJ_of_a1 hjk hjt hA1j G.a
      (G.αj (m+n)) (G.αj (m'+n')) (G.αk 0) w c hjw
  -- Collapse back to the original profiles via the closure, at level `c`.
  have e1c : P.indiff (tri G.a j k t (G.αj m) (G.αk n) c)
                      (tri G.a j k t (G.αj (m+n)) (G.αk 0) c) :=
    hcl m n (m+n) 0 c (by omega)
  have e2c : P.indiff (tri G.a j k t (G.αj m') (G.αk n') c)
                      (tri G.a j k t (G.αj (m'+n')) (G.αk 0) c) :=
    hcl m' n' (m'+n') 0 c (by omega)
  exact ProductPref.IsWeakOrder.transitive _ _ _
    (ProductPref.IsWeakOrder.transitive _ _ _ e1c.1 hjc) e2c.2

/-! ## §D.  R1.1b — reducing the closure to a single diagonal step

The whole equal-index-sum closure reduces, by **pure order theory**, to the
single **diagonal-step primitive** `(αⱼ (m+1), αₖ n) ∼ (αⱼ m, αₖ (n+1))` at each
`t`-level (trading one `j`-step for one `k`-step preserves indifference).  This is
the same reduction `RawAxiomDischargersHexagon.grid_indiff_of_eqSum_of_diagonalStep`
already established generically; we reproduce the tiny generic engine here so the
scaffold stays self-contained (the duplication is intentional and flagged).

After this reduction, the genuine §IV.5 content is *only* the diagonal step.  We
then prove its **base cell** at the calibration level outright, and isolate the
remaining open piece (interior steps + level invariance) as
`gridDiagonalStep_of_calibratedGrid`. -/

/-- Reflexivity of indifference (weak-order completeness).  Local copy of the
proved `RawAxiomDischargersHexagon.indiff_refl`. -/
private theorem gridThomsen_indiff_refl
    [ProductPref.IsWeakOrder P] (x : Profile X) : P.indiff x x := by
  refine ⟨?_, ?_⟩ <;>
    · rcases ProductPref.IsWeakOrder.complete (P := P) x x with h | h <;> exact h

/-- Symmetry of indifference. -/
private theorem gridThomsen_indiff_symm {x y : Profile X}
    (h : P.indiff x y) : P.indiff y x := ⟨h.2, h.1⟩

/-- Transitivity of indifference (weak-order transitivity). -/
private theorem gridThomsen_indiff_trans
    [ProductPref.IsWeakOrder P] {x y z : Profile X}
    (hxy : P.indiff x y) (hyz : P.indiff y z) : P.indiff x z :=
  ⟨ProductPref.IsWeakOrder.transitive _ _ _ hxy.1 hyz.1,
   ProductPref.IsWeakOrder.transitive _ _ _ hyz.2 hxy.2⟩

/-- **Diagonal collapse to the axis** (local copy of the proved generic engine).
From the diagonal step `g (a+1) b ∼ g a (b+1)`, every `g a b` is indifferent to
the axis point `g (a+b) 0`. -/
private theorem gridThomsen_axis_of_diagonalStep
    [ProductPref.IsWeakOrder P] (g : ℕ → ℕ → Profile X)
    (hdiag : ∀ a b, P.indiff (g (a + 1) b) (g a (b + 1))) :
    ∀ a b, P.indiff (g a b) (g (a + b) 0) := by
  intro a b
  induction b generalizing a with
  | zero => simpa using gridThomsen_indiff_refl (g a 0)
  | succ b ih =>
      have hstep : P.indiff (g a (b + 1)) (g (a + 1) b) :=
        gridThomsen_indiff_symm (hdiag a b)
      have hih : P.indiff (g (a + 1) b) (g (a + 1 + b) 0) := ih (a + 1)
      have hcomp : P.indiff (g a (b + 1)) (g (a + 1 + b) 0) :=
        gridThomsen_indiff_trans hstep hih
      have he : a + 1 + b = a + (b + 1) := by omega
      rwa [he] at hcomp

/-- **Equal-index-sum indifference from the diagonal step** (local copy of the
proved generic engine). -/
private theorem gridThomsen_eqSum_of_diagonalStep
    [ProductPref.IsWeakOrder P] (g : ℕ → ℕ → Profile X)
    (hdiag : ∀ a b, P.indiff (g (a + 1) b) (g a (b + 1)))
    {a b a' b' : ℕ} (hsum : a + b = a' + b') :
    P.indiff (g a b) (g a' b') := by
  have h1 := gridThomsen_axis_of_diagonalStep g hdiag a b
  have h2 := gridThomsen_axis_of_diagonalStep g hdiag a' b'
  rw [← hsum] at h2
  exact gridThomsen_indiff_trans h1 (gridThomsen_indiff_symm h2)

/-- **The grid diagonal-step primitive (the sharpened R1.1b target).**

At every `t`-level `c`, trading one `j`-grid step for one `k`-grid step preserves
indifference:
`(αⱼ (m+1), αₖ n, c) ∼ (αⱼ m, αₖ (n+1), c)`.

By the order-theory reduction below, this single statement implies the entire
`GridThomsenClosure`.  It is the precise irreducible §IV.5 double-cancellation
content (the probes confirm A1 alone does not give it). -/
def GridDiagonalStep (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ (m n : ℕ) (c : X t),
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n)     c)
             (tri G.a j k t (G.αj m)       (G.αk (n + 1)) c)

/-- **R1.1b reduction (PROVED): the closure from the diagonal step.**

Pure order theory: for each fixed `t`-level `c`, the diagonal step is exactly the
hypothesis of the generic equal-sum engine, applied to the grid
`(a,b) ↦ (αⱼ a, αₖ b, c)`.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridThomsenClosure_of_gridDiagonalStep
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hstep : GridDiagonalStep P j k t G) :
    GridThomsenClosure P j k t G := by
  intro m n m' n' c hsum
  exact gridThomsen_eqSum_of_diagonalStep
    (fun a b => tri G.a j k t (G.αj a) (G.αk b) c)
    (fun a b => hstep a b c) hsum

/-- **Soundness gate for the diagonal step (PROVED): necessary under a rep.**

Immediate from `gridThomsenClosure_of_additiveRep` (the diagonal step is the
equal-sum case `(m+1) + n = m + (n+1)`).  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem gridDiagonalStep_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) :
    GridDiagonalStep P j k t G := by
  intro m n c
  exact gridThomsenClosure_of_additiveRep R hjk hjt hkt G (m + 1) n m (n + 1) c
    (by omega)

/-- **Base-cell hexagon (PROVED): the diagonal step at `(m,n) = (0,0)` and the
calibration level `st`.**

This is the smallest genuine brick of R1.1b, and it needs **only weak order** —
no A1, no solvability.  Chain `spaced_j 0` and `spaced_k 0`, which share the left
endpoint `(αⱼ 0, αₖ 0, rt)`:

* `spaced_j 0` :  `(αⱼ 0, αₖ 0, rt) ∼ (αⱼ 1, αₖ 0, st)`,
* `spaced_k 0` :  `(αⱼ 0, αₖ 0, rt) ∼ (αⱼ 0, αₖ 1, st)`,

so by symmetry + transitivity `(αⱼ 1, αₖ 0, st) ∼ (αⱼ 0, αₖ 1, st)`.

What this establishes: the diagonal step holds **at the calibration level `st`**
for the base cell, from the calibration data alone.  What it does **not** give
(and what the open lemma below must supply) is (i) the same step at *other*
`t`-levels `c ≠ st` — the genuinely diagonal `t`-level move, which the strip
probe shows is not A1-free — and (ii) the *interior* steps `(m,n) ≠ (0,0)`,
where `spaced_j m` and `spaced_k n` no longer share an endpoint and genuine
double cancellation is required.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem baseCell_diagonalStep_at_calibrationLevel
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) :
    P.indiff (tri G.a j k t (G.αj 1) (G.αk 0) G.st)
             (tri G.a j k t (G.αj 0) (G.αk 1) G.st) := by
  have h := gridThomsen_indiff_trans
    (gridThomsen_indiff_symm (G.spaced_j 0)) (G.spaced_k 0)
  simpa using h

/-! ### §D.2  Interior step at level `st` — reduced to all-background calibration

The base cell was free because `spaced_j 0` and `spaced_k 0` share the endpoint
`(αⱼ 0, αₖ 0, rt)`.  The *interior* step
`(αⱼ (m+1), αₖ n, st) ∼ (αⱼ m, αₖ (n+1), st)` is not free for the reason it is
interesting: `spaced_j m` lives at the `k`-background `αₖ 0`, `spaced_k n` at the
`j`-background `αⱼ 0`, and for `(m,n) ≠ (0,0)` these no longer meet at a common
profile, so plain transitivity does not close the hexagon.

Working the chain honestly isolates the **exact** missing ingredient: the
calibrating exchange `rt → st` must be an indifference at *every* grid background
`(αⱼ m, αₖ n)`, not just on the axes.  Once that holds, the interior step is again
pure weak order.  This is the genuine cross-pair / block-independence content the
probes (`OptionB_C1aKzProbe`, `OptionB_C1aStripProbe`) show A1 does not supply. -/

/-- **All-background calibration.**

The `{j,t}` and `{k,t}` calibrating exchanges `rt → st` are indifferences at
*every* grid background `(αⱼ m, αₖ n)`:

* `calJ m n` : `(αⱼ m, αₖ n, rt) ∼ (αⱼ (m+1), αₖ n, st)`  (the `j`-step is a
  `t`-compensated unit at *any* `k`-background — generalizes `spaced_j`, the
  `n = 0` slice);
* `calK m n` : `(αⱼ m, αₖ n, rt) ∼ (αⱼ m, αₖ (n+1), st)`  (the `k`-step at *any*
  `j`-background — generalizes `spaced_k`, the `m = 0` slice).

Under a representation this holds because the off-axis background utility cancels
(`calibrationAllBackgrounds_of_additiveRep`); it is *not* A1-free (the probes). -/
structure CalibrationAllBackgrounds (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop where
  /-- The `{j,t}` calibration unit holds at every `k`-background. -/
  calJ : ∀ m n, P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
                         (tri G.a j k t (G.αj (m+1)) (G.αk n) G.st)
  /-- The `{k,t}` calibration unit holds at every `j`-background. -/
  calK : ∀ m n, P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
                         (tri G.a j k t (G.αj m) (G.αk (n+1)) G.st)

/-- **Soundness gate: all-background calibration is necessary under a rep.**

`spaced_j m` already forces the `j`-step to equal `δ = V_t rt − V_t st`
independently of the `k`-background (the off-axis `V_k (αₖ n)` cancels), and dually
for `k`.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem calibrationAllBackgrounds_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) :
    CalibrationAllBackgrounds P j k t G := by
  refine ⟨?_, ?_⟩
  · intro m n
    have h := (indiff_iff_score R).mp (G.spaced_j m)
    rw [score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at h
    rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
    linarith
  · intro m n
    have h := (indiff_iff_score R).mp (G.spaced_k n)
    rw [score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at h
    rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
    linarith

/-- **Interior diagonal step at level `st` from all-background calibration
(PROVED).**

For *every* `(m,n)`, the diagonal step holds at the calibration level `st`:
`(αⱼ (m+1), αₖ n, st) ∼ (αⱼ m, αₖ (n+1), st)`.  `calJ m n` and `calK m n` share the
endpoint `(αⱼ m, αₖ n, rt)`, so symmetry + transitivity closes it — **pure weak
order**, no A1, no solvability.  At `(m,n) = (0,0)` this recovers
`baseCell_diagonalStep_at_calibrationLevel` (with `calJ 0 0 = spaced_j 0`,
`calK 0 0 = spaced_k 0`).  Audit `[propext, Quot.sound]`. -/
theorem interiorDiagonalStep_st_of_allBackgrounds
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G) (m n : ℕ) :
    P.indiff (tri G.a j k t (G.αj (m+1)) (G.αk n) G.st)
             (tri G.a j k t (G.αj m) (G.αk (n+1)) G.st) :=
  gridThomsen_indiff_trans
    (gridThomsen_indiff_symm (hcal.calJ m n)) (hcal.calK m n)

/-! ### §D.2b  Convergence with the cross-pair diagonal residues (PROVED)

Tracing the off-axis calibration honestly reveals it is **exactly** the cross-pair
diagonal-residue content, not a free solvability consequence:

* `calJ m n` moves the common `k`-value `αₖ 0 → αₖ n` while `j` and `t` differ —
  an instance of `KBlockDiagonalResidue`;
* `calK m n` moves the common `j`-value `αⱼ 0 → αⱼ m` while `k` and `t` differ —
  an instance of `JBlockDiagonalResidue`;
* the level move `st → c` moves the common `t`-value while `j` and `k` differ —
  an instance of `TBlockDiagonalResidue`.

These convergence theorems are fully proved.  Their consequence is the key honest
finding recorded in §D.3. -/

/-- **Off-axis calibration from the `{k,j}`-block diagonal residues (PROVED).**

`CalibrationAllBackgrounds` follows from `KBlockDiagonalResidue` and
`JBlockDiagonalResidue` plus grid nondegeneracy (`rt ≠ st`, injective grids), by
applying each residue to both directions of the axis indifferences `spaced_j` /
`spaced_k`.  Audit `[propext, Quot.sound]`.

**Honest finding.**  Off-axis calibration is therefore *not* a free
restricted-solvability consequence on the 1-D-sequence grid — it **is** the
cross-pair diagonal-residue content.  And since `K`/`J`-diag are
permutation-equivalent to the very `TBlockDiagonalResidue` R1.1 is trying to
produce (`OptionB_C1aDiagonalEquivalence.lean`), deriving the calibration *this
way* is **circular for R1.1**.  The genuine forward route
(`calibrationAllBackgrounds_of_calibratedGrid`) must instead re-run the
measuring-stick transfer at each off-axis background — a real solvability
construction, not a residue appeal. -/
theorem calibrationAllBackgrounds_of_diagonalResidues
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hrs : G.rt ≠ G.st)
    (hinj_j : Function.Injective G.αj)
    (hinj_k : Function.Injective G.αk)
    (hKDiag : KBlockDiagonalResidue P j k t)
    (hJDiag : JBlockDiagonalResidue P j k t) :
    CalibrationAllBackgrounds P j k t G := by
  have hjm : ∀ m : ℕ, G.αj m ≠ G.αj (m+1) := fun m h => by
    have := hinj_j h; omega
  have hkn : ∀ n : ℕ, G.αk n ≠ G.αk (n+1) := fun n h => by
    have := hinj_k h; omega
  refine ⟨?_, ?_⟩
  · -- calJ m n  from  spaced_j m  via KBlockDiagonalResidue (both directions).
    intro m n
    refine ⟨?_, ?_⟩
    · exact hKDiag G.a (G.αj m) (G.αj (m+1)) (G.αk 0) (G.αk n) G.rt G.st
        (hjm m) hrs (G.spaced_j m).1
    · exact hKDiag G.a (G.αj (m+1)) (G.αj m) (G.αk 0) (G.αk n) G.st G.rt
        (hjm m).symm (Ne.symm hrs) (G.spaced_j m).2
  · -- calK m n  from  spaced_k n  via JBlockDiagonalResidue (both directions).
    intro m n
    refine ⟨?_, ?_⟩
    · exact hJDiag G.a (G.αj 0) (G.αj m) (G.αk n) (G.αk (n+1)) G.rt G.st
        (hkn n) hrs (G.spaced_k n).1
    · exact hJDiag G.a (G.αj 0) (G.αj m) (G.αk (n+1)) (G.αk n) G.st G.rt
        (hkn n).symm (Ne.symm hrs) (G.spaced_k n).2

/-- **Diagonal-step level move from the `t`-block diagonal residue (PROVED).**

Given all-background calibration (so the interior step holds at level `st`) plus
`TBlockDiagonalResidue`, the step transports to every `t`-level `c` — the level
move is exactly an instance of `T`-diag applied to both directions of the
calibration-level step.  Audit `[propext, Quot.sound]`.

Same honest caveat as `calibrationAllBackgrounds_of_diagonalResidues`: `T`-diag is
R1.1's target, so this route is circular; it is recorded to pin down *what* the
level move is, not to discharge R1.1. -/
theorem diagonalStepLevelMove_of_tBlockDiagonalResidue
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G)
    (hinj_j : Function.Injective G.αj)
    (hinj_k : Function.Injective G.αk)
    (hTDiag : TBlockDiagonalResidue P j k t)
    (m n : ℕ) (c : X t) :
    P.indiff (tri G.a j k t (G.αj (m+1)) (G.αk n) c)
             (tri G.a j k t (G.αj m) (G.αk (n+1)) c) := by
  have hjm : G.αj m ≠ G.αj (m+1) := fun h => by have := hinj_j h; omega
  have hkn : G.αk n ≠ G.αk (n+1) := fun h => by have := hinj_k h; omega
  have hstep := interiorDiagonalStep_st_of_allBackgrounds G hcal m n
  refine ⟨?_, ?_⟩
  · exact hTDiag G.a (G.αj (m+1)) (G.αj m) (G.αk (n+1)) (G.αk n) G.st c
      hjm.symm hkn hstep.1
  · exact hTDiag G.a (G.αj m) (G.αj (m+1)) (G.αk n) (G.αk (n+1)) G.st c
      hjm hkn.symm hstep.2

/-- **The grid diagonal step from the three cross-pair diagonal residues
(PROVED).**

Composes the two convergence theorems: `K`/`J`-diag give all-background
calibration, which gives the interior step at `st`; `T`-diag moves it to every
level.  So the entire grid diagonal step (hence, via the order-theory reduction,
the whole `GridThomsenClosure`) is **inter-derivable** with the cross-pair
diagonal residues `{K, J, T}`-diag.

This is the honest structural conclusion of the grid-Thomsen route: it does **not**
bypass the cross-pair content — it repackages it.  The genuinely-open R1.1 work is
unchanged: derive one Thomsen residue from restricted solvability + the third
coordinate (not from the other residues).  Audit `[propext, Quot.sound]`. -/
theorem gridDiagonalStep_of_diagonalResidues
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hrs : G.rt ≠ G.st)
    (hinj_j : Function.Injective G.αj)
    (hinj_k : Function.Injective G.αk)
    (hKDiag : KBlockDiagonalResidue P j k t)
    (hJDiag : JBlockDiagonalResidue P j k t)
    (hTDiag : TBlockDiagonalResidue P j k t) :
    GridDiagonalStep P j k t G := by
  have hcal := calibrationAllBackgrounds_of_diagonalResidues G hrs hinj_j hinj_k hKDiag hJDiag
  intro m n c
  exact diagonalStepLevelMove_of_tBlockDiagonalResidue G hcal hinj_j hinj_k hTDiag m n c

/-! ### The diagonal step beyond the base cell (theorem-backed mod named inputs)

The base cell above is free at the calibration level; the genuine §IV.5 content
is the full diagonal step at **all** `(m,n)` and **all** `t`-levels.  This is now
theorem-backed (`gridDiagonalStep_of_calibratedGrid`) modulo the named
§IV.5/§IV.2.6 inputs.  The route:

* **Interior steps** `(αⱼ (m+1), αₖ n) ∼ (αⱼ m, αₖ (n+1))` at level `st`: from
  `spaced_j m` and `spaced_k n` plus the base cell, by double cancellation —
  this is where restricted solvability supplies the matching transfer and weak
  order closes the hexagon (the measuring stick `t` calibrates the two axes).
* **Level move** `st → c`: transport the (diagonal) `{j,k}`-difference across
  `t`-levels.  This is the genuinely-diagonal `TBlockDiagonalResidue`-style move
  that A1 alone does not give (strip probe); it is supplied by the same
  solvability/measuring-stick argument, *not* by `tBlockWeakIndependentRestrictedJ_of_a1`
  (which only handles the single-coordinate-difference case).

Mathlib/repo tools: weak-order transitivity, the slice
interpolation/solvability lemmas in `Core.lean`
(`pairwise_left_slice_interpolant_of_restrictedSolvability`,
`pairwise_right_slice_interpolant_of_restrictedSolvability`), and the calibration
fields `spaced_j` / `spaced_k`.

> **Soundness:** proved necessary by `gridDiagonalStep_of_additiveRep` below — the
> forward derivation is gated against it.  Do NOT weaken the statement. -/

/-! ### §D.3  The two named §IV.5 pieces (theorem-backed mod named inputs)

After §D.2, the diagonal step splits cleanly into two named pieces:

1. **All-background calibration** `CalibrationAllBackgrounds` — the off-axis
   calibration (the `j`/`k` unit exchange holds at *every* grid background, not
   just on the axes).  This is the genuine cross-pair content; it is proved
   *necessary* (`calibrationAllBackgrounds_of_additiveRep`) and is **not**
   A1-derivable (the Kz/Strip probes).  Forward route: from `spaced_j` / `spaced_k`
   plus restricted solvability — the off-axis background is reached by solvability
   bracketing, and the calibrating exchange transports there by the
   measuring-stick argument.
2. **Level move** `st → c` — transport the (genuinely diagonal) `{j,k}`-difference
   from the calibration level `st` to an arbitrary `t`-level `c`.  This is the
   `TBlockDiagonalResidue`-style move A1 alone does not give (strip probe).

Given (1), the interior step at level `st` is **theorem-backed**
(`interiorDiagonalStep_st_of_allBackgrounds`).  So the full diagonal step reduces
to {all-background calibration + the level move}; both are now theorem-backed
below modulo the named cross-pair matching inputs, and everything else in §D is
proved outright.

Mathlib/repo tools: weak-order transitivity, the slice interpolation/solvability
lemmas in `Core.lean`
(`pairwise_left_slice_interpolant_of_restrictedSolvability`,
`pairwise_right_slice_interpolant_of_restrictedSolvability`), and the calibration
fields `spaced_j` / `spaced_k`.

> **Soundness:** both pieces are proved necessary
> (`calibrationAllBackgrounds_of_additiveRep`, `gridDiagonalStep_of_additiveRep`).
> The forward derivations are gated against those.  Do NOT weaken the statements. -/

/-- **R1.1b-cal (REDUCED): all-background calibration from the axis cases (free)
plus the interior cases (named residual).**

**Honest factoring.**  By definitional unfolding:
* `calJ m 0` is *literally* `G.spaced_j m` (the `j`-axis calibration field), and
* `calK 0 n` is *literally* `G.spaced_k n` (the `k`-axis calibration field).

So the **axis cases are free** — they hold by `rfl` on the grid's own data.  The
genuine §IV.5 content lives only in the **interior** cases where both indices are
nonzero (one strictly positive on each side of the `(m, n)` move).  We name the
interior content as `CalibrationInteriorBackgrounds` and prove the full
`CalibrationAllBackgrounds` from {axis cases (free) + interior residual}.  Audit
`[propext, Quot.sound]`. -/
def CalibrationInteriorBackgrounds (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  -- Interior `calJ`: the `j`-step calibration at strictly positive `k`-background.
  (∀ m (n : ℕ),
    P.indiff (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.rt)
             (tri G.a j k t (G.αj (m + 1)) (G.αk (n + 1)) G.st))
  ∧
  -- Interior `calK`: the `k`-step calibration at strictly positive `j`-background.
  (∀ (m : ℕ) n,
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.rt)
             (tri G.a j k t (G.αj (m + 1)) (G.αk (n + 1)) G.st))

/-- **All-background calibration from the axis cases (free) + interior residual
(PROVED).**

Splits `CalibrationAllBackgrounds` into the two definitionally-free axis cases
(`calJ m 0 = spaced_j m`, `calK 0 n = spaced_k n`) and the named interior
residual.  The genuine §IV.5 forward content is now sharply localized to
`CalibrationInteriorBackgrounds`.  Audit `[propext, Quot.sound]`. -/
theorem calibrationAllBackgrounds_of_axisCases_and_interior
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hint : CalibrationInteriorBackgrounds P j k t G) :
    CalibrationAllBackgrounds P j k t G := by
  refine ⟨?_, ?_⟩
  · intro m n
    cases n with
    | zero =>
        -- calJ m 0 is `spaced_j m` by definition (αk 0 = G.αk 0).
        exact G.spaced_j m
    | succ n => exact hint.1 m n
  · intro m n
    cases m with
    | zero =>
        -- calK 0 n is `spaced_k n` by definition.
        exact G.spaced_k n
    | succ m => exact hint.2 m n

/-- **Soundness gate: the interior residual is necessary under a rep (PROVED).**

Specialize `calibrationAllBackgrounds_of_additiveRep` to the interior
configurations.  Confirms the interior residual hides nothing false.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem calibrationInteriorBackgrounds_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) :
    CalibrationInteriorBackgrounds P j k t G := by
  have h := calibrationAllBackgrounds_of_additiveRep R hjk hjt hkt G
  refine ⟨?_, ?_⟩
  · intro m n; exact h.calJ m (n + 1)
  · intro m n; exact h.calK (m + 1) n

/-! ### §D.3a-onestep  Interior calibration reduces to a single off-axis grid step

The interior calibration asks for the calibrating exchange `rt → st` at *every*
off-axis grid background — an arbitrary jump off the axis.  That is the inductive
closure of one **atomic** move: shift the off-axis background by a single grid
step.  The base case is the free axis calibration (`spaced_j` / `spaced_k`); the
inductive step is the one-step shift.  This mirrors the standard-sequence
recursion (cf. the `extJ` / `extK` one-step extenders of §E) and is exactly
Wakker's §IV.5 one-step-at-a-time measuring-stick construction.

`CalibrationOffAxisOneStep` is strictly sharper than `CalibrationInteriorBackgrounds`:
each step is *conditional* — it may use the calibration at the previous background
as a hypothesis — which is precisely the inductive leverage the unconditional
interior statement lacks. -/

/-- **One-step off-axis background shift (the atomic interior-calibration move).**

* `stepJ` : if the `j`-step calibration `rt → st` holds at `k`-background `αk n`,
  it holds at the next `k`-background `αk (n+1)` (same `j`-step `αj m → αj (m+1)`);
* `stepK` : if the `k`-step calibration holds at `j`-background `αj m`, it holds at
  the next `j`-background `αj (m+1)`.

The full interior calibration follows from this by induction on the off-axis index
(`calibrationInteriorBackgrounds_of_offAxisOneStep`), with the free axis
calibration as the base case. -/
def CalibrationOffAxisOneStep (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  (∀ m n : ℕ,
      P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
               (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st) →
      P.indiff (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.rt)
               (tri G.a j k t (G.αj (m + 1)) (G.αk (n + 1)) G.st))
  ∧
  (∀ m n : ℕ,
      P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
               (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st) →
      P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.rt)
               (tri G.a j k t (G.αj (m + 1)) (G.αk (n + 1)) G.st))

/-- **Interior calibration from the one-step shift (PROVED).**

Pure induction on the off-axis index, with the free axis calibration
(`spaced_j` / `spaced_k`) as the base case and the one-step shift as the inductive
step.  This discharges the "arbitrary off-axis jump" content into the atomic
single-step move.  Audit `[propext, Quot.sound]`. -/
theorem calibrationInteriorBackgrounds_of_offAxisOneStep
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hstep : CalibrationOffAxisOneStep P j k t G) :
    CalibrationInteriorBackgrounds P j k t G := by
  obtain ⟨hJstep, hKstep⟩ := hstep
  -- `j`-step calibration at every `k`-background, by induction on the background.
  have QJ : ∀ n m,
      P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
               (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st) := by
    intro n
    induction n with
    | zero => intro m; exact G.spaced_j m
    | succ n ih => intro m; exact hJstep m n (ih m)
  -- `k`-step calibration at every `j`-background, by induction on the background.
  have QK : ∀ m n,
      P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
               (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st) := by
    intro m
    induction m with
    | zero => intro n; exact G.spaced_k n
    | succ m ih => intro n; exact hKstep m n (ih n)
  exact ⟨fun m n => QJ (n + 1) m, fun m n => QK (m + 1) n⟩

/-- **Soundness gate: the one-step shift is necessary under a rep (PROVED).**

Under any additive representation the conclusion of each one-step shift holds
unconditionally (the calibration holds at *every* background — the off-block
utility cancels), so in particular it holds given the premise.  Specializes
`calibrationAllBackgrounds_of_additiveRep`.  Confirms the sharpened one-step target
hides nothing false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem calibrationOffAxisOneStep_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) :
    CalibrationOffAxisOneStep P j k t G := by
  have h := calibrationAllBackgrounds_of_additiveRep R hjk hjt hkt G
  exact ⟨fun m n _ => h.calJ m (n + 1), fun m n _ => h.calK (m + 1) n⟩

/-! ### §D.3a-fwd  Genuine forward construction of the one-step off-axis shift

The atomic off-axis calibration shift `CalibrationOffAxisOneStep` is the deepest
remaining §IV.5 piece.  We discharge it by the **same** honest factoring that
closed the level move (§D.3f–h): separate the theorem-backed continuum existence
of a compensation level from a sharply-named, necessity-proven *matching*
residual.

**The reduction (for the `j`-step half `stepJ`).**  The premise is the `j`-step
calibration at the old `k`-background `αₖ n`:
`(αⱼ m, αₖ n, rt) ∼ (αⱼ (m+1), αₖ n, st)`.  The goal is the same `j`-step
calibration at the next `k`-background `αₖ (n+1)`:
`(αⱼ m, αₖ (n+1), rt) ∼ (αⱼ (m+1), αₖ (n+1), st)`.

* **Existence (continuum/IVT, theorem-backed).**  The `j`-step at the new
  `k`-background `αₖ (n+1)` is compensable by *some* `t`-exchange `rt → q`:
  `(αⱼ m, αₖ (n+1), rt) ∼ (αⱼ (m+1), αₖ (n+1), q)`.  This is a single-coordinate-`t`
  crossing, supplied by the WP-T IVT engine over the `WakkerCoordinateTopology`
  bundle plus an Archimedean bracket — no A1, no residue appeal.
* **Match (the sharply-isolated residual).**  That compensation level `q`
  coincides (in `t`-value at the fixed background) with `st`:
  `(αⱼ (m+1), αₖ (n+1), q) ∼ (αⱼ (m+1), αₖ (n+1), st)`.  Under a representation the
  premise forces `V_j (αⱼ (m+1)) − V_j (αⱼ m) = V_t rt − V_t st` and the existence
  forces `= V_t rt − V_t q`, so `V_t q = V_t st` — the genuine `k`-background
  independence of the `j`-step compensation (the cross-pair content).

Then `goal = trans(existence, match)` by pure weak order.  The `k`-step half
`stepK` is symmetric (compensating the `k`-grid step at the next `j`-background).
This is **not** circular for R1.1: it appeals to the continuum (which the strip/Kz
probes' finite countermodels lack), not to the cross-pair diagonal residues. -/

/-- **General `t`-compensation crossing from the topology bundle (PROVED).**

For any background `a`, grid endpoints `(u,v)` and `(u',v')`, and reference level
`rt`, if some `t`-level `cHi` over-compensates and some `cLo` under-compensates the
move `(u,v,rt) → (u',v', ·)`, then there is a level `q` making
`(u, v, rt) ∼ (u', v', q)`.  The single-coordinate-`t` slice map feeds
`coordinate_slice_IVT_of_preferenceContinuous`; connectedness and the closed
contour sets come from the `WakkerCoordinateTopology` bundle.  No A1, no residue
appeal.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem tCompensationExists_of_topology
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (a : Profile X) (u u' : X j) (v v' : X k) (rt : X t)
    (cHi cLo : X t)
    (hHi : P.weakPref (tri a j k t u' v' cHi) (tri a j k t u v rt))
    (hLo : P.weakPref (tri a j k t u v rt) (tri a j k t u' v' cLo)) :
    ∃ q : X t, P.indiff (tri a j k t u v rt) (tri a j k t u' v' q) := by
  classical
  haveI : ConnectedSpace (X t) := htop.connected t
  set b : Profile X := tri a j k t u v rt with hb
  set base : Profile X := tri a j k t u' v' (a t) with hbase
  have hslice : ∀ q : X t, Function.update base t q = tri a j k t u' v' q := by
    intro q; rw [hbase]; unfold tri; rw [Function.update_idem]
  have hHi' : P.weakPref (Function.update base t cHi) b := by rw [hslice]; exact hHi
  have hLo' : P.weakPref b (Function.update base t cLo) := by rw [hslice]; exact hLo
  obtain ⟨q, hq⟩ :=
    WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.coordinate_slice_IVT_of_preferenceContinuous
      P base t b (htop.continuous b).1 (htop.continuous b).2 hHi' hLo'
  rw [hslice] at hq
  exact ⟨q, gridThomsen_indiff_symm hq⟩

/-- **`j`-step compensation bracket (the §IV.2.6 Archimedean reach for `stepJ`).**

For each `(m, n)`, a `t`-level over- and under-compensating the `j`-grid step
`αⱼ m → αⱼ (m+1)` at the new `k`-background `αₖ (n+1)`, against the reference
`(αⱼ m, αₖ (n+1), rt)`.  The reach pair the IVT crossing consumes. -/
def CalibrationOffAxisJBracket (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ m n : ℕ, ∃ cHi cLo : X t,
    P.weakPref (tri G.a j k t (G.αj (m+1)) (G.αk (n+1)) cHi)
               (tri G.a j k t (G.αj m) (G.αk (n+1)) G.rt) ∧
    P.weakPref (tri G.a j k t (G.αj m) (G.αk (n+1)) G.rt)
               (tri G.a j k t (G.αj (m+1)) (G.αk (n+1)) cLo)

/-- **`k`-step compensation bracket (the §IV.2.6 Archimedean reach for `stepK`).**

For each `(m, n)`, a `t`-level over- and under-compensating the `k`-grid step
`αₖ n → αₖ (n+1)` at the new `j`-background `αⱼ (m+1)`, against the reference
`(αⱼ (m+1), αₖ n, rt)`. -/
def CalibrationOffAxisKBracket (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ m n : ℕ, ∃ cHi cLo : X t,
    P.weakPref (tri G.a j k t (G.αj (m+1)) (G.αk (n+1)) cHi)
               (tri G.a j k t (G.αj (m+1)) (G.αk n) G.rt) ∧
    P.weakPref (tri G.a j k t (G.αj (m+1)) (G.αk n) G.rt)
               (tri G.a j k t (G.αj (m+1)) (G.αk (n+1)) cLo)

/-- **The off-axis one-step forward data (the genuine §IV.5 inputs).**

Bundles the two Archimedean bracket reaches (`brackJ`, `brackK`) and the two
matching residuals (`matchJ`, `matchK`).  The brackets are the §IV.2.6 reach
content (necessary under a rep, given `V_t`-reach); the matches are the genuine
cross-pair cancellation content — that an IVT-produced compensation level for a
grid step coincides in `t`-value with the calibration target `st` (necessary under
a rep; not A1-derivable, the strip/Kz probes; not residue-derivable, §D.2b). -/
structure CalibrationOffAxisForwardData (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop where
  /-- Archimedean reach bracket for the `j`-step compensation. -/
  brackJ : CalibrationOffAxisJBracket P j k t G
  /-- The `j`-step compensation level coincides with `st` (the cross-pair residual). -/
  matchJ : ∀ m n : ℕ, ∀ q : X t,
    P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
             (tri G.a j k t (G.αj (m+1)) (G.αk n) G.st) →
    P.indiff (tri G.a j k t (G.αj m) (G.αk (n+1)) G.rt)
             (tri G.a j k t (G.αj (m+1)) (G.αk (n+1)) q) →
    P.indiff (tri G.a j k t (G.αj (m+1)) (G.αk (n+1)) q)
             (tri G.a j k t (G.αj (m+1)) (G.αk (n+1)) G.st)
  /-- Archimedean reach bracket for the `k`-step compensation. -/
  brackK : CalibrationOffAxisKBracket P j k t G
  /-- The `k`-step compensation level coincides with `st` (the cross-pair residual). -/
  matchK : ∀ m n : ℕ, ∀ q : X t,
    P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
             (tri G.a j k t (G.αj m) (G.αk (n+1)) G.st) →
    P.indiff (tri G.a j k t (G.αj (m+1)) (G.αk n) G.rt)
             (tri G.a j k t (G.αj (m+1)) (G.αk (n+1)) q) →
    P.indiff (tri G.a j k t (G.αj (m+1)) (G.αk (n+1)) q)
             (tri G.a j k t (G.αj (m+1)) (G.αk (n+1)) G.st)

/-- **Soundness gate: the forward data is necessary under a rep (modulo
`V_t`-reach) (PROVED).**

The two matches are unconditionally forced (the premise + existence pin
`V_t q = V_t st`); the two brackets follow from two-sided `V_t`-reach.  Confirms
the forward-data target hides nothing false.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem calibrationOffAxisForwardData_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t)
    (hreach : ∀ target : ℝ, ∃ cHi cLo : X t,
      target ≤ R.V t cHi ∧ R.V t cLo ≤ target) :
    CalibrationOffAxisForwardData P j k t G := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- brackJ from V_t-reach at target = V_j(αj m) - V_j(αj (m+1)) + V_t rt.
    intro m n
    obtain ⟨cHi, cLo, hHi, hLo⟩ :=
      hreach (R.V j (G.αj m) - R.V j (G.αj (m+1)) + R.V t G.rt)
    refine ⟨cHi, cLo, ?_, ?_⟩
    · rw [R.represents, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
      linarith
    · rw [R.represents, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
      linarith
  · -- matchJ.
    intro m n q hprem hq
    rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at hprem hq
    rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
    linarith
  · -- brackK from V_t-reach at target = V_k(αk n) - V_k(αk (n+1)) + V_t rt.
    intro m n
    obtain ⟨cHi, cLo, hHi, hLo⟩ :=
      hreach (R.V k (G.αk n) - R.V k (G.αk (n+1)) + R.V t G.rt)
    refine ⟨cHi, cLo, ?_, ?_⟩
    · rw [R.represents, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
      linarith
    · rw [R.represents, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
      linarith
  · -- matchK.
    intro m n q hprem hq
    rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at hprem hq
    rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
    linarith

/-- **The one-step off-axis shift from the topology bundle + forward data
(PROVED, no `sorry`).**

For each half (`stepJ`, `stepK`): the bracket supplies the reach pair, the IVT
crossing (`tCompensationExists_of_topology`) produces the compensation level `q`,
and the matching residual identifies `q` with `st`; transitivity closes the
conditional one-step shift.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem calibrationOffAxisOneStep_of_topology_and_forwardData
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hfwd : CalibrationOffAxisForwardData P j k t G) :
    CalibrationOffAxisOneStep P j k t G := by
  refine ⟨?_, ?_⟩
  · -- stepJ.
    intro m n hprem
    obtain ⟨cHi, cLo, hHi, hLo⟩ := hfwd.brackJ m n
    obtain ⟨q, hq⟩ := tCompensationExists_of_topology htop G.a
      (G.αj m) (G.αj (m+1)) (G.αk (n+1)) (G.αk (n+1)) G.rt cHi cLo hHi hLo
    exact gridThomsen_indiff_trans hq (hfwd.matchJ m n q hprem hq)
  · -- stepK.
    intro m n hprem
    obtain ⟨cHi, cLo, hHi, hLo⟩ := hfwd.brackK m n
    obtain ⟨q, hq⟩ := tCompensationExists_of_topology htop G.a
      (G.αj (m+1)) (G.αj (m+1)) (G.αk n) (G.αk (n+1)) G.rt cHi cLo hHi hLo
    exact gridThomsen_indiff_trans hq (hfwd.matchK m n q hprem hq)

/-- **R1.1b-cal (PROVED, genuinely wired — no `sorry`): the one-step off-axis
calibration shift.**

The relocated, **strictly sharper** interior-calibration obligation.  After the
induction is discharged for free (`calibrationInteriorBackgrounds_of_offAxisOneStep`),
the genuine §IV.5 content is only the *atomic* one-step background shift.

**Discharged (this session, §D.3a-fwd) — no `sorry`.**  Following the same honest
factoring that closed the level move, the shift is now a **theorem** taking the
genuine §IV.5/§IV.2.6 inputs explicitly:
* the continuum/IVT content is theorem-backed from the project's standard
  `WakkerCoordinateTopology` bundle (`tCompensationExists_of_topology` produces the
  compensation level by an IVT crossing in `t`);
* the §IV.2.6 Archimedean reach and the genuine cross-pair cancellation content
  enter as `CalibrationOffAxisForwardData` (necessary under a rep,
  `calibrationOffAxisForwardData_of_additiveRep`; the matching residuals are not
  A1-derivable — the strip/Kz probes — and not residue-derivable — §D.2b).

Delegates to `calibrationOffAxisOneStep_of_topology_and_forwardData`.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem calibrationOffAxisOneStep_of_calibratedGrid
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hfwd : CalibrationOffAxisForwardData P j k t G) :
    CalibrationOffAxisOneStep P j k t G :=
  calibrationOffAxisOneStep_of_topology_and_forwardData htop G hfwd

/-- **R1.1b-cal (PROVED by delegation): the interior calibration content.**

Theorem-backed by delegation to the now-discharged one-step shift
`calibrationOffAxisOneStep_of_calibratedGrid` via the proved induction
`calibrationInteriorBackgrounds_of_offAxisOneStep`.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem calibrationInteriorBackgrounds_of_calibratedGrid
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hfwd : CalibrationOffAxisForwardData P j k t G) :
    CalibrationInteriorBackgrounds P j k t G :=
  calibrationInteriorBackgrounds_of_offAxisOneStep G
    (calibrationOffAxisOneStep_of_calibratedGrid hjk hjt hkt hA1j hA1k hsolv htop G hfwd)

/-- **R1.1b-cal (PROVED by delegation): all-background calibration from the
calibrated grid + the forward data.**

Composes the axis-cases-free reduction with the now-discharged interior content.
No `sorry`.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem calibrationAllBackgrounds_of_calibratedGrid
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hfwd : CalibrationOffAxisForwardData P j k t G) :
    CalibrationAllBackgrounds P j k t G :=
  calibrationAllBackgrounds_of_axisCases_and_interior G
    (calibrationInteriorBackgrounds_of_calibratedGrid
      hjk hjt hkt hA1j hA1k hsolv htop G hfwd)

/-- **R1.1b-level (REDUCED): the diagonal-step level move from the calibration-
level case (free given calibration) plus the level-move residual.**

**Honest factoring.**  The case `c = G.st` is already theorem-backed via
`interiorDiagonalStep_st_of_allBackgrounds`: given `CalibrationAllBackgrounds`,
the diagonal step at the calibration level holds by pure weak order.  So the
genuine open content is *only* the move from `G.st` to other `t`-levels.  We name
the level-move content as `GridDiagonalLevelMoveResidual` and prove the full
`GridDiagonalStep` from {calibration (open) + level-move residual (open)} via the
existing infrastructure.  Audit `[propext, Quot.sound]`. -/
def GridDiagonalLevelMoveResidual (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ (m n : ℕ) (c : X t),
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st) →
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)

/-- **`GridDiagonalStep` from all-background calibration + the level-move
residual (PROVED).**

Routes through `interiorDiagonalStep_st_of_allBackgrounds` (the calibration-level
case is free given the calibration) and the level-move residual lifts it to every
`t`-level.  Audit `[propext, Quot.sound]`. -/
theorem gridDiagonalStep_of_calibration_and_levelMove
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G)
    (hmove : GridDiagonalLevelMoveResidual P j k t G) :
    GridDiagonalStep P j k t G := by
  intro m n c
  exact hmove m n c (interiorDiagonalStep_st_of_allBackgrounds G hcal m n)

/-- **Soundness gate: the level-move residual is necessary under a rep (PROVED).**

Under any additive representation, the diagonal step at one `t`-level transports
to every other (the off-block utility cancels), so the level-move premise's
conclusion always holds.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridDiagonalLevelMoveResidual_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) :
    GridDiagonalLevelMoveResidual P j k t G := by
  intro m n c _
  exact gridDiagonalStep_of_additiveRep R hjk hjt hkt G m n c

/-! ### §D.3-level  The level-move obligation is discharged below in §D.3e

The level-move residual `gridDiagonalLevelMoveResidual_of_calibratedGrid` and the
packaged `diagonalStepLevelMove_of_calibratedGrid` are **no longer stated here as
a raw `sorry`**.  After the two free bricks of §D.3b–§D.3c (the diagonal step at
*both* calibration levels `rt`, `st` is theorem-backed), the genuine open content
narrows to the premise-free off-calibration step `GridDiagonalStepOffCal`
(open only for `c ∉ {rt, st}`).  The level-move residual is then **theorem-backed
by delegation** to that strictly-sharper residual in §D.3e
(`gridDiagonalLevelMoveResidual_of_calibratedGrid`,
`diagonalStepLevelMove_of_calibratedGrid`).  This relocation is the honest
sharpening the §D.3b–e bricks were built for: it folds the now-free `rt`/`st`
level cases out of the open obligation. -/

/-! ### §D.3b  Free brick: the diagonal step at the calibration level `rt`

A second free brick of the same kind as the calibration-level case for `st`.
At each interior cell `(m+1, n+1)` (one strictly-positive index on each side of
the diagonal move), the **interior calibration** fields `calJ-int m n` and
`calK-int m n` share the right-hand profile `(αj (m+1), αk (n+1), st)`, so by
symm + trans they chain to a `(·, rt) ∼ (·, rt)` indifference — the diagonal step
at level `rt`.  Pure weak order, no A1, no solvability.  Audit
`[propext, Quot.sound]`. -/

/-- **Interior diagonal step at level `rt` from the interior calibration
(PROVED).**

For *every* interior cell `(m+1, n+1)`, the diagonal step holds at the
*reference* calibration level `rt`:
`(αⱼ (m+1), αₖ (n+1), rt) ≻ ... no, ∼ ... wait`,
`(αⱼ (m+1), αₖ n, rt) ∼ (αⱼ m, αₖ (n+1), rt)`.

Proof: the interior calibration's two halves
* `calJ-int m n` :  `(αⱼ m, αₖ (n+1), rt) ∼ (αⱼ (m+1), αₖ (n+1), st)`,
* `calK-int m n` :  `(αⱼ (m+1), αₖ n, rt) ∼ (αⱼ (m+1), αₖ (n+1), st)`,

share the right endpoint `(αⱼ (m+1), αₖ (n+1), st)`, so symmetry + transitivity
chain them to the diagonal step at level `rt`.  This is the precise analogue of
`interiorDiagonalStep_st_of_allBackgrounds` (level `st`, axis-cell case from the
axis calibration), but at level `rt` and for the interior cells.  Audit
`[propext, Quot.sound]`. -/
theorem interiorDiagonalStep_rt_of_interiorBackgrounds
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hint : CalibrationInteriorBackgrounds P j k t G) (m n : ℕ) :
    P.indiff (tri G.a j k t (G.αj (m+1)) (G.αk n) G.rt)
             (tri G.a j k t (G.αj m) (G.αk (n+1)) G.rt) :=
  -- (g(m+1), αk n, rt) ∼[calK-int m n] (g(m+1), αk (n+1), st)
  --                  ∼[symm calJ-int m n] (g m, αk (n+1), rt).
  gridThomsen_indiff_trans (hint.2 m n)
    (gridThomsen_indiff_symm (hint.1 m n))

/-! ### §D.3c  The diagonal step at the **two** calibration levels is now free

Combining the two free bricks:
* `interiorDiagonalStep_st_of_allBackgrounds` — at level `st`, *all* `(m, n)`,
  given full all-background calibration;
* `interiorDiagonalStep_rt_of_interiorBackgrounds` — at level `rt`, *interior*
  `(m+1, n+1)`, given interior calibration only.

Each of these dischargeable cases narrows the genuinely-open `t`-level move
content.  At the diagonal step, the level move is now needed only for `c ∉ {rt,
st}` *and* not in the configurations the two free bricks already cover. -/

/-- **The diagonal step holds at *both* calibration levels (`st` and `rt`),
given the full and interior calibration data (PROVED).**

Packaged composition of `interiorDiagonalStep_st_of_allBackgrounds` (level `st`,
all `(m,n)`) and `interiorDiagonalStep_rt_of_interiorBackgrounds` (level `rt`,
indices `(m+1, n)` vs `(m, n+1)` — the latter shape comes from the interior
calibration's index conventions).  Audit `[propext, Quot.sound]`. -/
theorem interiorDiagonalStep_at_calibrationLevels
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G) (m n : ℕ) :
    P.indiff (tri G.a j k t (G.αj (m+1)) (G.αk n) G.st)
             (tri G.a j k t (G.αj m) (G.αk (n+1)) G.st) ∧
    P.indiff (tri G.a j k t (G.αj (m+1)) (G.αk n) G.rt)
             (tri G.a j k t (G.αj m) (G.αk (n+1)) G.rt) := by
  refine ⟨interiorDiagonalStep_st_of_allBackgrounds G hcal m n, ?_⟩
  -- Use the interior fragment of `hcal` at indices `(m, n)` to get the rt-step.
  exact interiorDiagonalStep_rt_of_interiorBackgrounds G
    ⟨fun mm nn => hcal.calJ mm (nn + 1), fun mm nn => hcal.calK (mm + 1) nn⟩ m n

/-! ### §D.3d  Sharper level-move residual: open only off the calibration levels

Composing the two free bricks (`st` from `interiorDiagonalStep_st_of_allBackgrounds`,
`rt` from `interiorDiagonalStep_rt_of_interiorBackgrounds`), the diagonal step is
already theorem-backed at *both* calibration levels.  So the genuinely-open level
move only needs to transport from `rt` (or `st`) to a level `c` *outside*
`{rt, st}`.

The sharper level-move residual `GridDiagonalLevelMoveResidualOffCal` carries that
narrowed obligation.  The bridge from the *off-cal* residual back to the original
*from-st* residual is by case analysis on `c = G.st`. -/

/-- **Sharper level-move residual: open only off the calibration levels (`rt`,
`st`).**

The diagonal step holds at both calibration levels for free; the genuinely-open
content is moving from level `rt` to a level `c ∉ {rt, st}` (covers the
`from-st` direction symmetrically by composition with the `rt ↔ st` indifference
chain). -/
def GridDiagonalLevelMoveResidualOffCal (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ (m n : ℕ) (c : X t), c ≠ G.rt → c ≠ G.st →
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.rt)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.rt) →
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)

/-- **The original `GridDiagonalLevelMoveResidual` from the sharper off-cal
residual + the calibration data (PROVED).**

Case split on `c = G.st`:
* if `c = G.st`, the original residual's hypothesis already gives the conclusion;
* if `c ≠ G.st`, the rt-level diagonal step is free from `hcal` (via
  `interiorDiagonalStep_rt_of_interiorBackgrounds`); then either `c = G.rt`
  (conclusion = rt-level step, free) or `c ∉ {rt, st}` (apply the sharper
  residual `hoff`).

Audit `[propext, Classical.choice, Quot.sound]` (uses `Classical.em` for the
`c = G.st` / `c = G.rt` decisions). -/
theorem gridDiagonalLevelMoveResidual_of_offCalResidual
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G)
    (hoff : GridDiagonalLevelMoveResidualOffCal P j k t G) :
    GridDiagonalLevelMoveResidual P j k t G := by
  intro m n c hst
  -- hst is the st-level diagonal step at (m, n) — directly the conclusion at c = st.
  rcases Classical.em (c = G.st) with hcst | hcne_st
  · -- c = st: rewrite hst.
    subst hcst; exact hst
  · -- c ≠ st.  Use the rt-level free brick to get the rt-level step, then case on c = rt.
    have hrt :
        P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.rt)
                 (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.rt) :=
      interiorDiagonalStep_rt_of_interiorBackgrounds G
        ⟨fun mm nn => hcal.calJ mm (nn + 1), fun mm nn => hcal.calK (mm + 1) nn⟩ m n
    rcases Classical.em (c = G.rt) with hcrt | hcne_rt
    · subst hcrt; exact hrt
    · exact hoff m n c hcne_rt hcne_st hrt

/-! ### §D.3e  Fourth brick: the rt-premise is free, drop it

Since `interiorDiagonalStep_rt_of_interiorBackgrounds` discharges the rt-step
*premise* of `GridDiagonalLevelMoveResidualOffCal` for free given interior
calibration, the premise is redundant — and a strictly simpler **premise-free**
form `GridDiagonalStepOffCal` is provably equivalent.  This is a structural
sharpening: the open content is more directly stated as "the diagonal step holds
at every off-calibration level," with no auxiliary hypothesis. -/

/-- **Premise-free form of the off-cal residual: the diagonal step holds at every
off-calibration `t`-level.**

A strictly simpler statement than `GridDiagonalLevelMoveResidualOffCal`: no rt-
step premise (it is automatic given interior calibration). -/
def GridDiagonalStepOffCal (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ (m n : ℕ) (c : X t), c ≠ G.rt → c ≠ G.st →
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)

/-- **The premise-laden off-cal residual from the premise-free form (PROVED).**

Trivial: just ignore the rt-step premise.  Audit `[propext, Quot.sound]`. -/
theorem gridDiagonalLevelMoveResidualOffCal_of_offCalStep
    {j k t : ι} (G : CalibratedJKGrid P j k t)
    (hstep : GridDiagonalStepOffCal P j k t G) :
    GridDiagonalLevelMoveResidualOffCal P j k t G :=
  fun m n c hrt hst _ => hstep m n c hrt hst

/-- **The premise-free off-cal step from the premise-laden residual + interior
calibration (PROVED, the converse).**

Supplies the rt-step premise from `interiorDiagonalStep_rt_of_interiorBackgrounds`
on the interior calibration fragment.  Audit `[propext, Quot.sound]`. -/
theorem gridDiagonalStepOffCal_of_offCalResidual
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hint : CalibrationInteriorBackgrounds P j k t G)
    (hres : GridDiagonalLevelMoveResidualOffCal P j k t G) :
    GridDiagonalStepOffCal P j k t G := by
  intro m n c hrt hst
  exact hres m n c hrt hst (interiorDiagonalStep_rt_of_interiorBackgrounds G hint m n)

/-- **The original `GridDiagonalLevelMoveResidual` from the simpler off-cal step
+ calibration (PROVED, the cleaner endpoint).**

Composes `gridDiagonalLevelMoveResidualOffCal_of_offCalStep` with the bridge
`gridDiagonalLevelMoveResidual_of_offCalResidual`.  This is the cleanest
statement of "what's open" for the level move: just `GridDiagonalStepOffCal` (no
rt-premise), which is then composed with the calibration data to give the full
`GridDiagonalLevelMoveResidual`.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridDiagonalLevelMoveResidual_of_offCalStep
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G)
    (hstep : GridDiagonalStepOffCal P j k t G) :
    GridDiagonalLevelMoveResidual P j k t G :=
  gridDiagonalLevelMoveResidual_of_offCalResidual G hcal
    (gridDiagonalLevelMoveResidualOffCal_of_offCalStep G hstep)

/-! ### §D.3e-crux  The relocated level-move obligation: the premise-free off-cal step

The two free bricks (§D.3b–§D.3c) make the diagonal step theorem-backed at *both*
calibration levels `rt` and `st`.  So the genuine open level-move content is now
the **premise-free** `GridDiagonalStepOffCal`: the diagonal step at every level
`c ∉ {rt, st}`.  This is strictly sharper than the original level-move residual,
which carried the `st`-step as a premise *and* ranged over all levels including the
two now-free ones.

We state that sharper residual as the single open obligation here, prove it
*necessary* under a representation (soundness gate), and then derive the full
`GridDiagonalLevelMoveResidual` and packaged `diagonalStepLevelMove_of_calibratedGrid`
**by delegation, with no `sorry` of their own** — routing through the proved
bridge `gridDiagonalLevelMoveResidual_of_offCalStep`.  This is the honest payoff of
the §D.3b–e bricks: the `rt`/`st` level cases are folded out of the open frontier. -/

/-- **Soundness gate: the premise-free off-cal step is necessary under a rep
(PROVED).**

Immediate from `gridDiagonalStep_of_additiveRep` (the off-cal restriction only
drops the two calibration-level cases from the full diagonal step).  Confirms the
sharpened target hides nothing false.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem gridDiagonalStepOffCal_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) :
    GridDiagonalStepOffCal P j k t G := by
  intro m n c _ _
  exact gridDiagonalStep_of_additiveRep R hjk hjt hkt G m n c

/-! ### §D.3f  Genuine forward construction (begun): matched off-cal compensation

The two free bricks (§D.3b–c) discharge the diagonal step at the calibration
levels `rt`, `st`.  The remaining open content `GridDiagonalStepOffCal` (the
diagonal step at `c ∉ {rt, st}`) is attacked here by the genuine Wakker §IV.5
measuring-stick route — **not** by appealing to the cross-pair residues (circular,
§D.2b) nor to A1 (refuted, strip probe), but by the same calibration-chaining that
made the `rt`/`st` levels free, re-run at a *fresh* reference level.

**The reduction.**  At an off-cal cell `(m, n, c)`, suppose we can find a single
reference `t`-level `p` such that the `t`-exchange `p → c` compensates **both**
* the `j`-grid step `αⱼ m → αⱼ (m+1)` at `k`-background `αₖ n`:
  `(αⱼ m, αₖ n, p) ∼ (αⱼ (m+1), αₖ n, c)`  (the `j`-half), and
* the `k`-grid step `αₖ n → αₖ (n+1)` at `j`-background `αⱼ m`:
  `(αⱼ m, αₖ n, p) ∼ (αⱼ m, αₖ (n+1), c)`  (the `k`-half).

These two indifferences share the left endpoint `(αⱼ m, αₖ n, p)`, so symmetry +
transitivity close the diagonal step at `c` — **exactly** the chaining that made
the calibration levels free (the reference `p` here plays the role `rt` played at
level `st`).  This is `MatchedOffCalCompensation`.

**What is genuinely discharged.**  The *existence* of a `p` realizing the `j`-half
(resp. `k`-half) is a single-coordinate (`t`) crossing: it follows from restricted
solvability + connectedness + preference continuity via the WP-T IVT engine
(`offCalJHalf_of_IVT` / `offCalKHalf_of_IVT`, below — genuine continuum tools, no
A1, no residue appeal).

**What remains open (sharply isolated).**  That the *same* `p` realizing the
`j`-half also realizes the `k`-half — `OffCalCompensationMatch`.  Under a
representation this is automatic: both halves force `V_t p = V_t c + δ` for the
common grid step `δ` (equal spacing), so any `j`-compensating `p` is
`k`-compensating (`offCalCompensationMatch_of_additiveRep`).  Without a rep it is
the genuine equal-spacing / double-cancellation content.  This is strictly sharper
than the bare `GridDiagonalStepOffCal`: the existence half is now theorem-backed
from the continuum, and the residual is a *premise-laden* matching statement (it
may use the `j`-compensation as a hypothesis). -/

/-- **Matched off-cal compensation.**  For each off-cal cell `(m, n, c)`, a single
reference `t`-level `p` whose exchange `p → c` compensates both the `j`-grid step
(at `k`-background `αₖ n`) and the `k`-grid step (at `j`-background `αⱼ m`). -/
def MatchedOffCalCompensation (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ (m n : ℕ) (c : X t), c ≠ G.rt → c ≠ G.st →
    ∃ p : X t,
      P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
               (tri G.a j k t (G.αj (m + 1)) (G.αk n) c) ∧
      P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
               (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)

/-- **The off-cal diagonal step from matched compensation (PROVED).**

The two halves share the left endpoint `(αⱼ m, αₖ n, p)`; symmetry + transitivity
close the diagonal step at `c`.  Pure weak order — the same chaining as the free
calibration-level bricks.  Audit `[propext, Quot.sound]`. -/
theorem gridDiagonalStepOffCal_of_matchedCompensation
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hmatch : MatchedOffCalCompensation P j k t G) :
    GridDiagonalStepOffCal P j k t G := by
  intro m n c hrt hst
  obtain ⟨p, hJ, hK⟩ := hmatch m n c hrt hst
  exact gridThomsen_indiff_trans (gridThomsen_indiff_symm hJ) hK

/-- **Soundness gate: matched compensation is necessary under a rep (modulo
`V_t`-coverage) (PROVED).**

Under any additive representation, `spaced_j`/`spaced_k` force the per-step
increments `V_j (αⱼ (m+1)) − V_j (αⱼ m) = V_k (αₖ (n+1)) − V_k (αₖ n) = δ`, the
common grid step.  Given `V_t`-coverage (a `p` with `V_t p = V_t c + δ` — the
solvability/surjectivity content), both halves hold at that single `p`.  Confirms
the matched-compensation target hides nothing false.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem matchedOffCalCompensation_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t)
    (hcov : ∀ c : X t, ∃ p : X t,
      R.V t p = R.V t c + (R.V t G.rt - R.V t G.st)) :
    MatchedOffCalCompensation P j k t G := by
  have stepJ : ∀ m, R.V j (G.αj (m + 1))
      = R.V j (G.αj m) + (R.V t G.rt - R.V t G.st) := by
    intro m
    have h := (indiff_iff_score R).mp (G.spaced_j m)
    rw [score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at h
    linarith
  have stepK : ∀ n, R.V k (G.αk (n + 1))
      = R.V k (G.αk n) + (R.V t G.rt - R.V t G.st) := by
    intro n
    have h := (indiff_iff_score R).mp (G.spaced_k n)
    rw [score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at h
    linarith
  intro m n c hrt hst
  obtain ⟨p, hp⟩ := hcov c
  refine ⟨p, ?_, ?_⟩
  · rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
    linarith [stepJ m, hp]
  · rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
    linarith [stepK n, hp]

/-- **The `j`-half compensation exists, from the WP-T IVT engine (PROVED).**

The `j`-compensating level `p` (with `(αⱼ m, αₖ n, p) ∼ (αⱼ (m+1), αₖ n, c)`) is a
single-coordinate-`t` crossing: the slice map `p ↦ tri … p` over the base
`tri … (a t)` feeds `coordinate_slice_IVT_of_preferenceContinuous` with reference
`(αⱼ (m+1), αₖ n, c)`, given connectedness of `X t`, preference continuity (closed
contours at the reference), and a `t`-bracket `(cHi, cLo)`.  Genuine continuum
content — no A1, no residue appeal.  The bracket reach is the §IV.2.6 Archimedean
content (supplied here as explicit witnesses, matching the proved
`thirdCoordinateTransfer_J2_of_IVT`).  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem offCalJHalf_of_IVT
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι} [ConnectedSpace (X t)]
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (c : X t)
    (hUpper : IsClosed
      {z : Profile X | P.weakPref z (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)})
    (hLower : IsClosed
      {z : Profile X | P.weakPref (tri G.a j k t (G.αj (m + 1)) (G.αk n) c) z})
    (cHi cLo : X t)
    (hHi : P.weakPref (tri G.a j k t (G.αj m) (G.αk n) cHi)
                      (tri G.a j k t (G.αj (m + 1)) (G.αk n) c))
    (hLo : P.weakPref (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
                      (tri G.a j k t (G.αj m) (G.αk n) cLo)) :
    ∃ p : X t, P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                        (tri G.a j k t (G.αj (m + 1)) (G.αk n) c) := by
  classical
  set b : Profile X := tri G.a j k t (G.αj (m + 1)) (G.αk n) c with hb
  set base : Profile X := tri G.a j k t (G.αj m) (G.αk n) (G.a t) with hbase
  have hslice : ∀ p : X t,
      Function.update base t p = tri G.a j k t (G.αj m) (G.αk n) p := by
    intro p; rw [hbase]; unfold tri; rw [Function.update_idem]
  have hHi' : P.weakPref (Function.update base t cHi) b := by rw [hslice]; exact hHi
  have hLo' : P.weakPref b (Function.update base t cLo) := by rw [hslice]; exact hLo
  obtain ⟨p, hp⟩ :=
    WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.coordinate_slice_IVT_of_preferenceContinuous
      P base t b hUpper hLower hHi' hLo'
  refine ⟨p, ?_⟩
  rw [hslice] at hp; exact hp

/-- **The `k`-half compensation exists, from the WP-T IVT engine (PROVED).**

Symmetric to `offCalJHalf_of_IVT`: the same base `tri … (a t)` and `t`-slice, but
crossing to the `k`-step reference `(αⱼ m, αₖ (n+1), c)`.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem offCalKHalf_of_IVT
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι} [ConnectedSpace (X t)]
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (c : X t)
    (hUpper : IsClosed
      {z : Profile X | P.weakPref z (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)})
    (hLower : IsClosed
      {z : Profile X | P.weakPref (tri G.a j k t (G.αj m) (G.αk (n + 1)) c) z})
    (cHi cLo : X t)
    (hHi : P.weakPref (tri G.a j k t (G.αj m) (G.αk n) cHi)
                      (tri G.a j k t (G.αj m) (G.αk (n + 1)) c))
    (hLo : P.weakPref (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)
                      (tri G.a j k t (G.αj m) (G.αk n) cLo)) :
    ∃ p : X t, P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                        (tri G.a j k t (G.αj m) (G.αk (n + 1)) c) := by
  classical
  set b : Profile X := tri G.a j k t (G.αj m) (G.αk (n + 1)) c with hb
  set base : Profile X := tri G.a j k t (G.αj m) (G.αk n) (G.a t) with hbase
  have hslice : ∀ p : X t,
      Function.update base t p = tri G.a j k t (G.αj m) (G.αk n) p := by
    intro p; rw [hbase]; unfold tri; rw [Function.update_idem]
  have hHi' : P.weakPref (Function.update base t cHi) b := by rw [hslice]; exact hHi
  have hLo' : P.weakPref b (Function.update base t cLo) := by rw [hslice]; exact hLo
  obtain ⟨p, hp⟩ :=
    WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.coordinate_slice_IVT_of_preferenceContinuous
      P base t b hUpper hLower hHi' hLo'
  refine ⟨p, ?_⟩
  rw [hslice] at hp; exact hp

/-- **The off-cal matching residual.**  Given a reference `p` whose exchange
`p → c` compensates the `j`-grid step at `(m, n)`, it also compensates the
`k`-grid step.  The sharply-isolated genuine cancellation content (the existence
of `p` is discharged by `offCalJHalf_of_IVT`).  Necessary under a rep
(`offCalCompensationMatch_of_additiveRep`); equivalent to the equal-spacing of the
two grids. -/
def OffCalCompensationMatch (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ (m n : ℕ) (c : X t), c ≠ G.rt → c ≠ G.st → ∀ p : X t,
    P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
             (tri G.a j k t (G.αj (m + 1)) (G.αk n) c) →
    P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)

/-- **Soundness gate: the matching residual is necessary under a rep (PROVED).**

Both grid steps have the same per-step utility increment `δ` (equal spacing, from
`spaced_j`/`spaced_k`), so a `p` with `V_t p = V_t c + δ` (forced by the `j`-half
premise) automatically satisfies the `k`-half.  Confirms the matching residual
hides nothing false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem offCalCompensationMatch_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) :
    OffCalCompensationMatch P j k t G := by
  have stepJ : ∀ m, R.V j (G.αj (m + 1))
      = R.V j (G.αj m) + (R.V t G.rt - R.V t G.st) := by
    intro m
    have h := (indiff_iff_score R).mp (G.spaced_j m)
    rw [score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at h
    linarith
  have stepK : ∀ n, R.V k (G.αk (n + 1))
      = R.V k (G.αk n) + (R.V t G.rt - R.V t G.st) := by
    intro n
    have h := (indiff_iff_score R).mp (G.spaced_k n)
    rw [score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at h
    linarith
  intro m n c hrt hst p hJ
  have hJ' := (indiff_iff_score R).mp hJ
  rw [score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at hJ'
  rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
  linarith [stepJ m, stepK n]

/-- **Strength characterization (PROVED): the matching residual follows from
all-background calibration + the canonical KLST `t`-block separability.**

This pins the bespoke `OffCalCompensationMatch` residual to the project's
*standard* R1 forward target.  Given full calibration, the diagonal step at the
calibration level `st` is free (`interiorDiagonalStep_st_of_allBackgrounds`); the
canonical KLST `t`-block separability `TBlockWeakIndependent` (necessary under a
rep, `tBlockWeakIndependent_of_additiveRep`; not A1-derivable, the strip probe)
transports it to the off-cal level `c`; chaining with the `j`-half premise closes
the `k`-half.

> **Honest scope note — NOT a main-chain discharge.**  This lemma is a
> *relative-strength* result: it shows `OffCalCompensationMatch` is **no stronger
> than** the canonical KLST `t`-block separability (the condition the entire R1
> development already reduces to), so carrying it adds no new assumption.  It is
> **deliberately not wired** into `gridDiagonalStepOffCal_of_calibratedGrid`: that
> chain uses the genuinely-*non-circular* continuum/IVT route (§D.3f–h), whereas
> deriving the level move from `TBlockWeakIndependent` would re-introduce exactly
> the circularity §D.2b flags (`TBlockWeakIndependent` is the weak-separability
> form of the target `TBlockDiagonalResidue`).  The value here is the
> characterization: the off-cal frontier does not grow beyond the standard KLST
> condition.  Audit `[propext, Quot.sound]`. -/
theorem offCalCompensationMatch_of_calibration_and_tBlock
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G)
    (hTB : TBlockWeakIndependent P j k t) :
    OffCalCompensationMatch P j k t G := by
  intro m n c hrt hst p hJ
  -- Diagonal step at the calibration level `st` (free from full calibration).
  have hst_step := interiorDiagonalStep_st_of_allBackgrounds G hcal m n
  -- Transport `st → c` by the canonical KLST `t`-block separability (both
  -- directions, giving the indifference `(αⱼ(m+1),αₖn,c) ∼ (αⱼm,αₖ(n+1),c)`).
  have hDc : P.indiff
      (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
      (tri G.a j k t (G.αj m) (G.αk (n + 1)) c) :=
    ⟨hTB G.a (G.αj (m + 1)) (G.αj m) (G.αk (n + 1)) (G.αk n) G.st c hst_step.1,
     hTB G.a (G.αj m) (G.αj (m + 1)) (G.αk n) (G.αk (n + 1)) G.st c hst_step.2⟩
  -- `k`-half = trans(`j`-half, diagonal step at `c`).
  exact gridThomsen_indiff_trans hJ hDc

/-- **Matched compensation from the `j`-half existence + the matching residual
(PROVED).**  Pure assembly: pick the `j`-compensating `p`, then the matching
residual upgrades it to compensate the `k`-step too.  Audit `[propext,
Quot.sound]`. -/
theorem matchedOffCalCompensation_of_jHalfExists_and_match
    {j k t : ι} (G : CalibratedJKGrid P j k t)
    (hJexists : ∀ (m n : ℕ) (c : X t), c ≠ G.rt → c ≠ G.st →
      ∃ p : X t, P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                          (tri G.a j k t (G.αj (m + 1)) (G.αk n) c))
    (hmatch : OffCalCompensationMatch P j k t G) :
    MatchedOffCalCompensation P j k t G := by
  intro m n c hrt hst
  obtain ⟨p, hp⟩ := hJexists m n c hrt hst
  exact ⟨p, hp, hmatch m n c hrt hst p hp⟩

/-- **R1.1b-level (PROVED): the off-cal diagonal step from the `j`-half existence
(continuum/IVT) + the matching residual.**

The genuine forward decomposition of `GridDiagonalStepOffCal`: the solvability/IVT
existence of the `j`-compensating level (`offCalJHalf_of_IVT`) plus the single
remaining cancellation residual `OffCalCompensationMatch` (necessary under a rep).
This declaration is **not** a `sorry`; it factors the open content into a
theorem-backed existence half and a sharply-named, necessity-proven matching
residual — the honest sharpening the §D.3f construction delivers.  Audit
`[propext, Quot.sound]`. -/
theorem gridDiagonalStepOffCal_of_jHalfExists_and_match
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (hJexists : ∀ (m n : ℕ) (c : X t), c ≠ G.rt → c ≠ G.st →
      ∃ p : X t, P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                          (tri G.a j k t (G.αj (m + 1)) (G.αk n) c))
    (hmatch : OffCalCompensationMatch P j k t G) :
    GridDiagonalStepOffCal P j k t G :=
  gridDiagonalStepOffCal_of_matchedCompensation G
    (matchedOffCalCompensation_of_jHalfExists_and_match G hJexists hmatch)


/-! ### §D.3g  Wiring the `j`-half existence through the topology bundle

`offCalJHalf_of_IVT` needs three things: connectedness of `X t`, the closed
contour sets at the reference, and a `t`-bracket `(cHi, cLo)`.  The first two are
*exactly* the `WakkerCoordinateTopology` bundle (`connected`, `continuous`), so
they are not separate assumptions — they are the project's standard §III.4.2
topology input.  The bracket is the §IV.2.6 Archimedean reach content: a `t`-level
that over-compensates the `j`-step and one that under-compensates it.  We package
the bracket as a named bundle `OffCalJBracket` (proved *necessary* under a rep —
the reach is automatic from `V_t`-coverage) and derive the full `j`-half existence
from {topology bundle + bracket}. -/

/-- **Off-cal `j`-bracket reach (the §IV.2.6 Archimedean content for the `j`-half).**

For each off-cal cell `(m, n, c)`, two `t`-levels bracketing the `j`-step
reference `(αⱼ (m+1), αₖ n, c)` from the slice over `(αⱼ m, αₖ n, ·)`:
* `cHi` with `(αⱼ m, αₖ n, cHi) ≽ (αⱼ (m+1), αₖ n, c)` (over-compensates), and
* `cLo` with `(αⱼ (m+1), αₖ n, c) ≽ (αⱼ m, αₖ n, cLo)` (under-compensates).

This is the reach pair the IVT crossing consumes; in Wakker's construction it is
supplied by the Archimedean escape of a strict `t`-standard-sequence grid. -/
def OffCalJBracket (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ (m n : ℕ) (c : X t), c ≠ G.rt → c ≠ G.st →
    ∃ cHi cLo : X t,
      P.weakPref (tri G.a j k t (G.αj m) (G.αk n) cHi)
                 (tri G.a j k t (G.αj (m + 1)) (G.αk n) c) ∧
      P.weakPref (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
                 (tri G.a j k t (G.αj m) (G.αk n) cLo)

/-- **Soundness gate: the `j`-bracket is necessary under a rep (modulo
`V_t`-reach) (PROVED).**

Given a representation and `V_t`-reach (some level scores at least `V_j (αⱼ (m+1))
− V_j (αⱼ m)` above `c`, some at most), the bracket holds: the over/under
witnesses are exactly those reach levels.  Confirms the bracket hides nothing
false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem offCalJBracket_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t)
    (hreach : ∀ (m n : ℕ) (c : X t), ∃ cHi cLo : X t,
      R.V t G.rt - R.V t G.st ≤ R.V t cHi - R.V t c ∧
      R.V t cLo - R.V t c ≤ R.V t G.rt - R.V t G.st) :
    OffCalJBracket P j k t G := by
  have stepJ : ∀ m, R.V j (G.αj (m + 1))
      = R.V j (G.αj m) + (R.V t G.rt - R.V t G.st) := by
    intro m
    have h := (indiff_iff_score R).mp (G.spaced_j m)
    rw [score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt] at h
    linarith
  intro m n c hrt hst
  obtain ⟨cHi, cLo, hHi, hLo⟩ := hreach m n c
  refine ⟨cHi, cLo, ?_, ?_⟩
  · rw [R.represents, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
    linarith [stepJ m]
  · rw [R.represents, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt]
    linarith [stepJ m]

/-- **The `j`-half existence from the topology bundle + the bracket (PROVED).**

Connectedness of `X t` and the closed contour sets come from the
`WakkerCoordinateTopology` bundle (`htop.connected`, `htop.continuous`); the
bracket witnesses come from `OffCalJBracket`.  Feeds `offCalJHalf_of_IVT`.  No
`sorry`.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem offCalJHalf_of_topology_and_bracket
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hbr : OffCalJBracket P j k t G) :
    ∀ (m n : ℕ) (c : X t), c ≠ G.rt → c ≠ G.st →
      ∃ p : X t, P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                          (tri G.a j k t (G.αj (m + 1)) (G.αk n) c) := by
  haveI : ConnectedSpace (X t) := htop.connected t
  intro m n c hrt hst
  obtain ⟨cHi, cLo, hHi, hLo⟩ := hbr m n c hrt hst
  exact offCalJHalf_of_IVT G m n c
    (htop.continuous (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)).1
    (htop.continuous (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)).2
    cHi cLo hHi hLo

/-- **R1.1b-level (PROVED, genuinely wired): the off-cal diagonal step from the
topology bundle + the `j`-bracket + the matching residual.**

The genuine forward discharge of `GridDiagonalStepOffCal`, with **no `sorry`**:
* connectedness + preference continuity (the `WakkerCoordinateTopology` bundle the
  project carries everywhere) discharge the IVT crossing;
* the §IV.2.6 Archimedean `OffCalJBracket` supplies the reach pair (necessary
  under a rep, `offCalJBracket_of_additiveRep`);
* the single genuine cross-pair residual is `OffCalCompensationMatch` (necessary
  under a rep, `offCalCompensationMatch_of_additiveRep`; not A1-derivable, the
  strip probe; not residue-derivable, §D.2b).

So the level move is no longer one opaque `sorry`: the continuum existence content
is theorem-backed, and the open content is exactly the equal-spacing matching
residual.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridDiagonalStepOffCal_of_topology_bracket_and_match
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hbr : OffCalJBracket P j k t G)
    (hmatch : OffCalCompensationMatch P j k t G) :
    GridDiagonalStepOffCal P j k t G :=
  gridDiagonalStepOffCal_of_jHalfExists_and_match G
    (offCalJHalf_of_topology_and_bracket htop G hbr) hmatch


/-! ### §D.3h  The wired calibrated-grid consumers (no `sorry`)

With §D.3f–g in place, the former `sorry`-bearing `gridDiagonalStepOffCal_of_calibratedGrid`
and its downstream chain are re-expressed as genuine theorems taking the two
named §IV.5 inputs explicitly: the §IV.2.6 Archimedean reach `OffCalJBracket`
(`hbr`) and the equal-spacing matching residual `OffCalCompensationMatch`
(`hmatch`), with the topology bundle `htop` discharging the continuum/IVT content.
None carries `sorry`. -/

/-- **R1.1b-level (PROVED, genuinely wired — no `sorry`): the premise-free
off-calibration diagonal step.**

This is the relocated, **strictly sharper** level-move obligation.  After §D.3b–e,
the diagonal step is theorem-backed at the two calibration levels `rt` and `st`,
so the genuine remaining §IV.5 content is only the step at a level `c ∉ {rt, st}`.

**Discharged (this session, §D.3f–g) — no `sorry`.**  The honest forward route is
the measuring-stick transport, now mechanized:
* connectedness of `X t` + preference continuity (the `WakkerCoordinateTopology`
  bundle `htop` the project carries everywhere) discharge the IVT crossing that
  produces the compensating reference level;
* the §IV.2.6 Archimedean reach `OffCalJBracket` supplies the bracket pair
  (necessary under a rep, `offCalJBracket_of_additiveRep`);
* the single genuine cross-pair residual is `OffCalCompensationMatch` — that the
  `j`-compensating level also compensates the `k`-step (necessary under a rep,
  `offCalCompensationMatch_of_additiveRep`; not A1-derivable, the strip probe; not
  residue-derivable, §D.2b).

So the former opaque `sorry` is replaced by a genuine delegation to
`gridDiagonalStepOffCal_of_topology_bracket_and_match`: the continuum/IVT content
is theorem-backed, and the open content is the sharply-named equal-spacing
matching residual carried as an explicit, necessity-proven structural input
(`hmatch`).  The bracket reach is carried as `hbr` (the §IV.2.6 escape content,
shared with WP-density).  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridDiagonalStepOffCal_of_calibratedGrid
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hbr : OffCalJBracket P j k t G)
    (hmatch : OffCalCompensationMatch P j k t G) :
    GridDiagonalStepOffCal P j k t G :=
  gridDiagonalStepOffCal_of_topology_bracket_and_match htop G hbr hmatch

/-- **R1.1b-level (PROVED by delegation): the level-move residual.**

Theorem-backed by delegation to the strictly-sharper premise-free
`gridDiagonalStepOffCal_of_calibratedGrid` via the proved bridge
`gridDiagonalLevelMoveResidual_of_offCalStep` (which folds in the now-free `rt`/`st`
calibration-level cases).  The open content is the off-cal step's named inputs
(`hbr`, `hmatch`).  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridDiagonalLevelMoveResidual_of_calibratedGrid
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hfwd : CalibrationOffAxisForwardData P j k t G)
    (hbr : OffCalJBracket P j k t G)
    (hmatch : OffCalCompensationMatch P j k t G) :
    GridDiagonalLevelMoveResidual P j k t G :=
  gridDiagonalLevelMoveResidual_of_offCalStep G
    (calibrationAllBackgrounds_of_calibratedGrid hjk hjt hkt hA1j hA1k hsolv htop G hfwd)
    (gridDiagonalStepOffCal_of_calibratedGrid hjk hjt hkt hA1j hA1k hsolv htop G hbr hmatch)

/-- **R1.1b-level (PROVED by delegation): the full diagonal-step level move.**

Composes the calibration (R1.1b-cal) with the level-move residual.  Audit
`[propext, Classical.choice, Quot.sound]` modulo the two named off-cal inputs. -/
theorem diagonalStepLevelMove_of_calibratedGrid
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hfwd : CalibrationOffAxisForwardData P j k t G)
    (hbr : OffCalJBracket P j k t G)
    (hmatch : OffCalCompensationMatch P j k t G)
    (hcal : CalibrationAllBackgrounds P j k t G)
    (m n : ℕ) (c : X t) :
    P.indiff (tri G.a j k t (G.αj (m+1)) (G.αk n) c)
             (tri G.a j k t (G.αj m) (G.αk (n+1)) c) :=
  (gridDiagonalLevelMoveResidual_of_calibratedGrid hjk hjt hkt hA1j hA1k hsolv htop G hfwd hbr hmatch)
    m n c (interiorDiagonalStep_st_of_allBackgrounds G hcal m n)

/-- **R1.1b (PROVED by delegation): the full grid diagonal step from the
calibrated grid.**

Routes through the two §D.3 obligations: all-background calibration supplies the
interior step at level `st`, and the level move lifts it to every `t`-level.
Audit `[propext, Classical.choice, Quot.sound]` modulo the named inputs. -/
theorem gridDiagonalStep_of_calibratedGrid
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hfwd : CalibrationOffAxisForwardData P j k t G)
    (hbr : OffCalJBracket P j k t G)
    (hmatch : OffCalCompensationMatch P j k t G) :
    GridDiagonalStep P j k t G := by
  intro m n c
  exact diagonalStepLevelMove_of_calibratedGrid hjk hjt hkt hA1j hA1k hsolv htop G hfwd hbr hmatch
    (calibrationAllBackgrounds_of_calibratedGrid hjk hjt hkt hA1j hA1k hsolv htop G hfwd)
    m n c

/-- **R1.1b (PROVED by delegation): grid Thomsen closure from the calibrated
grid.**

Composes the order-theory reduction `gridThomsenClosure_of_gridDiagonalStep` with
the diagonal-step crux `gridDiagonalStep_of_calibratedGrid`.  Audit
`[propext, Classical.choice, Quot.sound]` modulo the named inputs. -/
theorem gridThomsenClosure_of_calibratedGrid
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hfwd : CalibrationOffAxisForwardData P j k t G)
    (hbr : OffCalJBracket P j k t G)
    (hmatch : OffCalCompensationMatch P j k t G) :
    GridThomsenClosure P j k t G :=
  gridThomsenClosure_of_gridDiagonalStep G
    (gridDiagonalStep_of_calibratedGrid hjk hjt hkt hA1j hA1k hsolv htop G hfwd hbr hmatch)


/-! ## §E.  R1.1a — construction of the calibrated grid

R1.1a is the genuine multi-week §IV.5 measuring-stick construction.  Following the
project's B1 discipline (`NamedResidualBundleConstructionRoadmap.md`), we do **not**
leave it as one opaque `sorry`: we isolate the irreducible *existence* content into
a named seed-data residual `CalibratedGridSeedData`, prove the **grid assembly
fully theorem-backed** from it (no `sorry`), and prove the residual *necessary*
under a representation (the soundness gate).  The only remaining open obligation is
the seed-data existence itself — exactly the bare §IV.2/§IV.5 standard-sequence
seed at the third-coordinate measuring stick.

### What the seed data carries

`CalibratedGridSeedData` gives, over a common background `a`, the recursive
ingredients for **both** axis sequences calibrated against one `t`-exchange
`rt ↦ st`:

* the `t`-exchange `rt ≠ st` (the measuring-stick unit);
* `j`-grid recursion: `αj 0`, and a one-step extender `extJ` producing, from any
  `u : X j`, a next `u' : X j` with `(u, αk 0, rt) ∼ (u', αk 0, st)` (this is the
  `t`-calibrated `OneStepExtensible` on `j` at `k`-background `αk 0`);
* `k`-grid recursion: `αk 0`, and a one-step extender `extK` likewise on `k` at
  `j`-background `αj 0`;
* strictness seeds: the first `j`-step and first `k`-step are strict, and a
  one-step strict lift along each axis (so the grids are injective by
  `standardSequence_alpha_injective_of_strictStep`).

This is the honest §IV.5 content: the existence of two interlocking
`t`-calibrated standard sequences.  Restricted solvability + Archimedean +
essentiality + the topology one-step seam supply it (Wakker IV.2.6/IV.5); proving
*that* is the remaining frontier, isolated here. -/

/-- **Calibrated-grid seed data (the isolated §IV.5 existence residual).**

The recursive ingredients for the two `t`-calibrated axis sequences.  `extJ` /
`extK` are the `t`-calibrated one-step extenders; `firstStrictJ` / `firstStrictK`
+ `liftJ` / `liftK` are the strictness seeds making the grids injective. -/
structure CalibratedGridSeedData (P : ProductPref X) (j k t : ι) where
  /-- Common background. -/
  a    : Profile X
  /-- The `t`-exchange "from" value. -/
  rt   : X t
  /-- The `t`-exchange "to" value. -/
  st   : X t
  /-- The measuring-stick exchange is nontrivial. -/
  rt_ne_st : rt ≠ st
  /-- Seed `j`-grid point. -/
  j0   : X j
  /-- Seed `k`-grid point. -/
  k0   : X k
  /-- `t`-calibrated one-step extender on the `j`-axis (at `k`-background `k0`). -/
  extJ : ∀ u : X j, ∃ u' : X j,
    P.indiff (tri a j k t u k0 rt) (tri a j k t u' k0 st)
  /-- `t`-calibrated one-step extender on the `k`-axis (at `j`-background `j0`). -/
  extK : ∀ v : X k, ∃ v' : X k,
    P.indiff (tri a j k t j0 v rt) (tri a j k t j0 v' st)

/-- **Recursive `j`-grid from the seed extender** (chooses each next point). -/
noncomputable def CalibratedGridSeedData.gridJ
    {j k t : ι} (S : CalibratedGridSeedData P j k t) : ℕ → X j
  | 0     => S.j0
  | n + 1 => Classical.choose (S.extJ (S.gridJ n))

/-- **Recursive `k`-grid from the seed extender.** -/
noncomputable def CalibratedGridSeedData.gridK
    {j k t : ι} (S : CalibratedGridSeedData P j k t) : ℕ → X k
  | 0     => S.k0
  | n + 1 => Classical.choose (S.extK (S.gridK n))

/-- The `j`-grid satisfies the calibrating spacing by construction
(`Classical.choose_spec` on `extJ`). -/
theorem CalibratedGridSeedData.gridJ_spaced
    {j k t : ι} (S : CalibratedGridSeedData P j k t) (n : ℕ) :
    P.indiff (tri S.a j k t (S.gridJ n) S.k0 S.rt)
             (tri S.a j k t (S.gridJ (n + 1)) S.k0 S.st) :=
  Classical.choose_spec (S.extJ (S.gridJ n))

/-- The `k`-grid satisfies the calibrating spacing by construction. -/
theorem CalibratedGridSeedData.gridK_spaced
    {j k t : ι} (S : CalibratedGridSeedData P j k t) (n : ℕ) :
    P.indiff (tri S.a j k t S.j0 (S.gridK n) S.rt)
             (tri S.a j k t S.j0 (S.gridK (n + 1)) S.st) :=
  Classical.choose_spec (S.extK (S.gridK n))

/-- **Grid assembly (PROVED): a `CalibratedJKGrid` from the seed data.**

Packs the two recursive grids into a `CalibratedJKGrid`.  The `spaced_j` /
`spaced_k` fields are exactly `gridJ_spaced` / `gridK_spaced` — note the spacing
is stated with `αk 0` (resp. `αj 0`) on the off-axis coordinate, matching the
`CalibratedJKGrid` definition (the calibration is anchored on the axes; the
off-axis/all-background strengthening is the separate §D.3 obligation).  No
`sorry`.  Audit `[propext, Classical.choice, Quot.sound]`. -/
noncomputable def calibratedJKGrid_of_seedData
    {j k t : ι} (S : CalibratedGridSeedData P j k t) :
    CalibratedJKGrid P j k t where
  a        := S.a
  αj       := S.gridJ
  αk       := S.gridK
  rt       := S.rt
  st       := S.st
  spaced_j := by
    intro n
    -- gridJ_spaced uses k-background `k0 = gridK 0`; rewrite to match.
    have h := S.gridJ_spaced n
    simpa [CalibratedGridSeedData.gridK] using h
  spaced_k := by
    intro n
    have h := S.gridK_spaced n
    simpa [CalibratedGridSeedData.gridJ] using h

/-- **Soundness gate (PROVED): the seed data is necessary under a rep, modulo the
bare existence of the axis seed points and exchange.**

Given an additive representation and a nontrivial measuring-stick exchange
`rt ≠ st` whose `t`-utility gap is realized by both a `j`-step and a `k`-step at
*every* point (the surjectivity/solvability content), the extenders exist: each
`extJ u` is the `j`-value whose utility is `V_j u + (V_t rt − V_t st)`, supplied by
the rep's coverage hypothesis.  This confirms the seed-data shape hides nothing
false; the coverage hypotheses are the honest solvability residual.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem calibratedGridSeedData_extenders_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (rt st : X t) (j0 : X j) (k0 : X k)
    (hcovJ : ∀ u : X j, ∃ u' : X j,
      R.V j u' = R.V j u + (R.V t rt - R.V t st))
    (hcovK : ∀ v : X k, ∃ v' : X k,
      R.V k v' = R.V k v + (R.V t rt - R.V t st)) :
    (∀ u : X j, ∃ u' : X j,
        P.indiff (tri a j k t u k0 rt) (tri a j k t u' k0 st)) ∧
    (∀ v : X k, ∃ v' : X k,
        P.indiff (tri a j k t j0 v rt) (tri a j k t j0 v' st)) := by
  refine ⟨?_, ?_⟩
  · intro u
    obtain ⟨u', hu'⟩ := hcovJ u
    refine ⟨u', ?_⟩
    rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt, hu']
    ring
  · intro v
    obtain ⟨v', hv'⟩ := hcovK v
    refine ⟨v', ?_⟩
    rw [indiff_iff_score R, score_tri_eq R hjk hjt hkt, score_tri_eq R hjk hjt hkt, hv']
    ring

/-! ### §E.2  Injectivity of the assembled grids

The grids are injective once the axis steps are strict.  This is the
order-theoretic core (strict steps ⟹ strictly antitone ⟹ injective); we prove it
inline over the relevant slice map so the file needs no extra imports. -/

/-- **Strict-step slice map is injective (PROVED, inline).**

If `f : ℕ → Profile X` has every consecutive step strict (`f n ≻ f (n+1)`), then
the map is injective: strict steps chain (via weak-order transitivity) to a strict
preference `f a ≻ f b` for `a < b`, and `f a = f b` would make that preference
self-referential, contradicting irreflexivity (`¬ (x ≻ x)`).  Audit
`[propext, Quot.sound]`. -/
private theorem strictStepSlice_injective
    [ProductPref.IsWeakOrder P] (f : ℕ → Profile X)
    (hstep : ∀ n, P.strict (f n) (f (n + 1))) :
    Function.Injective f := by
  -- Strictly antitone: a < b → f a ≻ f b.
  have hanti : ∀ a b, a < b → P.strict (f a) (f b) := by
    intro a b hab
    induction b with
    | zero => omega
    | succ b ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hab with hlt | heq
        · -- f a ≻ f b ≻ f (b+1):  weak chain forward, and block the reverse.
          have h1 := ih hlt
          have h2 := hstep b
          refine ⟨ProductPref.IsWeakOrder.transitive _ _ _ h1.1 h2.1, ?_⟩
          intro hrev
          -- hrev : f (b+1) ≽ f a;  with f a ≽ f b gives f (b+1) ≽ f b, contradicting h2.
          exact h2.2 (ProductPref.IsWeakOrder.transitive _ _ _ hrev h1.1)
        · subst heq; exact hstep a
  intro a b hab
  by_contra hne
  rcases Nat.lt_or_ge a b with hlt | hge
  · have h := hanti a b hlt
    rw [hab] at h
    exact h.2 h.1
  · have hlt : b < a := lt_of_le_of_ne hge (fun h => hne h.symm)
    have h := hanti b a hlt
    rw [hab] at h
    exact h.2 h.1

/-- **Reversed strict-step slice injectivity (PROVED, inline).**

Same as `strictStepSlice_injective` but for the ascending direction
`f n ≺ f (n+1)` (i.e. `f (n+1) ≻ f n`).  Audit `[propext, Quot.sound]`. -/
private theorem strictStepSlice_injective_rev
    [ProductPref.IsWeakOrder P] (f : ℕ → Profile X)
    (hstep : ∀ n, P.strict (f (n + 1)) (f n)) :
    Function.Injective f := by
  have hmono : ∀ a b, a < b → P.strict (f b) (f a) := by
    intro a b hab
    induction b with
    | zero => omega
    | succ b ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hab with hlt | heq
        · have h1 := ih hlt
          have h2 := hstep b
          refine ⟨ProductPref.IsWeakOrder.transitive _ _ _ h2.1 h1.1, ?_⟩
          intro hrev
          exact h1.2 (ProductPref.IsWeakOrder.transitive _ _ _ hrev h2.1)
        · subst heq; exact hstep a
  intro a b hab
  by_contra hne
  rcases Nat.lt_or_ge a b with hlt | hge
  · have h := hmono a b hlt; rw [hab] at h; exact h.2 h.1
  · have hlt : b < a := lt_of_le_of_ne hge (fun h => hne h.symm)
    have h := hmono b a hlt; rw [hab] at h; exact h.2 h.1

/-- **Assembled `j`-grid injectivity from strict steps (PROVED).**

If every `j`-step of the assembled grid is strict at the fixed `(k0, rt)`
off-axis background (in the natural ascending direction `g (n+1) ≻ g n`), the
`j`-grid map is injective.  Reduces to `strictStepSlice_injective_rev` over the
slice `n ↦ tri a j k t (gridJ n) k0 rt`.  Audit `[propext, Quot.sound]`. -/
theorem gridJ_injective_of_strictSteps
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t)
    (S : CalibratedGridSeedData P j k t)
    (hstep : ∀ n,
      P.strict (tri S.a j k t (S.gridJ (n + 1)) S.k0 S.rt)
               (tri S.a j k t (S.gridJ n) S.k0 S.rt)) :
    Function.Injective S.gridJ := by
  have hcomp : Function.Injective
      (fun n => tri S.a j k t (S.gridJ n) S.k0 S.rt) :=
    strictStepSlice_injective_rev (fun n => tri S.a j k t (S.gridJ n) S.k0 S.rt) hstep
  intro m n hmn
  apply hcomp
  simp only [tri_eq_update_j S.a hjk hjt, hmn]

/-- **Assembled `k`-grid injectivity from strict steps (PROVED).** -/
theorem gridK_injective_of_strictSteps
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hkt : k ≠ t)
    (S : CalibratedGridSeedData P j k t)
    (hstep : ∀ n,
      P.strict (tri S.a j k t S.j0 (S.gridK (n + 1)) S.rt)
               (tri S.a j k t S.j0 (S.gridK n) S.rt)) :
    Function.Injective S.gridK := by
  have hcomp : Function.Injective
      (fun n => tri S.a j k t S.j0 (S.gridK n) S.rt) :=
    strictStepSlice_injective_rev (fun n => tri S.a j k t S.j0 (S.gridK n) S.rt) hstep
  intro m n hmn
  apply hcomp
  simp only [tri_eq_update_k S.a hkt, hmn]

/-! ### §E.2b  Option A capstone — grid + injectivity from a strict-step seam

The grid assembly and injectivity are now combined into the **Option A**
deliverable: from the seed data plus per-step strictness (in the natural
`(n+1) ≻ n` ascending direction at the off-axis background), produce a calibrated
grid with both axis maps injective.  Everything here is proved; the strictness
input is supplied by Option B below from the structural axioms + the explicit
seam. -/

/-- Strict-after-indifference chaining (weak order). -/
private theorem strict_of_strict_indiff
    [ProductPref.IsWeakOrder P] {x y z : Profile X}
    (hxy : P.strict x y) (hyz : P.indiff y z) : P.strict x z := by
  refine ⟨ProductPref.IsWeakOrder.transitive _ _ _ hxy.1 hyz.1, ?_⟩
  intro hzx
  exact hxy.2 (ProductPref.IsWeakOrder.transitive _ _ _ hyz.1 hzx)

/-- **`j`-grid strict step from spacing + a strict `t`-exchange (PROVED).**

The calibration `spaced_j` moves `t : rt → st`; combined with the `t`-exchange
being *strict* (`(·,·,rt) ≻ (·,·,st)`) at the next grid point, the constant-`rt`
step is strict in the ascending direction.  Audit `[propext, Quot.sound]`. -/
theorem gridJ_strictStep_of_tExchangeStrict
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (S : CalibratedGridSeedData P j k t)
    (htStrict : ∀ (u : X j) (v : X k),
      P.strict (tri S.a j k t u v S.rt) (tri S.a j k t u v S.st))
    (n : ℕ) :
    P.strict (tri S.a j k t (S.gridJ (n + 1)) S.k0 S.rt)
             (tri S.a j k t (S.gridJ n) S.k0 S.rt) :=
  -- (g(n+1),k0,rt) ≻ (g(n+1),k0,st) ∼ (gn,k0,rt).
  strict_of_strict_indiff (htStrict (S.gridJ (n+1)) S.k0)
    (gridThomsen_indiff_symm (S.gridJ_spaced n))

/-- **`k`-grid strict step from spacing + a strict `t`-exchange (PROVED).** -/
theorem gridK_strictStep_of_tExchangeStrict
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (S : CalibratedGridSeedData P j k t)
    (htStrict : ∀ (u : X j) (v : X k),
      P.strict (tri S.a j k t u v S.rt) (tri S.a j k t u v S.st))
    (n : ℕ) :
    P.strict (tri S.a j k t S.j0 (S.gridK (n + 1)) S.rt)
             (tri S.a j k t S.j0 (S.gridK n) S.rt) :=
  strict_of_strict_indiff (htStrict S.j0 (S.gridK (n+1)))
    (gridThomsen_indiff_symm (S.gridK_spaced n))

/-- **OPTION A (PROVED): calibrated grid with injective axes from the seed data +
a strict `t`-exchange.**

The full Option-A deliverable: from the seed data `S` and the single extra
hypothesis that the calibrating `t`-exchange `rt → st` is strictly preferred
everywhere (`htStrict`), produce a calibrated grid whose **both** axis maps are
injective.  No `sorry`.  The strict-exchange hypothesis is exactly the essential-
coordinate-`t` content, supplied by Option B from the structural axioms.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem calibratedJKGrid_with_injectivity_of_seedData
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (S : CalibratedGridSeedData P j k t)
    (htStrict : ∀ (u : X j) (v : X k),
      P.strict (tri S.a j k t u v S.rt) (tri S.a j k t u v S.st)) :
    ∃ G : CalibratedJKGrid P j k t,
      Function.Injective G.αj ∧ Function.Injective G.αk := by
  refine ⟨calibratedJKGrid_of_seedData S, ?_, ?_⟩
  · -- αj of the assembled grid is definitionally S.gridJ.
    exact gridJ_injective_of_strictSteps hjk hjt S
      (fun n => (gridJ_strictStep_of_tExchangeStrict S htStrict n))
  · exact gridK_injective_of_strictSteps hkt S
      (fun n => (gridK_strictStep_of_tExchangeStrict S htStrict n))

/-! ### §E.3  Option B — discharge the seam from structural axioms + topology

Following the design decision, the calibrated-grid construction takes the
`OneStepExtensible`/topology input **explicitly** in its signature (exactly as the
rest of Option B threads `WakkerCoordinateTopology`).  Option B then builds the
seed data from that seam and closes the construction via Option A — no `sorry`.

The remaining genuinely-open content (the bare §III.4.2 `OneStepExtensible` from
connectedness + continuity) is the topology seam already discharged elsewhere in
the project (`oneStepExtensible_of_wakkerCoordinateTopology_and_archimedeanEscape`),
carried here as an explicit hypothesis. -/

/-- **The `t`-calibrated one-step seam (the explicit topology input).**

For each axis, a one-step extender producing, from any point, a next point making
the `t`-calibrated indifference `(·, off-axis, rt) ∼ (next, off-axis, st)` hold.
This is `Core.OneStepExtensible` in the `tri` vocabulary at the measuring-stick
exchange `rt → st`; Wakker derives it from connectedness + continuity (the
§III.4.2 seam). -/
structure CalibratedOneStepSeam (P : ProductPref X) (j k t : ι)
    (a : Profile X) (rt st : X t) (j0 : X j) (k0 : X k) : Prop where
  /-- `t`-calibrated one-step extension on the `j`-axis (at `k`-background `k0`). -/
  extJ : ∀ u : X j, ∃ u' : X j,
    P.indiff (tri a j k t u k0 rt) (tri a j k t u' k0 st)
  /-- `t`-calibrated one-step extension on the `k`-axis (at `j`-background `j0`). -/
  extK : ∀ v : X k, ∃ v' : X k,
    P.indiff (tri a j k t j0 v rt) (tri a j k t j0 v' st)

/-- **Seed data from the explicit one-step seam (PROVED).**  A thin repackaging:
the seam's extenders are exactly the seed-data fields.  Audit `[propext,
Quot.sound]`. -/
def calibratedGridSeedData_of_seam
    {j k t : ι} {a : Profile X} {rt st : X t} {j0 : X j} {k0 : X k}
    (hrs : rt ≠ st)
    (seam : CalibratedOneStepSeam P j k t a rt st j0 k0) :
    CalibratedGridSeedData P j k t where
  a    := a
  rt   := rt
  st   := st
  rt_ne_st := hrs
  j0   := j0
  k0   := k0
  extJ := seam.extJ
  extK := seam.extK

/-- **Uniform strict `t`-exchange from A1-`t` + one strict instance (PROVED).**

`CoordinateOrderIndependent P t` transfers both the weak preference and the
non-reverse across backgrounds, so a single strict instance
`(u0,v0,rt) ≻ (u0,v0,st)` lifts to *every* background `(u,v)`.  This is the
essential-coordinate-`t` content the strict-exchange hypothesis of Option A needs.
Audit `[propext, Quot.sound]`. -/
theorem tExchangeStrict_of_a1t
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1t : CoordinateOrderIndependent P t)
    (a : Profile X) (rt st : X t) (u0 : X j) (v0 : X k)
    (hseed : P.strict (tri a j k t u0 v0 rt) (tri a j k t u0 v0 st))
    (u : X j) (v : X k) :
    P.strict (tri a j k t u v rt) (tri a j k t u v st) := by
  -- Rewrite each `tri … rt/st` as a single coordinate-`t` update over the packed
  -- background, so A1-`t` (CoordinateOrderIndependent on `t`) applies.
  have hpack : ∀ (uu : X j) (vv : X k) (c : X t),
      tri a j k t uu vv c
        = Function.update (Function.update (Function.update a j uu) k vv) t c := by
    intro uu vv c; rfl
  -- coordPref t (bg) rt st  is  weakPref (tri … rt) (tri … st).
  have hbgseed : Function.update (Function.update a j u0) k v0
      = Function.update (Function.update a j u0) k v0 := rfl
  rcases hseed with ⟨hw, hnr⟩
  refine ⟨?_, ?_⟩
  · -- weak direction transfers by A1-t.
    have : CoordinateOrderIndependent P t := hA1t
    exact this (Function.update (Function.update a j u0) k v0)
               (Function.update (Function.update a j u) k v) rt st hw
  · -- non-reverse transfers by A1-t (contrapositive: a reverse at (u,v) would
    -- transfer back to (u0,v0), contradicting hnr).
    intro hrev
    exact hnr (hA1t (Function.update (Function.update a j u) k v)
                    (Function.update (Function.update a j u0) k v0) st rt hrev)

/-- **OPTION B (PROVED): calibrated grid with injective axes from the structural
axioms + the explicit one-step / A1-`t` seam.**

The design-decision signature: the §III.4.2 `OneStepExtensible` content enters as
the explicit `seam`, and essential-coordinate-`t` strictness as `hA1t` + one
strict seed `hseed` (both legitimate structural inputs).  Builds the seed data
(`calibratedGridSeedData_of_seam`), lifts the strict exchange uniformly
(`tExchangeStrict_of_a1t`), and closes via Option A
(`calibratedJKGrid_with_injectivity_of_seedData`).  **No `sorry`.**  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem calibratedJKGrid_of_structuralAxioms_and_seam
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (rt st : X t) (j0 : X j) (k0 : X k)
    (hrs : rt ≠ st)
    (hA1t : CoordinateOrderIndependent P t)
    (hseed : P.strict (tri a j k t j0 k0 rt) (tri a j k t j0 k0 st))
    (seam : CalibratedOneStepSeam P j k t a rt st j0 k0) :
    ∃ G : CalibratedJKGrid P j k t,
      Function.Injective G.αj ∧ Function.Injective G.αk := by
  set S : CalibratedGridSeedData P j k t := calibratedGridSeedData_of_seam hrs seam with hS
  have htStrict : ∀ (u : X j) (v : X k),
      P.strict (tri S.a j k t u v S.rt) (tri S.a j k t u v S.st) := by
    intro u v
    -- S.a = a, S.rt = rt, S.st = st definitionally.
    exact tExchangeStrict_of_a1t hjk hjt hkt hA1t a rt st j0 k0 hseed u v
  exact calibratedJKGrid_with_injectivity_of_seedData hjk hjt hkt S htStrict

/-! ### §E.4  The seam discharge from `WakkerCoordinateTopology` (PROVED)

With Option A + Option B proved, the remaining wiring is mechanical: produce the
explicit `seam` (the §III.4.2 `OneStepExtensible`) from the project's standard
topology bundle `WakkerCoordinateTopology` + restricted solvability, exactly as
the rest of Option B does.  This closes the chain: structural axioms + topology
bundle ⟹ calibrated grid with injective axes.

The strict `t`-seed is taken as an explicit hypothesis at the chosen seed point
`(j0, k0)`, matching the §III.4 distinctness convention used elsewhere in the
project (it is essentially the `coordPref t` form of `Essential P t` localized to
the chosen seed; producing it from the bare `Essential P t` requires a base shift
that the calibrated-grid signature does not assume).  The exchange `rt ≠ st`
likewise sits explicit in the signature. -/

/-- **`CalibratedOneStepSeam` from `WakkerCoordinateTopology` + restricted
solvability (PROVED).**

Both extenders are direct instances of
`oneStepExtensible_of_wakkerCoordinateTopology_and_restrictedSolvability` at
coordinate `t` (the calibrating coordinate), with the off-axis coordinate's value
folded into the base.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem calibratedOneStepSeam_of_topology
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (a : Profile X) (rt st : X t) (j0 : X j) (k0 : X k) (hrs : rt ≠ st) :
    CalibratedOneStepSeam P j k t a rt st j0 k0 := by
  -- The topology+solvability discharge produces `OneStepExtensible` on coordinate
  -- `j` (resp. `k`) at the calibrating exchange `rt → st` on `t`, over the
  -- off-axis-pinned base.  The seam's `tri`-shape is the same `update`-stack
  -- (commuting `update`s on different coordinates).
  refine ⟨?_, ?_⟩
  · -- extJ: ∀ u, ∃ u', P.indiff (tri a j k t u k0 rt) (tri a j k t u' k0 st).
    intro u
    -- Set the off-axis-pinned base for coordinate `j`.
    set base_j : Profile X := Function.update a k k0 with hbase_j
    have hext_j : ProductPref.OneStepExtensible P j base_j t rt st :=
      WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.oneStepExtensible_of_wakkerCoordinateTopology_and_restrictedSolvability
        (j := j) (k := t) hsolv htop hjt base_j rt st hrs
    obtain ⟨u', hu'⟩ := hext_j u
    refine ⟨u', ?_⟩
    -- Bridge: tri a j k t u k0 rt = update (update base_j j u) t rt.
    have eL : tri a j k t u k0 rt =
        Function.update (Function.update base_j j u) t rt := by
      unfold tri
      rw [hbase_j, Function.update_comm hjk u k0 a]
    have eR : tri a j k t u' k0 st =
        Function.update (Function.update base_j j u') t st := by
      unfold tri
      rw [hbase_j, Function.update_comm hjk u' k0 a]
    rw [eL, eR]
    exact hu'
  · -- extK: ∀ v, ∃ v', P.indiff (tri a j k t j0 v rt) (tri a j k t j0 v' st).
    intro v
    set base_k : Profile X := Function.update a j j0 with hbase_k
    have hext_k : ProductPref.OneStepExtensible P k base_k t rt st :=
      WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.oneStepExtensible_of_wakkerCoordinateTopology_and_restrictedSolvability
        (j := k) (k := t) hsolv htop hkt base_k rt st hrs
    obtain ⟨v', hv'⟩ := hext_k v
    refine ⟨v', ?_⟩
    -- Bridge: tri a j k t j0 v rt = update (update base_k k v) t rt.
    have eL : tri a j k t j0 v rt =
        Function.update (Function.update base_k k v) t rt := by
      unfold tri
      -- update (update (update a j j0) k v) t rt
      --   = update (update base_k k v) t rt   (just unfolds base_k).
      rw [hbase_k]
    have eR : tri a j k t j0 v' st =
        Function.update (Function.update base_k k v') t st := by
      unfold tri
      rw [hbase_k]
    rw [eL, eR]
    exact hv'

/-- **R1.1a wired (PROVED): calibrated grid from structural axioms + topology
bundle.**

The full Option-A-then-Option-B chain wired through the project's standard
topology bundle.  `sorry`-free.  Inputs:
* the structural axiom `RestrictedSolvability` (already a structural field);
* `CoordinateOrderIndependent P t` (A1 on the calibrating coordinate, also a
  structural field);
* the topology bundle `WakkerCoordinateTopology P` (the §III.4.2 connectedness +
  preference continuity input the project carries explicitly);
* an explicit measuring-stick exchange `rt ≠ st` and a strict seed
  `(j0, k0, rt) ≻ (j0, k0, st)` at the chosen seed point — together they
  encode `Essential P t` localized to the seed (the §III.4 distinctness
  convention).

Audit `[propext, Classical.choice, Quot.sound]` modulo whatever the topology
bundle's projections audit (currently `[propext, Classical.choice, Quot.sound]`
post-Phase-71 with the `separable` field projected soundly). -/
theorem calibratedJKGrid_of_structuralAxioms_and_topology
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hsolv : RestrictedSolvability P)
    (hA1t : CoordinateOrderIndependent P t)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (a : Profile X) (rt st : X t) (j0 : X j) (k0 : X k)
    (hrs : rt ≠ st)
    (hseed : P.strict (tri a j k t j0 k0 rt) (tri a j k t j0 k0 st)) :
    ∃ G : CalibratedJKGrid P j k t,
      Function.Injective G.αj ∧ Function.Injective G.αk :=
  calibratedJKGrid_of_structuralAxioms_and_seam hjk hjt hkt a rt st j0 k0 hrs hA1t hseed
    (calibratedOneStepSeam_of_topology hjk hjt hkt hsolv htop a rt st j0 k0 hrs)

/-! ### §E.5  The bare-structural-axioms wrapper — honest reformulation

**Honest finding (this session):** the originally-stated bare wrapper

```
calibratedJKGrid_of_structuralAxioms : Essential ∧ RestrictedSolvability ∧
                                        Archimedean ⟹ ∃ G, ...
```

is **not provable as stated** — `WakkerCoordinateTopology P` is *not* derivable
from those structural axioms alone (per `RawAxiomDischargersTopology.lean` §5:
the project itself adopts the topology bundle as an explicit `Prop`-valued data
input).  Producing the bundle from bare axioms is the WP-T frontier and is
genuinely open.

The honest fix is to lift the topology bundle into the signature, matching the
project-wide convention.  The wrapper below is then a **theorem** (no `sorry`):
it is exactly `calibratedJKGrid_of_structuralAxioms_and_topology` with the same
inputs, presented as the "structural axioms" interface for downstream consumers.

> **Soundness:** the seam's extender shape is necessary under a rep
> (`calibratedGridSeedData_extenders_of_additiveRep`).  Audit picks up the project's
> standard §III.4.2 bracket-reach axioms transitively, exactly as the rest of
> Option B does. -/

/-- **R1.1a wrapper (PROVED): calibrated grid from structural axioms + topology
bundle + explicit seed.**

The honest signature: `RestrictedSolvability` + `CoordinateOrderIndependent P t`
(both structural fields) + the project's `WakkerCoordinateTopology` bundle (the
§III.4.2 input every other Option B theorem carries explicitly) + an explicit
exchange and strict seed.  Pure delegation to
`calibratedJKGrid_of_structuralAxioms_and_topology`; no `sorry`.

Audit `[propext, Classical.choice, Quot.sound]` + the project-standard
§III.4.2 bracket-reach axioms (inherited transitively). -/
theorem calibratedJKGrid_of_structuralAxioms
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hsolv : RestrictedSolvability P)
    (hA1t : CoordinateOrderIndependent P t)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (a : Profile X) (rt st : X t) (j0 : X j) (k0 : X k)
    (hrs : rt ≠ st)
    (hseed : P.strict (tri a j k t j0 k0 rt) (tri a j k t j0 k0 st)) :
    ∃ G : CalibratedJKGrid P j k t,
      Function.Injective G.αj ∧ Function.Injective G.αk :=
  calibratedJKGrid_of_structuralAxioms_and_topology
    hjk hjt hkt hsolv hA1t htop a rt st j0 k0 hrs hseed

/-! ## §F.  R1.2 — transport to all profiles (described; the remaining glue)

With R1.1a + R1.1b discharged, `TBlockDiagonalResidue P j k t` (the full,
non-grid residue) follows by transport:

1. Build the calibrated grid `G` (R1.1a) and the closure (R1.1b), hence the
   grid-restricted residue (`gridTBlockDiagonalResidue_of_closure`).
2. For arbitrary `x, z : X j`, `r, p : X k`, `w, c : X t`, bracket each value
   between consecutive grid points (Archimedean density: the strict grids escape
   every reference) and use restricted solvability + preference continuity to find
   the exact grid-indifferent value (the `X1` slice-indifference selector,
   `OptionB_ResidualSharedInfrastructure.lean`).
3. Transport the comparison through the brackets: the grid-restricted residue
   applies at the grid points, and continuity closes the limit.

This is the §IV.2.6/§IV.5 transport (roadmap R1.2), "moderate — mostly reuse once
R1.1 lands".  Stated here as the target the two `sorry`s above unlock; not yet
mechanized.

The downstream chain, once `TBlockDiagonalResidue P j k t` is a theorem at the
three coordinate-role permutations `(j,k,t)`, `(j,t,k)`, `(t,k,j)`:
`crossPairCancellationData_of_a1_and_oneThomsenResidue`
(`OptionB_C1aDiagonalUnifiedCapstone.lean`) ⟹ `CrossPairCancellationData`, then
`doubleCancellation_of_a1_and_oneThomsenResidue`
(`OptionB_C1aDiagonalHexagon.lean`) ⟹ the classical hexagon — closing R1.1 and,
with the already-theorem-backed residuals 2 and 3, all of Option B. -/

/-! ### §F.1  The grid-Thomsen named-input bundle and the `sorry`-free capstone

To present the grid-Thomsen route's residual frontier as a *single* object — and
to compose the whole `sorry`-free chain into one statement — we bundle the named
§IV.5/§IV.2.6 inputs the two forward constructions consume:

* `fwd`  — `CalibrationOffAxisForwardData` (off-axis shift: reach brackets + the
  two cross-pair matching residuals);
* `bracket` — `OffCalJBracket` (level move: the §IV.2.6 `j`-half reach);
* `match`  — `OffCalCompensationMatch` (level move: the equal-spacing matching
  residual).

Everything else in the chain is theorem-backed, so this bundle is *exactly* the
genuine open content of the grid-Thomsen route. -/

/-- **The grid-Thomsen named-input frontier (the genuine §IV.5/§IV.2.6 content).**

A single structure bundling the named, soundness-gated, A1-non-derivable inputs
that the `sorry`-free grid-Thomsen chain consumes.  Carrying this is the honest
residual frontier of the route; everything else is theorem-backed. -/
structure GridThomsenForwardFrontier (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop where
  /-- Off-axis calibration shift forward data (reach brackets + matching residuals). -/
  fwd     : CalibrationOffAxisForwardData P j k t G
  /-- Level-move `j`-half §IV.2.6 Archimedean reach bracket. -/
  bracket : OffCalJBracket P j k t G
  /-- Level-move equal-spacing matching residual. -/
  match'  : OffCalCompensationMatch P j k t G

/-- **Soundness gate: the whole frontier is necessary under a rep (PROVED).**

Each component is necessary (`calibrationOffAxisForwardData_of_additiveRep`,
`offCalJBracket_of_additiveRep`, `offCalCompensationMatch_of_additiveRep`), given
the `V_t`-reach the representation supplies.  Confirms the bundled frontier hides
nothing false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridThomsenForwardFrontier_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t)
    (hreachFwd : ∀ target : ℝ, ∃ cHi cLo : X t,
      target ≤ R.V t cHi ∧ R.V t cLo ≤ target)
    (hreachBr : ∀ (m n : ℕ) (c : X t), ∃ cHi cLo : X t,
      R.V t G.rt - R.V t G.st ≤ R.V t cHi - R.V t c ∧
      R.V t cLo - R.V t c ≤ R.V t G.rt - R.V t G.st) :
    GridThomsenForwardFrontier P j k t G where
  fwd     := calibrationOffAxisForwardData_of_additiveRep R hjk hjt hkt G hreachFwd
  bracket := offCalJBracket_of_additiveRep R hjk hjt hkt G hreachBr
  match'  := offCalCompensationMatch_of_additiveRep R hjk hjt hkt G

/-- **R1.1b capstone (PROVED, `sorry`-free): grid Thomsen closure from the
calibrated grid + the named frontier.**

Repackages `gridThomsenClosure_of_calibratedGrid` to consume the single bundled
frontier `GridThomsenForwardFrontier` instead of its three components separately.
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridThomsenClosure_of_frontier
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hfrontier : GridThomsenForwardFrontier P j k t G) :
    GridThomsenClosure P j k t G :=
  gridThomsenClosure_of_calibratedGrid hjk hjt hkt hA1j hA1k hsolv htop G
    hfrontier.fwd hfrontier.bracket hfrontier.match'

/-- **R1.2 capstone (PROVED, `sorry`-free): the grid-restricted
`TBlockDiagonalResidue` from the calibrated grid + the named frontier.**

Composes the closure capstone with the bridge `gridTBlockDiagonalResidue_of_closure`
(closure + A1-`j` ⟹ the `t`-level invariance of the `{j,k}`-comparison on grid
points).  This is the grid-Thomsen route's endpoint in the project's downstream
vocabulary: it produces the grid restriction of `TBlockDiagonalResidue` — exactly
the residue the R1.1 unified capstone (`crossPairCancellationData_of_a1_and_oneThomsenResidue`)
consumes (after the R1.2 transport from grid points to all profiles, §F above).
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridTBlockDiagonalResidue_of_frontier
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hfrontier : GridThomsenForwardFrontier P j k t G)
    (m n m' n' : ℕ) (w c : X t)
    (hw : P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  w)
                     (tri G.a j k t (G.αj m') (G.αk n') w)) :
    P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  c)
               (tri G.a j k t (G.αj m') (G.αk n') c) :=
  gridTBlockDiagonalResidue_of_closure hjk hjt hkt hA1j G
    (gridThomsenClosure_of_frontier hjk hjt hkt hA1j hA1k hsolv htop G hfrontier)
    m n m' n' w c hw

end ProductPref
end WakkerInfra

/-! ## Audit — the proved parts audit clean.

**This scaffold is now `sorry`-free.**  Both former open obligations have been
discharged this session by the genuine Wakker §IV.5 / §IV.2.6 measuring-stick
construction (§D.3a-fwd for the off-axis calibration shift, §D.3f–h for the
level move).  Each is now a **theorem** taking the genuine continuum + cross-pair
inputs explicitly:

* **off-axis one-step shift** (`calibrationOffAxisOneStep_of_calibratedGrid`):
  topology bundle (IVT crossing, `tCompensationExists_of_topology`) +
  `CalibrationOffAxisForwardData` (the §IV.2.6 reach brackets + the two cross-pair
  matching residuals, necessary under a rep);
* **level move** (`gridDiagonalStepOffCal_of_calibratedGrid`): topology bundle +
  `OffCalJBracket` (§IV.2.6 reach) + `OffCalCompensationMatch` (the equal-spacing
  matching residual, necessary under a rep).

So the grid-Thomsen closure `gridThomsenClosure_of_calibratedGrid` audits at
`[propext, Classical.choice, Quot.sound]` — **no `sorryAx`** — modulo the named,
proven-necessary structural inputs (the genuine §IV.5 cross-pair cancellation
content + §IV.2.6 Archimedean reach), exactly matching the project's honest
named-residual discipline.  All matching residuals are proved necessary under a
representation (`offCalCompensationMatch_of_additiveRep`,
`calibrationOffAxisForwardData_of_additiveRep`), not A1-derivable (the strip/Kz
probes), and not residue-derivable (§D.2b is circular).  This file remains NOT in
the umbrella import and NOT in `OptionB_AxiomCheck.lean` pending review. -/

#print axioms WakkerInfra.ProductPref.gridThomsenClosure_of_additiveRep
#print axioms WakkerInfra.ProductPref.gridTBlockDiagonalResidue_of_closure
#print axioms WakkerInfra.ProductPref.gridThomsenClosure_of_gridDiagonalStep
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_of_additiveRep
#print axioms WakkerInfra.ProductPref.baseCell_diagonalStep_at_calibrationLevel
#print axioms WakkerInfra.ProductPref.calibrationAllBackgrounds_of_additiveRep
#print axioms WakkerInfra.ProductPref.interiorDiagonalStep_st_of_allBackgrounds
#print axioms WakkerInfra.ProductPref.calibrationAllBackgrounds_of_axisCases_and_interior
#print axioms WakkerInfra.ProductPref.calibrationInteriorBackgrounds_of_additiveRep
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_of_calibration_and_levelMove
#print axioms WakkerInfra.ProductPref.gridDiagonalLevelMoveResidual_of_additiveRep
#print axioms WakkerInfra.ProductPref.interiorDiagonalStep_rt_of_interiorBackgrounds
#print axioms WakkerInfra.ProductPref.interiorDiagonalStep_at_calibrationLevels
#print axioms WakkerInfra.ProductPref.gridDiagonalLevelMoveResidual_of_offCalResidual
#print axioms WakkerInfra.ProductPref.calibrationAllBackgrounds_of_diagonalResidues
#print axioms WakkerInfra.ProductPref.diagonalStepLevelMove_of_tBlockDiagonalResidue
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_of_diagonalResidues
#print axioms WakkerInfra.ProductPref.calibratedJKGrid_of_seedData
#print axioms WakkerInfra.ProductPref.calibratedGridSeedData_extenders_of_additiveRep
#print axioms WakkerInfra.ProductPref.gridJ_injective_of_strictSteps
#print axioms WakkerInfra.ProductPref.gridK_injective_of_strictSteps
#print axioms WakkerInfra.ProductPref.calibratedJKGrid_with_injectivity_of_seedData
#print axioms WakkerInfra.ProductPref.tExchangeStrict_of_a1t
#print axioms WakkerInfra.ProductPref.calibratedJKGrid_of_structuralAxioms_and_seam
#print axioms WakkerInfra.ProductPref.calibratedOneStepSeam_of_topology
#print axioms WakkerInfra.ProductPref.calibratedJKGrid_of_structuralAxioms_and_topology


-- Brick 4 audits (premise-free off-cal step):
#print axioms WakkerInfra.ProductPref.gridDiagonalLevelMoveResidualOffCal_of_offCalStep
#print axioms WakkerInfra.ProductPref.gridDiagonalStepOffCal_of_offCalResidual
#print axioms WakkerInfra.ProductPref.gridDiagonalLevelMoveResidual_of_offCalStep

-- §D.3e-crux audits (level move now theorem-backed by delegation to the
-- premise-free off-cal step; soundness gate clean):
#print axioms WakkerInfra.ProductPref.gridDiagonalStepOffCal_of_additiveRep
#print axioms WakkerInfra.ProductPref.gridDiagonalLevelMoveResidual_of_calibratedGrid
#print axioms WakkerInfra.ProductPref.diagonalStepLevelMove_of_calibratedGrid

-- §D.3f audits (genuine forward construction: the off-cal level move factored
-- into a theorem-backed continuum existence half (`offCalJHalf_of_IVT`) + a
-- sharply-named matching residual `OffCalCompensationMatch`, both soundness-gated;
-- NONE carries `sorry`):
#print axioms WakkerInfra.ProductPref.gridDiagonalStepOffCal_of_matchedCompensation
#print axioms WakkerInfra.ProductPref.matchedOffCalCompensation_of_additiveRep
#print axioms WakkerInfra.ProductPref.offCalJHalf_of_IVT
#print axioms WakkerInfra.ProductPref.offCalKHalf_of_IVT
#print axioms WakkerInfra.ProductPref.offCalCompensationMatch_of_additiveRep
#print axioms WakkerInfra.ProductPref.offCalCompensationMatch_of_calibration_and_tBlock
#print axioms WakkerInfra.ProductPref.matchedOffCalCompensation_of_jHalfExists_and_match
#print axioms WakkerInfra.ProductPref.gridDiagonalStepOffCal_of_jHalfExists_and_match

-- §D.3g audits (the `j`-half existence wired through the topology bundle + the
-- Archimedean bracket; the rewired calibrated-grid consumers — NONE carries
-- `sorry`; the level-move `sorry` is ELIMINATED):
#print axioms WakkerInfra.ProductPref.offCalJBracket_of_additiveRep
#print axioms WakkerInfra.ProductPref.offCalJHalf_of_topology_and_bracket
#print axioms WakkerInfra.ProductPref.gridDiagonalStepOffCal_of_topology_bracket_and_match
#print axioms WakkerInfra.ProductPref.gridDiagonalStepOffCal_of_calibratedGrid
#print axioms WakkerInfra.ProductPref.gridDiagonalLevelMoveResidual_of_calibratedGrid
#print axioms WakkerInfra.ProductPref.gridDiagonalStep_of_calibratedGrid
#print axioms WakkerInfra.ProductPref.gridThomsenClosure_of_calibratedGrid

-- §F.1 capstone audits (bundled named frontier ⇒ closure ⇒ grid-restricted
-- TBlockDiagonalResidue; NONE carries `sorry`):
#print axioms WakkerInfra.ProductPref.gridThomsenForwardFrontier_of_additiveRep
#print axioms WakkerInfra.ProductPref.gridThomsenClosure_of_frontier
#print axioms WakkerInfra.ProductPref.gridTBlockDiagonalResidue_of_frontier

-- §D.3a-onestep audits (interior calibration now theorem-backed by delegation to
-- the atomic one-step off-axis shift; induction + soundness gate clean):
#print axioms WakkerInfra.ProductPref.calibrationInteriorBackgrounds_of_offAxisOneStep
#print axioms WakkerInfra.ProductPref.calibrationOffAxisOneStep_of_additiveRep
#print axioms WakkerInfra.ProductPref.calibrationInteriorBackgrounds_of_calibratedGrid

-- §D.3a-fwd audits (off-axis one-step shift genuinely discharged: IVT crossing +
-- the §IV.2.6 reach brackets + the two cross-pair matching residuals; NONE
-- carries `sorry`; the off-axis calibration `sorry` is ELIMINATED):
#print axioms WakkerInfra.ProductPref.tCompensationExists_of_topology
#print axioms WakkerInfra.ProductPref.calibrationOffAxisForwardData_of_additiveRep
#print axioms WakkerInfra.ProductPref.calibrationOffAxisOneStep_of_topology_and_forwardData
#print axioms WakkerInfra.ProductPref.calibrationOffAxisOneStep_of_calibratedGrid
#print axioms WakkerInfra.ProductPref.calibrationAllBackgrounds_of_calibratedGrid


/-! ## §G.  Research record — the four bricks, the open frontier, and the
       circularity findings

This section is the **honest record** of what this scaffold has and has not
established, written as a handoff for whoever continues the R1.1 work.

### G.1  What is theorem-backed (no `sorry`)

* **Necessity / soundness gates** for every named residual in the file:
  `gridThomsenClosure_of_additiveRep`, `gridDiagonalStep_of_additiveRep`,
  `calibrationAllBackgrounds_of_additiveRep`,
  `calibrationInteriorBackgrounds_of_additiveRep`,
  `gridDiagonalLevelMoveResidual_of_additiveRep`,
  `calibratedGridSeedData_extenders_of_additiveRep`.  Each confirms its target
  hides nothing false under any additive representation.

* **Order-theoretic engines** (audit `[propext, Quot.sound]`, no choice):
  `gridThomsen_indiff_refl/symm/trans`,
  `gridThomsen_axis_of_diagonalStep`, `gridThomsen_eqSum_of_diagonalStep`,
  `strictStepSlice_injective`, `strictStepSlice_injective_rev`,
  `strict_of_strict_indiff`.

* **Closure → diagonal-step reduction**: `gridThomsenClosure_of_gridDiagonalStep`
  reduces the entire `GridThomsenClosure` to the single `GridDiagonalStep`
  primitive (the equal-index-sum engine).

* **Closure → grid `T`-diag bridge**: `gridTBlockDiagonalResidue_of_closure`
  (closure + A1-`j` ⟹ grid-restricted `TBlockDiagonalResidue`).

* **Calibrated-grid construction (Option A → Option B → topology)**:
  - `calibratedJKGrid_of_seedData` — assemble grid from seed data;
  - `gridJ/K_injective_of_strictSteps` — injectivity from strict steps (inline);
  - `calibratedJKGrid_with_injectivity_of_seedData` — Option A;
  - `tExchangeStrict_of_a1t` — A1-`t` lifts strict exchange uniformly;
  - `calibratedJKGrid_of_structuralAxioms_and_seam` — Option B (from the seam);
  - `calibratedOneStepSeam_of_topology` — discharge the seam from
    `WakkerCoordinateTopology` + `RestrictedSolvability`;
  - `calibratedJKGrid_of_structuralAxioms_and_topology` — full chain;
  - `calibratedJKGrid_of_structuralAxioms` — honest reformulation taking the
    topology bundle (the original "bare axioms" signature was unprovable).

### G.2  The four bricks (sharpening of the open frontier)

Each brick proved a strict piece of the open content for free, narrowing the
genuinely-open frontier without circularity.

* **Brick 1 — Calibration axis cases are `rfl`.**  `calJ m 0 = G.spaced_j m` and
  `calK 0 n = G.spaced_k n` definitionally.  Composition theorem
  `calibrationAllBackgrounds_of_axisCases_and_interior` reduces
  `CalibrationAllBackgrounds` to the *interior* cases
  `CalibrationInteriorBackgrounds` (strictly positive on both off-axis indices).

* **Brick 2 — Diagonal step at level `st` from full calibration.**
  `interiorDiagonalStep_st_of_allBackgrounds` chains `calJ m n` and `calK m n` at
  their shared endpoint.  Lifts the step at the calibration level `st` by pure
  weak order; the genuine open content is then the level-move from `st` to other
  `t`-levels (`GridDiagonalLevelMoveResidual`).

* **Brick 3 — Diagonal step at level `rt` from interior calibration.**
  `interiorDiagonalStep_rt_of_interiorBackgrounds` chains the two halves of the
  *interior* calibration at their shared `st`-endpoint, giving the diagonal step
  at the *reference* level `rt` for all `(m, n)`.  Pure weak order, no A1, no
  solvability.

* **Brick 4 — The rt-step premise is redundant; drop it.**  The off-cal
  level-move residual `GridDiagonalLevelMoveResidualOffCal` carries an rt-step
  *premise* that brick 3 discharges for free.  Removing it gives the cleanest
  open statement `GridDiagonalStepOffCal`: "the diagonal step holds at every
  off-calibration `t`-level," premise-free, with bidirectional bridge theorems
  `gridDiagonalLevelMoveResidualOffCal_of_offCalStep`,
  `gridDiagonalStepOffCal_of_offCalResidual`, and the cleanest endpoint
  composition `gridDiagonalLevelMoveResidual_of_offCalStep`.

### G.3  The two former open statements (now theorem-backed, named inputs)

After the four bricks, the genuinely-open R1.1 forward content is isolated into
two theorems, both now **discharged** (no `sorry`) modulo explicit named inputs:

1. **`calibrationOffAxisOneStep_of_calibratedGrid`** — the atomic one-step
   off-axis background shift `CalibrationOffAxisOneStep` (the relocated, sharper
   interior-calibration obligation):
   ```
   (∀ m n, [calJ at αk n] → [calJ at αk (n+1)])  ∧
   (∀ m n, [calK at αj m] → [calK at αj (m+1)])
   ```
   Now a **theorem** delegating to
   `calibrationOffAxisOneStep_of_topology_and_forwardData`: the IVT crossing is
   theorem-backed from the `WakkerCoordinateTopology` bundle, and the §IV.2.6 reach
   + cross-pair matching enter as the named `CalibrationOffAxisForwardData`.  The
   full arbitrary-off-axis interior calibration
   `calibrationInteriorBackgrounds_of_calibratedGrid` follows by the free induction
   `calibrationInteriorBackgrounds_of_offAxisOneStep` (base case `spaced_j`/`spaced_k`).

2. **`gridDiagonalStepOffCal_of_calibratedGrid`** — the premise-free off-cal
   step `GridDiagonalStepOffCal` (the relocated, sharper level-move obligation):
   ```
   ∀ m n c, c ≠ G.rt → c ≠ G.st →
     P.indiff (tri G.a j k t (G.αj (m+1)) (G.αk n) c)
              (tri G.a j k t (G.αj m) (G.αk (n+1)) c)
   ```
   Now a **theorem** (§D.3f–h): the IVT crossing is theorem-backed from the
   topology bundle, the §IV.2.6 reach enters as the named `OffCalJBracket`, and the
   single cross-pair residual is the named `OffCalCompensationMatch`.

Both are proved necessary under any additive representation
(`calibrationOffAxisOneStep_of_additiveRep`,
`gridDiagonalStepOffCal_of_additiveRep`).  Neither named matching input is
A1-derivable (the Kz/Strip probes refute single-coordinate independence as a
sufficient input).

### G.4  Convergence / circularity finding (§D.2b)

The grid-Thomsen route does **not** bypass the cross-pair content.
`gridDiagonalStep_of_diagonalResidues` proves the entire grid diagonal step —
hence `GridThomsenClosure` — is **inter-derivable** with the cross-pair diagonal
residues `{K, J, T}`-diag of `OptionB_C1aDiagonalResidue.lean`:

* off-axis calibration *is* `K`-diag / `J`-diag content;
* the level move *is* `T`-diag content.

Since `K`-diag, `J`-diag, and `T`-diag are permutation-equivalent
(`OptionB_C1aDiagonalEquivalence.lean`) and `T`-diag is the very residual R1.1 is
trying to produce, **deriving the grid closure from those residues is circular
for R1.1**.  The grid route adds value only as a *structural repackaging* of the
open content — it does not eliminate it.

Practical consequence: the genuine cross-pair *matching* residuals (now isolated
as the named inputs `OffCalCompensationMatch` / `CalibrationOffAxisForwardData`)
**must** be discharged from restricted solvability + the third coordinate directly
(the genuine Wakker §IV.5 standard-sequence equal-spacing construction), not from
the existing diagonal residues.

### G.5  Honest reformulation finding (§E.5)

The originally-stated bare-axioms wrapper

```
calibratedJKGrid_of_structuralAxioms : Essential ∧ RestrictedSolvability ∧
                                        Archimedean ⟹ ∃ G, ...
```

was **not provable as stated**.  `WakkerCoordinateTopology P` is *not* derivable
from those structural axioms alone (per `RawAxiomDischargersTopology.lean` §5:
the project itself adopts the topology bundle as an explicit `Prop`-valued data
input).  The wrapper has been honestly reformulated to take the topology bundle
in its signature; it is now a theorem (no `sorry`).

### G.6  Suggested next steps

For whoever continues the R1.1 work, the two former obligations are now
theorem-backed modulo the named cross-pair *matching* residuals.  The genuinely
remaining mechanization is to **eliminate** those matching residuals (rather than
characterize + soundness-gate them) via the full standard-sequence equal-spacing
construction:

1. **Eliminate `CalibrationOffAxisForwardData.matchJ`/`matchK`** (inside
   `calibrationOffAxisOneStep_of_calibratedGrid`).  The IVT existence half is
   already theorem-backed (`tCompensationExists_of_topology`); what remains is to
   prove the IVT-produced compensation `t`-level *coincides* with the calibration
   target — the equal-spacing content.  Honest route: run the genuine §IV.5
   measuring-stick equal-spacing argument on the two interlocking standard
   sequences, NOT an appeal to `T`/`K`/`J`-diag (§D.2b is circular).

2. **Eliminate `OffCalCompensationMatch`** (inside
   `gridDiagonalStepOffCal_of_calibratedGrid`).  Same shape: the `j`-half
   existence is theorem-backed (`offCalJHalf_of_topology_and_bracket`) and the
   reach bracket is escape-grid-dischargeable (`offCalJBracket_of_escapeGrid`,
   pure order theory); what remains is the matching equation that the
   `j`-compensation also compensates the `k`-step — the equal-spacing content
   characterized as KLST `t`-block separability
   (`offCalCompensationMatch_of_calibration_and_tBlock`).

3. **Connect to the broader R1.1 chain.**  Already wired: the closure
   `gridThomsenClosure_of_calibratedGrid` (theorem-backed mod the named inputs)
   gives `GridThomsenClosure`, hence the grid-restricted `TBlockDiagonalResidue`
   (`gridTBlockDiagonalResidue_of_closure`).  The R1.2 transport (§F) lifts the
   grid-restricted residue to the full `TBlockDiagonalResidue P j k t`, closing
   R1.1 at one coordinate triple; permutation-equivalence then closes all three
   triples and the entire R1.1.

The scaffold is structurally complete and `sorry`-free; the remaining work is the
genuine §IV.5 equal-spacing mechanization, sharply localized to the named matching
residuals above.
-/
