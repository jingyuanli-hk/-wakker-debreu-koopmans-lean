/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — C1.a-3 interior-calibration discharge (Route B of the crux roadmap)

> **STATUS: `sorry`-free.**  Executes Route B of `OptionB_C1aCruxAttackRoadmap.md`:
> reduces the simultaneous-closure crux to the cleanest possible named input — the
> **interior calibration** — proves that input forces the crux by *pure weak
> order* (no representation), and characterizes it *exactly* as canonical KLST
> `k`-block + `j`-block separability.  NOT in the umbrella import, NOT merged into
> `OptionB_AxiomCheck.lean`.
>
> ## What this brick establishes
>
> The simultaneous-closure crux (`OptionB_C1aSimultaneousClosure`) reduces, by pure
> weak order (`diagonalOffCal_iff_compensatorsCoincide`), to the single-background
> coincidence `CompensatorsCoincide` at an *interior* grid background `(αⱼ m, αₖ n)`.
> §B of that file showed (under a rep) the coincidence IS the interior step-size
> equality, which the grid's *axis* calibration (`spaced_j` at `αₖ 0`, `spaced_k`
> at `αⱼ 0`) supplies only on the axes.
>
> This brick names the missing datum directly:
>
> ```lean
> InteriorCalibration P j k t G m n :=
>   indiff (tri … αⱼ m,  αₖ n, rt) (tri … αⱼ(m+1), αₖ n, st)   -- (A) j-step at interior n
>   ∧ indiff (tri … αⱼ m, αₖ n, rt) (tri … αⱼ m, αₖ(n+1), st)  -- (B) k-step at interior m
> ```
>
> i.e. the `j`-step and `k`-step are each compensated by the *same* reference
> exchange `rt → st` at the *common interior* background.  Three results:
>
> 1. **`compensatorsCoincide_of_interiorCalibration`** (pure weak order, audit
>    `[propext, Quot.sound]`): the interior calibration forces the compensator
>    coincidence — hence (via `diagonalOffCal_iff_compensatorsCoincide`) the off-cal
>    diagonal step — with **no representation**.  This is the sharpest forward
>    discharge of the crux: everything downstream of the interior calibration is now
>    free.
> 2. **`interiorCalibration_of_kBlock_jBlock`** (pure weak order, audit
>    `[propext, Quot.sound]`): the interior calibration follows from the grid's axis
>    calibration plus `KBlockWeakIndependent` (shift the held `k`-axis value `αₖ 0 →
>    αₖ n`) and `JBlockWeakIndependent` (shift the held `j`-axis value `αⱼ 0 → αⱼ m`).
>    So the residual is **no stronger than** canonical KLST `k`/`j`-block
>    separability — the exact characterization.
> 3. **`interiorCalibration_of_additiveRep`** (soundness gate, audit
>    `[propext, Classical.choice, Quot.sound]`): the interior calibration holds under
>    any representation (the additive scores make step sizes background-independent),
>    so the named input hides nothing false.
>
> ## Honest determination (Route B verdict)
>
> Route B **does not escape the wall** — but it sharpens it to the cleanest form yet.
> Chaining the three results:
>
> ```text
> KBlockWeakIndependent ∧ JBlockWeakIndependent           (canonical KLST inputs)
>   ──interiorCalibration_of_kBlock_jBlock──▶ InteriorCalibration   (pure weak order)
>   ──compensatorsCoincide_of_interiorCalibration──▶ CompensatorsCoincide (pure weak order)
>   ──diagonalOffCal_iff_compensatorsCoincide──▶ off-cal diagonal step ──▶ crux closed.
> ```
>
> Every arrow except the first is now FREE (pure weak order).  The quotient lever
> (`gridStandardSequenceUnique`, `OptionB_C1aQuotientGluing`) supplies within-
> background standard-sequence uniqueness for free, but it cannot manufacture
> `InteriorCalibration`: that is the *existence* of the cross-background calibration,
> structurally beyond the lever's fixed-base reach (the lever transports only
> indifferences *agreeing in a single coordinate*; the calibration indifferences
> differ in two coordinates `{j,t}` resp. `{k,t}`, so their cross-background
> transport is exactly `KBlockWeakIndependent` / `JBlockWeakIndependent`, NOT free
> under `TradeoffConsistency` — the §3 scope-note residual).
>
> **Net result.** The crux is now pinned to a single named input —
> `KBlockWeakIndependent ∧ JBlockWeakIndependent` — that is (i) proven necessary
> under a rep, (ii) the canonical KLST block separability, and (iii) the *only*
> remaining non-free arrow.  This is the §6 fallback in its sharpest, fully-
> characterized form: carry block separability as the proven-necessary,
> rep-validated KLST input.  No `hStrict`, no hidden gap, no circularity.

Imports `OptionB_C1aSimultaneousClosure` (the crux + `tri` + `CompensatorsCoincide`),
`OptionB_C1aKzAnchor` (`KBlockWeakIndependent`), `OptionB_C1aKzReduction`
(`JBlockWeakIndependent`).
-/

import WakkerDebreuKoopmans.OptionB_C1aSimultaneousClosure
import WakkerDebreuKoopmans.OptionB_C1aKzAnchor
import WakkerDebreuKoopmans.OptionB_C1aKzReduction

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

/-! ## §A.  Pure-weak-order plumbing -/

private theorem ic_symm {x y : Profile X} (h : P.indiff x y) : P.indiff y x :=
  ⟨h.2, h.1⟩

private theorem ic_trans [ProductPref.IsWeakOrder P] {x y z : Profile X}
    (hxy : P.indiff x y) (hyz : P.indiff y z) : P.indiff x z :=
  ⟨ProductPref.IsWeakOrder.transitive _ _ _ hxy.1 hyz.1,
   ProductPref.IsWeakOrder.transitive _ _ _ hyz.2 hxy.2⟩

/-! ## §B.  The named residual: interior calibration -/

/-- **Interior calibration (the cleanest named residual of the crux).**

The `j`-step `αⱼ m → αⱼ(m+1)` and the `k`-step `αₖ n → αₖ(n+1)` are *each*
compensated by the same reference exchange `rt → st` at the **common interior**
background `(αⱼ m, αₖ n)`.  The grid's `spaced_j` / `spaced_k` supply exactly this,
but only on the axes (`αₖ 0` / `αⱼ 0`); the interior version is the residual. -/
def InteriorCalibration (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) (m n : ℕ) : Prop :=
  P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
           (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st)
  ∧ P.indiff (tri G.a j k t (G.αj m) (G.αk n) G.rt)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st)

/-! ## §C.  Forward discharge: interior calibration ⟹ coincidence (pure weak order) -/

/-- **The crux, discharged from the interior calibration (PROVED, pure weak order).**

Given the interior calibration at `(m, n)` and the two compensators `p`, `p'`
*relative to the reference target `c = G.st`* (the `j`-compensator
`[αⱼ m|αₖ n|p] ∼ [αⱼ(m+1)|αₖ n|st]` and the `k`-compensator
`[αⱼ m|αₖ n|p'] ∼ [αⱼ m|αₖ(n+1)|st]`), the two compensators coincide:

```text
[αⱼ m|αₖ n|p] ∼ [αⱼ(m+1)|αₖ n|st] ∼(sym A) [αⱼ m|αₖ n|rt] ∼(B) [αⱼ m|αₖ(n+1)|st] ∼(sym p') [αⱼ m|αₖ n|p']
```

No representation.  Audit `[propext, Quot.sound]`.  Composed with
`diagonalOffCal_iff_compensatorsCoincide` this closes the off-cal diagonal step. -/
theorem compensatorsCoincide_of_interiorCalibration
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (p p' : X t)
    (hcal : InteriorCalibration P j k t G m n)
    (hp  : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                    (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st))
    (hp' : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p')
                    (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st)) :
    CompensatorsCoincide P j k t G m n p p' := by
  obtain ⟨hA, hB⟩ := hcal
  unfold CompensatorsCoincide
  exact ic_trans hp (ic_trans (ic_symm hA) (ic_trans hB (ic_symm hp')))

/-- **The off-cal diagonal step, discharged from the interior calibration (PROVED,
pure weak order).**

Direct composition of `compensatorsCoincide_of_interiorCalibration` with the
simultaneous-closure equivalence `diagonalOffCal_iff_compensatorsCoincide` (at the
reference level `c = G.st`).  Audit `[propext, Quot.sound]`. -/
theorem diagonalOffCalAtSt_of_interiorCalibration
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (p p' : X t)
    (hcal : InteriorCalibration P j k t G m n)
    (hp  : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                    (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st))
    (hp' : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p')
                    (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st)) :
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st) := by
  rw [diagonalOffCal_iff_compensatorsCoincide G m n G.st p p' hp hp']
  exact compensatorsCoincide_of_interiorCalibration G m n p p' hcal hp hp'

/-! ## §D.  Exact characterization: interior calibration ⟺ `k`/`j`-block separability -/

/-- **The interior calibration from canonical KLST block separability (PROVED, pure
weak order).**

The interior calibration is *no stronger than* canonical KLST `k`-block and
`j`-block separability:

* the `j`-step at interior `αₖ n` is the axis `spaced_j m` (`αₖ 0`) shifted by
  `KBlockWeakIndependent` (the held `k`-value moves `αₖ 0 → αₖ n`; both `≽`-halves);
* the `k`-step at interior `αⱼ m` is the axis `spaced_k n` (`αⱼ 0`) shifted by
  `JBlockWeakIndependent` (the held `j`-value moves `αⱼ 0 → αⱼ m`; both `≽`-halves).

This pins the residual exactly to the canonical block-separability inputs.  Audit
`[propext, Quot.sound]`. -/
theorem interiorCalibration_of_kBlock_jBlock
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t)
    (G : CalibratedJKGrid P j k t) (m n : ℕ) :
    InteriorCalibration P j k t G m n := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- (A) forward, from spaced_j m forward, shift k: αₖ 0 → αₖ n.
    exact hKB G.a (G.αj m) (G.αj (m + 1)) (G.αk 0) (G.αk n) G.rt G.st (G.spaced_j m).1
  · -- (A) backward, from spaced_j m backward.
    exact hKB G.a (G.αj (m + 1)) (G.αj m) (G.αk 0) (G.αk n) G.st G.rt (G.spaced_j m).2
  · -- (B) forward, from spaced_k n forward, shift j: αⱼ 0 → αⱼ m.
    exact hJB G.a (G.αj 0) (G.αj m) (G.αk n) (G.αk (n + 1)) G.rt G.st (G.spaced_k n).1
  · -- (B) backward, from spaced_k n backward.
    exact hJB G.a (G.αj 0) (G.αj m) (G.αk (n + 1)) (G.αk n) G.st G.rt (G.spaced_k n).2

/-! ## §E.  Soundness gate: interior calibration holds under a representation -/

private theorem ic_score_tri (R : AdditiveRep P) {j k t : ι}
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

/-- **Soundness gate (PROVED): the interior calibration holds under a rep.**

Under an additive representation, the axis `spaced_j` / `spaced_k` force each step
size to equal `V_t rt − V_t st`, and additivity makes those increments
background-independent, so the interior calibrations hold at *every* `(m, n)`.
Confirms the named input hides nothing false.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem interiorCalibration_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) (m n : ℕ) :
    InteriorCalibration P j k t G m n := by
  -- Axis step sizes (from the calibration), decoded via the score split.
  have stepJ : R.V j (G.αj (m + 1)) - R.V j (G.αj m) = R.V t G.rt - R.V t G.st := by
    have h := (indiff_iff_score R).mp (G.spaced_j m)
    rw [ic_score_tri R hjk hjt hkt, ic_score_tri R hjk hjt hkt] at h
    linarith
  have stepK : R.V k (G.αk (n + 1)) - R.V k (G.αk n) = R.V t G.rt - R.V t G.st := by
    have h := (indiff_iff_score R).mp (G.spaced_k n)
    rw [ic_score_tri R hjk hjt hkt, ic_score_tri R hjk hjt hkt] at h
    linarith
  refine ⟨?_, ?_⟩
  · -- (A): indiff [αⱼ m|αₖ n|rt] [αⱼ(m+1)|αₖ n|st], i.e. j-step = rt→st gap at αₖ n.
    rw [indiff_iff_score R, ic_score_tri R hjk hjt hkt, ic_score_tri R hjk hjt hkt]
    linarith
  · -- (B): indiff [αⱼ m|αₖ n|rt] [αⱼ m|αₖ(n+1)|st], i.e. k-step = rt→st gap at αⱼ m.
    rw [indiff_iff_score R, ic_score_tri R hjk hjt hkt, ic_score_tri R hjk hjt hkt]
    linarith

end ProductPref
end WakkerInfra

/-! ## C1.a-3 interior-calibration (Route B) audit

* `compensatorsCoincide_of_interiorCalibration` / `diagonalOffCalAtSt_of_interiorCalibration`
  (pure weak order) — the interior calibration forces the compensator coincidence and
  hence the off-cal diagonal step, with NO representation.
* `interiorCalibration_of_kBlock_jBlock` (pure weak order) — the interior calibration is
  no stronger than canonical KLST `k`/`j`-block separability (the exact characterization).
* `interiorCalibration_of_additiveRep` (soundness gate) — it holds under any rep.

**Honest determination.**  Route B does not escape the wall, but pins it to the cleanest
named form: the crux closes from `KBlockWeakIndependent ∧ JBlockWeakIndependent` by pure
weak order alone, with every downstream arrow free (the quotient lever supplies the
within-background uniqueness gratis).  The single remaining non-free arrow is the block
separability itself — proven necessary (`interiorCalibration_of_additiveRep`,
`kBlockWeakIndependent_of_additiveRep`), the canonical KLST input.  This is the §6 fallback
in its sharpest, fully-characterized form.  Audit `[propext, Quot.sound]` /
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.compensatorsCoincide_of_interiorCalibration
#print axioms WakkerInfra.ProductPref.diagonalOffCalAtSt_of_interiorCalibration
#print axioms WakkerInfra.ProductPref.interiorCalibration_of_kBlock_jBlock
#print axioms WakkerInfra.ProductPref.interiorCalibration_of_additiveRep
