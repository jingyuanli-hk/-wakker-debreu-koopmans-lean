/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — C1.a-3 global construction (session 3): the simultaneous closure

> **STATUS: `sorry`-free.  The simultaneous two-compensator closure — the sharpest
> single-background form of the crux, with the genuine blockage machine-checked.**
> Not in the umbrella import.

This file is session 3 of the C1.a-3 global construction: the **simultaneous closure**,
distinct from the single measuring stick.  Sessions 1–2 measured the `j`-step against
`t` and relocated across `k`-backgrounds (the wall = `KBlockWeakIndependent` across `k`).
The simultaneous closure instead measures **both** the `j`-step and the `k`-step against
`t` at the **same common interior background** `(αⱼ m, αₖ n)`, via two compensators — no
cross-background relocation.

## The simultaneous mechanism (mechanized here)

At the common background `[αⱼ m | αₖ n | ·]`:
* the **`j`-compensator** `p` : `[αⱼ m|αₖ n|p] ∼ [αⱼ(m+1)|αₖ n|c]` (C1.a-1, `j`-half);
* the **`k`-compensator** `p'` : `[αⱼ m|αₖ n|p'] ∼ [αⱼ m|αₖ(n+1)|c]` (C1.a-1 dual,
  `k`-half).

Both are single-coordinate-`t` levels over the *same* base.  The off-cal diagonal step
`[αⱼ(m+1)|αₖ n|c] ∼ [αⱼ m|αₖ(n+1)|c]` then holds **iff the two compensators coincide**
`[αⱼ m|αₖ n|p] ∼ [αⱼ m|αₖ n|p']` — pure weak order.  This is the sharpest "simultaneous"
form: the entire crux is now one single-background `t`-level coincidence.

## What this file delivers (all machine-checked, no `sorry`)

* `CompensatorsCoincide P j k t G m n p p'` — the named single-background coincidence.
* `diagonalOffCal_iff_compensatorsCoincide` — **the simultaneous equivalence** (pure
  weak order): the off-cal diagonal step at the cell ⟺ the `j`- and `k`-compensators
  coincide, given they are genuine compensators (C1.a-1 data).
* `compensatorsCoincide_iff_equalStepSize_of_additiveRep` — **the blockage, machine-
  checked**: under a rep, the compensators coincide iff the `j`-step and `k`-step have
  equal `t`-compensation magnitude at the common background — which the `spaced_j`/
  `spaced_k` calibration gives only at the *axis* backgrounds; at interior backgrounds
  it is the cross-pair equal-spacing (the target).
* `compensatorsCoincide_of_additiveRep` — soundness gate (coincidence holds under a
  rep, from equal spacing).

## Honest determination (the seventh confirmation, sharpest form)

The simultaneous closure reduces the crux, by pure weak order, to a **single-background
`t`-level coincidence** of the two compensators — no cross-background relocation, the
sharpest possible form.  But §B proves that coincidence is *equal `t`-compensation
magnitude of the `j`- and `k`-steps at the common interior background*, which the grid's
axis calibration (`spaced_j` at `αₖ 0`, `spaced_k` at `αⱼ 0`) supplies only on the axes;
the interior equal-magnitude is the cross-pair content (`CalibrationAllBackgrounds`
interior = block separability).  So the simultaneous closure does **not** escape the
wall — it relocates it to the cleanest single-background statement, confirming (seventh
machine-checked time) that the crux is the interior step-size equality, irreducible
without the global representation.  The classical lever that would force it
(`standard_sequence_unique` via value-level `hStrict`) is **blocked**: `hStrict` is not
free even for essential, solvable, connected coordinates (`hStrict_fails_for_plateau`,
and non-injective utilities like `x²` are essential+solvable yet violate it).

Imports `OptionB_C1aGridThomsen` (the grid, `CalibrationAllBackgrounds`).  Not in the
umbrella import.
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

/-! ## §A.  The simultaneous two-compensator equivalence (pure weak order) -/

private theorem sc_symm {x y : Profile X} (h : P.indiff x y) : P.indiff y x :=
  ⟨h.2, h.1⟩

private theorem sc_trans [ProductPref.IsWeakOrder P] {x y z : Profile X}
    (hxy : P.indiff x y) (hyz : P.indiff y z) : P.indiff x z :=
  ⟨ProductPref.IsWeakOrder.transitive _ _ _ hxy.1 hyz.1,
   ProductPref.IsWeakOrder.transitive _ _ _ hyz.2 hxy.2⟩

/-- **The single-background compensator coincidence.**

The `j`-compensator `p` and the `k`-compensator `p'` give the *same* `t`-level trade-off
over the common background `[αⱼ m | αₖ n | ·]`. -/
def CompensatorsCoincide (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (p p' : X t) : Prop :=
  P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
           (tri G.a j k t (G.αj m) (G.αk n) p')

/-- **The simultaneous closure equivalence (PROVED, pure weak order).**

Given a `j`-compensator `p` (`[αⱼ m|αₖ n|p] ∼ [αⱼ(m+1)|αₖ n|c]`) and a `k`-compensator
`p'` (`[αⱼ m|αₖ n|p'] ∼ [αⱼ m|αₖ(n+1)|c]`) over the common background, the off-cal
diagonal step at the cell holds **iff** the two compensators coincide.

Forward: diagonal `∼` chains `[αⱼ m|αₖ n|p] ∼ [αⱼ(m+1)|αₖ n|c] ∼ [αⱼ m|αₖ(n+1)|c] ∼
[αⱼ m|αₖ n|p']`.  Backward: reverse.  Pure weak order — the sharpest single-background
form of the crux.  Audit `[propext, Quot.sound]`. -/
theorem diagonalOffCal_iff_compensatorsCoincide
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (c p p' : X t)
    (hp  : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                    (tri G.a j k t (G.αj (m + 1)) (G.αk n) c))
    (hp' : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p')
                    (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)) :
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)
      ↔ CompensatorsCoincide P j k t G m n p p' := by
  unfold CompensatorsCoincide
  constructor
  · intro hdiag
    -- [αⱼm|αₖn|p] ∼ [αⱼ(m+1)|αₖn|c] ∼ [αⱼm|αₖ(n+1)|c] ∼ [αⱼm|αₖn|p']
    exact sc_trans hp (sc_trans hdiag (sc_symm hp'))
  · intro hcoin
    -- [αⱼ(m+1)|αₖn|c] ∼ [αⱼm|αₖn|p] ∼ [αⱼm|αₖn|p'] ∼ [αⱼm|αₖ(n+1)|c]
    exact sc_trans (sc_symm hp) (sc_trans hcoin hp')

/-! ## §B.  The blockage: coincidence IS interior equal step-size (machine-checked)

Under a representation, the compensator coincidence is the equation `V_t p = V_t p'`,
which (via the compensator definitions) is `V_j(αⱼ(m+1)) − V_j(αⱼ m) = V_k(αₖ(n+1)) −
V_k(αₖ n)` at the **common interior background** — the `j`-step and `k`-step have equal
size.  The grid's `spaced_j`/`spaced_k` give this only on the axes; interior equality is
the cross-pair content. -/

private theorem sc_score_tri (R : AdditiveRep P) {j k t : ι}
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

/-- **The blockage, machine-checked: under a rep, compensator coincidence is the
interior equal step-size (PROVED).**

Under a representation, given the compensator equations (`p` `j`-compensates, `p'`
`k`-compensates at the common background), the coincidence `CompensatorsCoincide` holds
**iff** the `j`-step and `k`-step have equal utility size:
`V_j (αⱼ (m+1)) − V_j (αⱼ m) = V_k (αₖ (n+1)) − V_k (αₖ n)`.  The compensator equations
force `V_t p = V_t c + (V_j-step)` and `V_t p' = V_t c + (V_k-step)`; coincidence is
`V_t p = V_t p'`, i.e. the two steps are equal.  This pins the simultaneous closure's
residual to the **interior step-size equality** — the cross-pair content (the axis
calibration gives it only at `αₖ 0` / `αⱼ 0`).  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem compensatorsCoincide_iff_equalStepSize_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (c p p' : X t)
    (hp  : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                    (tri G.a j k t (G.αj (m + 1)) (G.αk n) c))
    (hp' : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p')
                    (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)) :
    CompensatorsCoincide P j k t G m n p p'
      ↔ R.V j (G.αj (m + 1)) - R.V j (G.αj m) = R.V k (G.αk (n + 1)) - R.V k (G.αk n) := by
  -- Decode the two compensator equations.
  have hpe := (indiff_iff_score R).mp hp
  have hpe' := (indiff_iff_score R).mp hp'
  rw [sc_score_tri R hjk hjt hkt, sc_score_tri R hjk hjt hkt] at hpe hpe'
  -- hpe  : V_j(αⱼm) + V_k(αₖn) + V_t p  + rest = V_j(αⱼ(m+1)) + V_k(αₖn) + V_t c + rest
  -- hpe' : V_j(αⱼm) + V_k(αₖn) + V_t p' + rest = V_j(αⱼm) + V_k(αₖ(n+1)) + V_t c + rest
  unfold CompensatorsCoincide
  rw [indiff_iff_score R, sc_score_tri R hjk hjt hkt, sc_score_tri R hjk hjt hkt]
  constructor
  · intro hco
    -- hco decodes to V_t p = V_t p'.
    linarith
  · intro hstep
    linarith

/-- **Soundness gate (PROVED): the compensators coincide under a rep.**

Under a representation, the `j`-step and `k`-step both have utility size `V_t rt − V_t st`
(equal spacing, from `spaced_j`/`spaced_k`), so by
`compensatorsCoincide_iff_equalStepSize_of_additiveRep` the compensators coincide.
Confirms the simultaneous closure's coincidence hides nothing false — it is exactly the
(rep-guaranteed) equal spacing.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem compensatorsCoincide_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (c p p' : X t)
    (hp  : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                    (tri G.a j k t (G.αj (m + 1)) (G.αk n) c))
    (hp' : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p')
                    (tri G.a j k t (G.αj m) (G.αk (n + 1)) c)) :
    CompensatorsCoincide P j k t G m n p p' := by
  have stepJ : R.V j (G.αj (m + 1)) - R.V j (G.αj m) = R.V t G.rt - R.V t G.st := by
    have h := (indiff_iff_score R).mp (G.spaced_j m)
    rw [sc_score_tri R hjk hjt hkt, sc_score_tri R hjk hjt hkt] at h
    linarith
  have stepK : R.V k (G.αk (n + 1)) - R.V k (G.αk n) = R.V t G.rt - R.V t G.st := by
    have h := (indiff_iff_score R).mp (G.spaced_k n)
    rw [sc_score_tri R hjk hjt hkt, sc_score_tri R hjk hjt hkt] at h
    linarith
  rw [compensatorsCoincide_iff_equalStepSize_of_additiveRep R hjk hjt hkt G m n c p p' hp hp']
  rw [stepJ, stepK]

end ProductPref
end WakkerInfra

/-! ## C1.a-3 simultaneous-closure (session 3) audit

* §A (pure weak order): `diagonalOffCal_iff_compensatorsCoincide` — the off-cal diagonal
  step ⟺ the `j`- and `k`-compensators coincide at the common background (the sharpest
  single-background form of the crux, no cross-background relocation).
* §B (the blockage, machine-checked): `compensatorsCoincide_iff_equalStepSize_of_additiveRep`
  — coincidence IS the interior `j`-step = `k`-step utility equality;
  `compensatorsCoincide_of_additiveRep` — soundness gate (coincidence from equal spacing
  under a rep).

**Honest determination.**  The simultaneous closure reduces the crux to a single-background
`t`-level coincidence of the two compensators — no cross-background relocation, the
sharpest possible form.  §B proves that coincidence is the **interior step-size equality**
of the `j`- and `k`-steps, which the grid's axis calibration supplies only on the axes;
the interior equality is the cross-pair content (`CalibrationAllBackgrounds` interior =
block separability).  So the simultaneous closure does NOT escape the wall — it pins it to
the cleanest single-background statement (the seventh machine-checked confirmation).  The
classical lever (`standard_sequence_unique` via value-level `hStrict`) is blocked:
`hStrict` is not free even for essential/solvable/connected coordinates (non-injective
utilities are essential+solvable yet violate it; `hStrict_fails_for_plateau`).  The §6
fallback (`KBlockWeakIndependent` as the proven-necessary KLST input) stands.  Audit
`[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.diagonalOffCal_iff_compensatorsCoincide
#print axioms WakkerInfra.ProductPref.compensatorsCoincide_iff_equalStepSize_of_additiveRep
#print axioms WakkerInfra.ProductPref.compensatorsCoincide_of_additiveRep
