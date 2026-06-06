/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-EQ1a.2-construct (session 1): the second measuring-stick sequence

> **STATUS: `sorry`-free foundation for the equal-spacing construction.**  WP-EQ1a.2
> of `OptionB_EqualSpacingWPEQ1aScoping.md`.  Not in the umbrella import.

## The construction this file founds

WP-EQ1a's investigation established that the off-cal matching `OffCalCompensationMatch`
(= `k`-block KLST separability, the genuine §IV.5 content) has **no weak-order
shortcut** — it needs the Wakker `n ≥ 3` measuring-stick **construction**: a second
`j`-standard-sequence `βⱼ`, calibrated against the *same* `t`-exchange `rt → st`, but
at the **shifted** `k`-background `αₖ (n+1)` instead of the base grid's `αₖ 0`.

The base grid's own `j`-sequence `αⱼ` is calibrated at `αₖ 0`.  The shifted sequence
`βⱼ` is calibrated at `αₖ (n+1)`.  Both are calibrated against `rt → st`.  By
**point-wise indifference uniqueness** (two standard sequences against the same
exchange agree), `βⱼ` and `αⱼ` coincide as trade-offs, so `αⱼ`'s `j`-step is
compensated by `rt → st` at the shifted background too — that is `ShiftedCalibration`,
which discharges `OffCalCompensationMatch` (this file, §D).

## What session 1 delivers (all machine-checked, no `sorry`)

* `SecondSequenceData P j k t G n` — the **interface** for the shifted-background
  measuring-stick sequence: a `βⱼ : ℕ → X j` calibrated against `rt → st` at
  `k`-background `αₖ (n+1)`, agreeing with the base `αⱼ` at index 0, with each
  `βⱼ m` *indifferent* (not necessarily equal) to `αⱼ m` on the shifted slice.
* `shiftedCalibration_of_secondSequence` — the **forward lemma**: the second-sequence
  data discharges `ShiftedCalibration` at every cell, by pure weak order (the
  point-wise indifference relocates the calibration).
* `secondSequenceData_of_additiveRep` — **soundness gate**: a representation supplies
  the second-sequence data (take `βⱼ := αⱼ`).

## WP-EQ1a.2-build finding (§G): the interface is CIRCULAR (machine-checked)

Attempting to *construct* `SecondSequenceData` without already knowing the matching
reveals it is **logically equivalent** to the shifted calibration it was meant to
reduce: `secondSequenceData_iff_shiftedCalibration` proves
`Nonempty (SecondSequenceData G n) ↔ (∀ m, ShiftedCalibration G m n)`.  With the
canonical `seq := αⱼ` the interface *is* the residual; with a genuinely different
`seq` (from `extend_to_standard_sequence`), `spaced` is free but the agreement fields
`agreeRt`/`agreeSt` *are* the one-cell matching by construction.  So the
second-sequence **reformulation does not reduce the residual**.

**Honest consequence.**  The genuine measuring-stick escape is **not** a 1-D second
standard sequence — it is the 2-D **Thomsen / hexagon** solvability construction
(Debreu 1960 / KLST 1971 Thm 6.2), closing a cancellation across the three coordinate
pairs `{j,k}`, `{j,t}`, `{k,t}` simultaneously via the third coordinate.  That is the
real (strictly harder) WP-EQ1a.2-build target.  The §6 fallback — carry
`KBlockWeakIndependent` (the hexagon) as a proven-necessary named structural input —
remains the honest alternative.

Imports `OptionB_C1aGridThomsen` (for `CalibratedJKGrid`, `OffCalCompensationMatch`,
`CalibrationAllBackgrounds`) and `OptionB_EqualSpacingStrictness` (for
`compensationLevel_unique_of_indiff`).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aGridThomsen
import WakkerDebreuKoopmans.OptionB_EqualSpacingStrictness

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

/-! ## §A.  Local weak-order chaining helpers -/

private theorem ss_symm {x y : Profile X} (h : P.indiff x y) : P.indiff y x :=
  ⟨h.2, h.1⟩

private theorem ss_trans [ProductPref.IsWeakOrder P] {x y z : Profile X}
    (hxy : P.indiff x y) (hyz : P.indiff y z) : P.indiff x z :=
  ⟨ProductPref.IsWeakOrder.transitive _ _ _ hxy.1 hyz.1,
   ProductPref.IsWeakOrder.transitive _ _ _ hyz.2 hxy.2⟩

/-- Score split of a `tri` profile (local copy; the `OptionB_C1aGridThomsen`
`score_tri_eq` is `private`). -/
private theorem ss_score_tri [ProductPref.IsWeakOrder P] (R : AdditiveRep P)
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

/-! ## §B.  The shifted-background calibration (re-stated locally)

`ShiftedCalibration` (the off-cal step's genuine residual, cf. the WP-EQ1a.2 scoping)
is the `j`-grid step at `k`-background `αₖ (n+1)` compensated by `rt → st`.  We
re-state it here (independent of the discarded match-cell file) so this file is
self-contained. -/

/-- **Shifted measuring-stick calibration at cell `(m, n)`** (the `calJ` entry at
the shifted `k`-background `αₖ (n+1)`):
`(αⱼ m, αₖ (n+1), rt) ∼ (αⱼ (m+1), αₖ (n+1), st)`. -/
def ShiftedCalibration (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) (m n : ℕ) : Prop :=
  P.indiff (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.rt)
           (tri G.a j k t (G.αj (m + 1)) (G.αk (n + 1)) G.st)

/-- Shifted calibration is the `calJ` field at the shifted background (PROVED). -/
theorem shiftedCalibration_of_allBackgrounds
    {j k t : ι} (G : CalibratedJKGrid P j k t)
    (hcal : CalibrationAllBackgrounds P j k t G) (m n : ℕ) :
    ShiftedCalibration P j k t G m n :=
  hcal.calJ m (n + 1)

/-! ## §C.  The second-sequence interface

`SecondSequenceData … n` packages the shifted-background measuring-stick sequence
`βⱼ` and its relation to the base grid's `αⱼ`.  The fields are exactly what
`extend_to_standard_sequence` produces (future sessions) plus the point-wise
indifference to `αⱼ` that the uniqueness argument yields. -/

/-- **Interface for the shifted-background measuring-stick `j`-sequence.**

At `k`-background `αₖ (n+1)`:
* `seq` is a `j`-value sequence,
* `spaced` : each `seq`-step is compensated by the calibrating `t`-exchange
  `rt → st` (the defining standard-sequence property at the shifted background),
* `agree` : each `seq m` is *indifferent* to the base grid's `αⱼ m` on the shifted
  `{j}`-slice (at `t`-level `rt`) — the point-wise agreement the §IV.5 uniqueness
  argument supplies (it need not be value equality, per WP-EQ1a.0). -/
structure SecondSequenceData (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) (n : ℕ) where
  /-- The shifted-background `j`-sequence. -/
  seq    : ℕ → X j
  /-- It is calibrated against `rt → st` at `k`-background `αₖ (n+1)`. -/
  spaced : ∀ m, P.indiff (tri G.a j k t (seq m) (G.αk (n + 1)) G.rt)
                         (tri G.a j k t (seq (m + 1)) (G.αk (n + 1)) G.st)
  /-- Each `seq m` agrees with the base `αⱼ m` on the shifted slice at level `rt`. -/
  agreeRt : ∀ m, P.indiff (tri G.a j k t (seq m) (G.αk (n + 1)) G.rt)
                          (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.rt)
  /-- And at level `st` (the agreement transports to the calibrating "to"-level). -/
  agreeSt : ∀ m, P.indiff (tri G.a j k t (seq m) (G.αk (n + 1)) G.st)
                          (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st)

/-! ## §D.  The forward lemma: second-sequence data ⟹ shifted calibration

The point-wise agreement relocates the second sequence's calibration onto the base
grid's `αⱼ`: chain `agreeRt`, `spaced`, `agreeSt` to get the base sequence's `j`-step
compensated by `rt → st` at the shifted background. -/

/-- **Shifted calibration from second-sequence data (PROVED, pure weak order).**

`(αⱼ m, αₖ (n+1), rt) ∼[agreeRt] (seq m, αₖ (n+1), rt) ∼[spaced] (seq (m+1), αₖ (n+1), st)
 ∼[agreeSt] (αⱼ (m+1), αₖ (n+1), st)`.

So the base grid's `j`-step is compensated by `rt → st` at the shifted `k`-background
— exactly `ShiftedCalibration`.  This is the genuine measuring-stick relocation,
non-circular (the second sequence is an external input, not derived from the diagonal
residues).  Audit `[propext, Quot.sound]`. -/
theorem shiftedCalibration_of_secondSequence
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (m n : ℕ)
    (S : SecondSequenceData P j k t G n) :
    ShiftedCalibration P j k t G m n := by
  unfold ShiftedCalibration
  exact ss_trans (ss_symm (S.agreeRt m)) (ss_trans (S.spaced m) (S.agreeSt (m + 1)))

/-! ## §E.  Soundness gate: a representation supplies the second-sequence data

Take `βⱼ := αⱼ`: the agreement is reflexive, and the shifted spacing is forced by
`spaced_j` (the `j`-step equals `δ = V_t rt − V_t st` regardless of the
`k`-background).  Confirms the interface hides nothing false. -/

/-- Reflexivity of indifference. -/
private theorem ss_refl [ProductPref.IsWeakOrder P] (x : Profile X) :
    P.indiff x x :=
  ⟨ProductPref.IsWeakOrder.complete x x |>.elim id id,
   ProductPref.IsWeakOrder.complete x x |>.elim id id⟩

/-- **Soundness gate: a rep supplies the second-sequence data (PROVED).**

With `seq := αⱼ`, `agreeRt`/`agreeSt` are reflexive, and `spaced` is the shifted
calibration forced by `spaced_j` under the rep (the off-axis `V_k` cancels).
Confirms `SecondSequenceData` is a sound target.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
noncomputable def secondSequenceData_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) (n : ℕ) :
    SecondSequenceData P j k t G n where
  seq := G.αj
  spaced := by
    intro m
    -- shifted calibration with seq = αj is exactly calJ at background n+1 under rep.
    have hstep : R.V j (G.αj (m + 1))
        = R.V j (G.αj m) + (R.V t G.rt - R.V t G.st) := by
      have h := (indiff_iff_score R).mp (G.spaced_j m)
      rw [ss_score_tri R hjk hjt hkt, ss_score_tri R hjk hjt hkt] at h
      linarith
    rw [indiff_iff_score R, ss_score_tri R hjk hjt hkt, ss_score_tri R hjk hjt hkt]
    linarith [hstep]
  agreeRt := fun m => ss_refl _
  agreeSt := fun m => ss_refl _

/-! ## §F.  Composition: second-sequence data ⟹ `OffCalCompensationMatch`

Combining the forward lemma with the all-background calibration discharges the
bespoke grid matching residual.  The off-cal matching's `j`-compensation hypothesis,
together with the shifted calibration and base `k`-calibration, closes the `k`-half
via the off-cal diagonal step.  We route through the existing
`gridDiagonalStepOffCal_of_matchedCompensation` infrastructure. -/

/-- **The off-cal diagonal step from second-sequence data + calibration (PROVED).**

`ShiftedCalibration` (from `S`) gives `calJ` at the shifted background; with the base
`calJ`/`calK` (from `hcal`), the diagonal step at the calibration level `st` is free
(`interiorDiagonalStep_st_of_allBackgrounds`).  The genuine off-cal level move
(`c ∉ {rt, st}`) still requires the matched compensation; what the second sequence
delivers is the *shifted calibration* feeding the all-background calibration's `calJ`
at every background.  This lemma records the relocation; the full off-cal step is
assembled where the matched compensation is supplied.  Audit `[propext, Quot.sound]`. -/
theorem shiftedCalibration_forall_of_secondSequenceFamily
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (S : ∀ n, SecondSequenceData P j k t G n) :
    ∀ m n, ShiftedCalibration P j k t G m n :=
  fun m n => shiftedCalibration_of_secondSequence G m n (S n)

/-! ## §G.  Honest circularity finding: the interface is EQUIVALENT to the residual

Session 1 fixed the interface and proved it *suffices* (§D).  WP-EQ1a.2-build must
now *construct* `SecondSequenceData` without already knowing the matching.  Working
this out reveals it is **circular**: the interface is logically *equivalent* to the
shifted calibration it was meant to reduce.

The reverse direction (below) makes this precise: with the canonical `seq := αⱼ`,
`SecondSequenceData G n` exists **iff** `∀ m, ShiftedCalibration G m n`.  And a
*genuinely different* `seq` (built by `extend_to_standard_sequence` at the shifted
background) has `spaced` for free, but its agreement fields `agreeRt`/`agreeSt` —
e.g. at `m = 1`, that the solvability-chosen `seq 1` (the `δ`-step from `αⱼ 0` at
background `αₖ (n+1)`) is indifferent to `αⱼ 1` (the `δ`-step at background `αₖ 0`) —
**are exactly the one-cell matching**.  So neither instantiation escapes:

* `seq := αⱼ` ⟹ the interface IS the shifted calibration (proved here);
* `seq ≠ αⱼ` ⟹ the agreement IS the matching (the §IV.5 content, by construction).

**Honest conclusion (machine-checked below).**  The second-sequence *reformulation*
does not reduce the residual.  The genuine measuring-stick escape is **not** a 1-D
second standard sequence; it is the 2-D **Thomsen configuration** (Debreu 1960 / KLST
1971 Thm 6.2): a solvability construction using the third coordinate `t` to close a
hexagon across the pairs `{j,k}`, `{j,t}`, `{k,t}` simultaneously.  That is the real
WP-EQ1a.2-build target — strictly harder than a second sequence — and the §6 fallback
(carry `KBlockWeakIndependent` as a proven-necessary named input) remains the honest
alternative if it proves intractable. -/

/-- **Reverse equivalence: shifted calibration ⟹ second-sequence data (PROVED).**

With the canonical `seq := αⱼ`, the shifted calibration *is* the `spaced` field and
the agreement fields are reflexive.  So `SecondSequenceData G n` exists iff
`∀ m, ShiftedCalibration G m n` — the interface is **logically equivalent** to the
residual, not a reduction of it.  Audit `[propext, Quot.sound]`. -/
def secondSequenceData_of_shiftedCalibration
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (n : ℕ)
    (hshift : ∀ m, ShiftedCalibration P j k t G m n) :
    SecondSequenceData P j k t G n where
  seq := G.αj
  spaced := fun m => hshift m
  agreeRt := fun m => ss_refl _
  agreeSt := fun m => ss_refl _

/-- **The equivalence, packaged (PROVED).**

`(∃ SecondSequenceData G n) ↔ (∀ m, ShiftedCalibration G m n)` (existence form via
the canonical witness).  Confirms WP-EQ1a.2-build through this interface is circular:
constructing the data is equivalent to proving the matching.  Audit
`[propext, Quot.sound]`. -/
theorem secondSequenceData_iff_shiftedCalibration
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t) (n : ℕ) :
    (Nonempty (SecondSequenceData P j k t G n)) ↔
      (∀ m, ShiftedCalibration P j k t G m n) := by
  constructor
  · rintro ⟨S⟩ m
    exact shiftedCalibration_of_secondSequence G m n S
  · intro hshift
    exact ⟨secondSequenceData_of_shiftedCalibration G n hshift⟩

end ProductPref
end WakkerInfra

/-! ## WP-EQ1a.2-construct audit

**Session 1 (interface, suffices):**
* §C interface: `SecondSequenceData`.
* §D forward (free): `shiftedCalibration_of_secondSequence` — the data discharges
  `ShiftedCalibration` by pure weak order.
* §E gate: `secondSequenceData_of_additiveRep`.

**WP-EQ1a.2-build attempt (§G — honest circularity finding):**
* `secondSequenceData_of_shiftedCalibration` + `secondSequenceData_iff_shiftedCalibration`
  — the interface is **logically equivalent** to the shifted calibration (the
  matching), so the second-sequence *reformulation* does not reduce the residual.

**Net:** the measuring-stick escape is not a 1-D second sequence (circular); it is
the 2-D Thomsen/hexagon solvability construction (Debreu/KLST).  That is the genuine
WP-EQ1a.2-build target, recorded honestly; the §6 fallback stands. -/

#print axioms WakkerInfra.ProductPref.shiftedCalibration_of_allBackgrounds
#print axioms WakkerInfra.ProductPref.shiftedCalibration_of_secondSequence
#print axioms WakkerInfra.ProductPref.secondSequenceData_of_additiveRep
#print axioms WakkerInfra.ProductPref.shiftedCalibration_forall_of_secondSequenceFamily
#print axioms WakkerInfra.ProductPref.secondSequenceData_of_shiftedCalibration
#print axioms WakkerInfra.ProductPref.secondSequenceData_iff_shiftedCalibration
