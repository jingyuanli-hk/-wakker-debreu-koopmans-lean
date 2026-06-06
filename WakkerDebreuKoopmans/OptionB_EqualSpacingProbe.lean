/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-EQ0: derivability probe for the equal-spacing matching kernel

> **STATUS: `sorry`-free derivability probe (WP-EQ0 of
> `OptionB_EqualSpacingConstructionPlan.md`).**  Not in the umbrella import.

Before attempting the multi-week equal-spacing forward construction (WP-EQ1), the
project discipline (vindicated by `OptionB_C1aHexagonProbe`,
`OptionB_C1aStripProbe`, `OptionB_C1aKzProbe`, and the §5 gate) requires a
machine-checked **derivability probe**: confirm the *specific lever* the
construction will use is neither already-true-for-free nor secretly circular.

## The matching kernel, self-contained

The genuine open content (WP-EQ1a) is the **matching**: the `t`-level that
compensates a `j`-step is the *same* regardless of the `k`-background.  Stripped of
the calibrated-grid packaging (`OffCalCompensationMatch`,
`CalibrationOffAxisForwardData.matchJ`), its atomic logical content is:

```
CompensationMatch P j k t :=
  ∀ a, x x' : X j, v v' : X k, rt st : X t,
    indiff [x|v|rt] [x'|v|st]  →   -- j-step x→x' compensated by t-exchange rt→st at k = v
    indiff [x|v'|rt] [x'|v'|st]    -- ... and the SAME exchange compensates it at k = v'
```

i.e. the `j`-step's `t`-compensation is `k`-background-independent (equal spacing).

## What WP-EQ0 establishes (both proved below)

* **Probe A (sanity / solvability does real work):** A1 (single-coordinate
  independence on every coordinate) does **NOT** imply `CompensationMatch`, even at
  `n = 3` with all coordinates essential.  Countermodel: the comonotone,
  Thomsen-violating `Pkz` (reused from `OptionB_C1aKzProbe`).  So the matching is
  genuine cross-pair content; the forward construction *must* use restricted
  solvability + the measuring stick, exactly as the plan states.

* **Probe B (non-circularity):** `CompensationMatch` is **necessary under any
  additive representation** (`compensationMatch_of_additiveRep`).  Combined with
  Probe A, this confirms the matching is a *sound, A1-non-derivable* target — so
  WP-EQ1a is attacking a true statement by a genuinely-needed lever, not a rename
  of an axiom we already have.  (The §D.2b circularity — deriving it from the
  permutation-equivalent diagonal residues — is avoided by construction: this
  predicate is stated directly on the preference, not via the residues.)

## Verdict

`CompensationMatch` is **sound** (necessary under a rep) and **not A1-derivable**.
WP-EQ1a is therefore attacking the right statement with the right lever
(solvability + third coordinate).  The probe gives a GREEN light to WP-EQ1.

Imports `OptionB_C1aThirdCoordinate` (for `tri`, the score helpers),
`OptionB_C1aKzProbe` (to reuse the `Pkz` countermodel and its A1 proof), and
`OptionB_C1aKzAnchor` (for `KBlockWeakIndependent`, the §D scoping confirmation),
and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aThirdCoordinate
import WakkerDebreuKoopmans.OptionB_C1aKzProbe
import WakkerDebreuKoopmans.OptionB_C1aKzAnchor

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBEqualSpacingProbe

open WakkerInfra
open WakkerInfra.ProductPref
open OptionBC1aKzProbe

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-! ## §A.  The matching kernel as a self-contained preference predicate -/

/-- **The equal-spacing matching kernel.**

At distinct coordinates `j, k, t`, a `j`-step `x → x'` whose `t`-exchange
`rt → st` compensates it at `k`-background `v` is compensated by the *same*
`t`-exchange at any other `k`-background `v'`.  This is the `k`-background
independence of the `j`-step's `t`-compensation — the equal-spacing content the
calibrated-grid `OffCalCompensationMatch` / `CalibrationOffAxisForwardData.matchJ`
package (here stripped to its atomic logical form, directly on the preference). -/
def CompensationMatch (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (x x' : X j) (v v' : X k) (rt st : X t),
    P.indiff (tri a j k t x v rt) (tri a j k t x' v st) →
    P.indiff (tri a j k t x v' rt) (tri a j k t x' v' st)

/-! ## §B.  Probe B (non-circularity): `CompensationMatch` is necessary under a rep

The matching is a genuine consequence of having an additive representation: under
`R`, the premise forces `V_j x + V_t rt = V_j x' + V_t st` (the `V_k v` term
cancels on both sides), an equation **independent of the `k`-background**, so it
holds verbatim at `v'`.  This is exactly equal spacing: the `j`-step's size on the
`t`-stick does not see `k`.  So the WP-EQ1a target hides nothing false. -/

/-- Score split of a `tri` profile (local copy of the file-wide engine). -/
private theorem score_tri_local [ProductPref.IsWeakOrder P]
    (R : WakkerDebreuKoopmans.AdditiveRep P)
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

/-- **Probe B: `CompensationMatch` is necessary under a rep (PROVED).**

Under `R`, the premise `[x|v|rt] ∼ [x'|v|st]` scores to `V_j x + V_t rt =
V_j x' + V_t st` (the common `V_k v` and background terms cancel) — an equation
free of the `k`-background.  Hence it holds at `v'`, giving the conclusion.
Confirms the WP-EQ1a target is sound (equal spacing is forced by any rep).  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem compensationMatch_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : WakkerDebreuKoopmans.AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    CompensationMatch P j k t := by
  intro a x x' v v' rt st hprem
  have hp := (indiff_iff_score R).mp hprem
  rw [score_tri_local R hjk hjt hkt, score_tri_local R hjk hjt hkt] at hp
  -- hp : V_j x + V_k v + V_t rt + rest = V_j x' + V_k v + V_t st + rest.
  -- Cancel V_k v and rest: V_j x + V_t rt = V_j x' + V_t st.
  rw [indiff_iff_score R, score_tri_local R hjk hjt hkt, score_tri_local R hjk hjt hkt]
  -- goal at v': V_j x + V_k v' + V_t rt + rest = V_j x' + V_k v' + V_t st + rest.
  linarith

/-! ## §C.  Probe A (sanity): A1 does NOT imply `CompensationMatch`

We reuse the `Pkz` countermodel (`OptionB_C1aKzProbe`): utility `gKz (x 0) (x 1) +
x 2`, comonotone (A1 on every coordinate, `kz_coordinateOrderIndependent`) but
Thomsen-violating.  The non-additivity of `gKz` makes a `j`-step's size depend on
the `k`-background, so the matching fails. -/

/-- `Ukz` of a `tri` profile (local copy; the original in `OptionB_C1aKzProbe` is
`private`).  Since `ι = Fin 3` and `tri` updates all three coordinates, the
background `a` is irrelevant: the value is `gKz u v + c`. -/
private lemma Ukz_tri_local (a : Fin 3 → Fin 3) (u v c : Fin 3) :
    Ukz (tri a 0 1 2 u v c) = gKz u v + ((c).val : ℤ) := by
  unfold tri Ukz
  have e0 : (Function.update (Function.update (Function.update a 0 u) 1 v) 2 c) 0 = u := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  have e1 : (Function.update (Function.update (Function.update a 0 u) 1 v) 2 c) 1 = v := by
    rw [Function.update_of_ne (by decide), Function.update_self]
  have e2 : (Function.update (Function.update (Function.update a 0 u) 1 v) 2 c) 2 = c := by
    rw [Function.update_self]
  rw [e0, e1, e2]

/-- **Probe A: `CompensationMatch` FAILS on `Pkz` at `(j,k,t) = (0,1,2)`.**

`j`-step `x = 0 → x' = 1`; reference `t`-exchange `rt = 1 → st = 0`.
* At `k`-background `v = 0`: `[0|0|1] ∼ [1|0|0]` needs `gKz 0 0 + 1 = gKz 1 0 + 0`,
  i.e. `0 + 1 = 1 + 0` ✓ (the premise holds — the step `0→1` at `k=0` has size 1).
* At `k`-background `v' = 2`: the conclusion `[0|2|1] ∼ [1|2|0]` would need
  `gKz 0 2 + 1 = gKz 1 2 + 0`, i.e. `2 + 1 = 4 + 0`, `3 = 4` — **fails** (the step
  `0→1` at `k=2` has size 2, not 1: `gKz` is non-additive).
All `gKz` arithmetic settled by `decide`. -/
theorem kz_not_compensationMatch :
    ¬ CompensationMatch Pkz 0 1 2 := by
  intro hCM
  -- Premise at k-background v = 0, reference exchange rt = 1 → st = 0.
  have hprem : Pkz.indiff
      (tri (fun _ : Fin 3 => (0 : Fin 3)) 0 1 2 0 0 1)
      (tri (fun _ : Fin 3 => (0 : Fin 3)) 0 1 2 1 0 0) := by
    refine ⟨?_, ?_⟩ <;>
    · show Ukz _ ≤ Ukz _
      rw [Ukz_tri_local, Ukz_tri_local]; decide
  -- Apply matching at k-background v' = 2: forces [0|2|1] ∼ [1|2|0].
  have hconcl := hCM (fun _ => 0) 0 1 0 2 1 0 hprem
  obtain ⟨h1, _⟩ := hconcl
  -- First leg: Ukz [1|2|0] ≤ Ukz [0|2|1], i.e. gKz 1 2 + 0 ≤ gKz 0 2 + 1, i.e. 4 ≤ 3.
  have e1 : Ukz (tri (fun _ : Fin 3 => (0:Fin 3)) 0 1 2 1 2 0)
              ≤ Ukz (tri (fun _ : Fin 3 => (0:Fin 3)) 0 1 2 0 2 1) := h1
  rw [Ukz_tri_local, Ukz_tri_local] at e1
  revert e1; decide

/-- **Probe A verdict, packaged.**

A1 holds on every coordinate of `Pkz` (`kz_coordinateOrderIndependent`) yet
`CompensationMatch 0 1 2` fails.  So the equal-spacing matching is NOT an A1
consequence — restricted solvability + the third coordinate are genuinely required
(the countermodel's finite coordinates are not solvable).  Matches the
`KzTransfer` / `StripTransfer` probe verdicts. -/
theorem a1_does_not_imply_compensationMatch :
    (∃ (Y : Fin 3 → Type) (Q : ProductPref Y),
      ProductPref.IsWeakOrder Q ∧
      (∀ i, CoordinateOrderIndependent Q i) ∧
      ¬ CompensationMatch Q 0 1 2) :=
  ⟨fun _ => Fin 3, Pkz, kz_isWeakOrder, kz_coordinateOrderIndependent,
   kz_not_compensationMatch⟩

/-! ## §D.  Scoping confirmation: the kernel is the indifference shadow of
    `KBlockWeakIndependent`

The WP-EQ1a scoping (`OptionB_EqualSpacingWPEQ1aScoping.md`) rests on the claim that
`CompensationMatch` is exactly the indifference form of the KLST `k`-block
separability `KBlockWeakIndependent` (`OptionB_C1aKzAnchor`):
```
KBlockWeakIndependent : weakPref [u|v|c] [u'|v|c'] → weakPref [u|v'|c] [u'|v'|c']
```
We confirm the forward direction in Lean (mapping `u↦x, u'↦x', c↦rt, c'↦st`):
applying `KBlockWeakIndependent` in both `≽`-directions turns the `{j,t}`-difference
indifference at `k = v` into the one at `k = v'`.  This machine-confirms that
WP-EQ1a's real target is `KBlockWeakIndependent` from the structural axioms — the
same condition the downstream capstone `crossPairCancellationData_of_blockIndependence`
consumes — so closing it needs **no glue** to the existing chain. -/

/-- **Scoping confirmation: `CompensationMatch ⟸ KBlockWeakIndependent` (PROVED).**

`CompensationMatch` is the indifference shadow of the KLST `k`-block separability.
So the WP-EQ1a forward target is exactly `KBlockWeakIndependent` (necessary under a
rep, `kBlockWeakIndependent_of_additiveRep`), connecting directly to the
block-independence capstone with no glue.  Audit `[propext, Quot.sound]`. -/
theorem compensationMatch_of_kBlockWeakIndependent
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hKB : KBlockWeakIndependent P j k t) :
    CompensationMatch P j k t := by
  intro a x x' v v' rt st hprem
  exact ⟨hKB a x x' v v' rt st hprem.1, hKB a x' x v v' st rt hprem.2⟩

end OptionBEqualSpacingProbe
end CertificateChecklist
end WakkerRoadmap

/-! ## WP-EQ0 probe audit

* Probe B (sound): `compensationMatch_of_additiveRep` — the matching kernel is
  necessary under any additive representation (equal spacing is forced).
* Probe A (not free): `a1_does_not_imply_compensationMatch` — A1 on every
  coordinate does not imply it (the `Pkz` countermodel).
* Scoping (§D): `compensationMatch_of_kBlockWeakIndependent` — the kernel is the
  indifference shadow of KLST `k`-block separability, so WP-EQ1a's target is
  `KBlockWeakIndependent` (the existing downstream-capstone input).

Verdict: the WP-EQ1a target is sound and A1-non-derivable — GREEN light to attack
it with restricted solvability + the third coordinate (the genuine Wakker §IV.5
measuring-stick lever), not a one-line A1 or residue projection. -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBEqualSpacingProbe.compensationMatch_of_additiveRep
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEqualSpacingProbe.kz_not_compensationMatch
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEqualSpacingProbe.a1_does_not_imply_compensationMatch
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEqualSpacingProbe.compensationMatch_of_kBlockWeakIndependent
