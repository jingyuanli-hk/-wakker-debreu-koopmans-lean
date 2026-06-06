/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-C1.a endpoint: the hexagon as a named, proven-necessary residual

This file closes WP-C1.a at the honest endpoint dictated by the two probes
(`OptionB_C1aHexagonProbe.lean`, `OptionB_C1aStripProbe.lean`):

* A1 (single-coordinate independence) does **not** imply the hexagon
  `DoubleCancellation` (probe `Pcm`), and
* A1 does **not** imply `StripTransfer` either (probe `Pstrip`).

So the genuine cross-pair §IV.5 cancellation content of the hexagon is *not*
free from the structural axioms.  Following the §5/WP-CI/WP-density discipline,
the honest deliverable is to bundle that content into a **single named structural
residual**, prove the hexagon follows from it by a clean reduction, and prove the
whole bundle is **necessary** under any additive representation (so carrying it
hides nothing false).

## What this file delivers (all machine-checked)

* `HexagonResidualData P j k t` — the named §IV.5 cancellation residual on the
  pair `{j,k}` with measuring-stick coordinate `t`, bundling the three
  precisely-targeted, individually-sound pieces from
  `OptionB_C1aThirdCoordinate.lean`:
  - **J2 existence** (the transfer-level supplier — restricted-solvability /
    IVT content);
  - **`KzTransfer`** (the `{k,t}` tradeoff-transfer — cross-pair content);
  - **`StripTransfer`** (the `t`-block independence strip — KLST content).
* `doubleCancellation_of_hexagonResidualData` — the **sound reduction**:
  `DoubleCancellation P j k` from the residual, by composing the WP-C1.a forward
  steps (`thirdCoordinateTransfer_of_components` then
  `doubleCancellation_of_thirdCoordinateTransfer`).  Pure weak-order transitivity.
* `hexagonResidualData_of_additiveRep` — **necessity of the whole bundle**: under
  an additive representation whose `t`-utility realizes the P1-forced levels
  (`htlevel`, the honest solvability residual), all three pieces hold.  So the
  residual is sound; it adds no false content.
* `doubleCancellation_of_additiveRep_via_residual` — a sanity capstone: the
  hexagon's *own* necessity (already `doubleCancellation_of_additiveRep`) factors
  through this residual, confirming the residual is exactly the right strength
  (neither too weak to give DC nor stronger than what a rep supplies).

## Honest determination (the WP-C1.a verdict)

WP-C1.a is **not** dischargeable from {A1 + the structural axioms} by a finite
projection — both probes refute that.  The hexagon's content is the named residual
`HexagonResidualData`, which is:
* **sufficient** for `DoubleCancellation` (`doubleCancellation_of_hexagonResidualData`),
* **necessary** under any representation with adequate `t`-coverage
  (`hexagonResidualData_of_additiveRep`), and
* **strictly stronger than A1** (probes `Pcm`, `Pstrip`).

The *full forward construction* of `HexagonResidualData` from restricted
solvability + connectedness + the Archimedean escape grid (the J2 bracket reach
and the §IV.5 strip/transfer) is the genuine multi-week Wakker §IV.5 frontier.
This file pins that frontier to a single sound, necessary named input — exactly
the WP-CI/WP-density pattern (coordinate independence and the escape grid are
likewise carried as proven-necessary structural ingredients).

This file imports `OptionB_C1aThirdCoordinate` and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_C1aThirdCoordinate

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

/-- **The named §IV.5 hexagon-cancellation residual.**

On the pair `{j,k}` with measuring-stick coordinate `t`, this bundles the three
precisely-targeted pieces the probes proved are *not* A1-derivable but *are*
necessary under a representation:

* `j2` — **transfer-level existence**: for every datum a level `w : X t` realizing
  the `{j,t}`-compensation `[x|r|w] ∼ [y|r|c]` (restricted solvability / IVT
  content);
* `kz` — **`KzTransfer`**: the matching `{k,t}`-compensation (cross-pair §IV.5);
* `strip` — **`StripTransfer`**: the `t`-block independence strip (KLST block
  independence).

Together they are sufficient for the hexagon (`doubleCancellation_of_hexagonResidualData`)
and necessary under a representation (`hexagonResidualData_of_additiveRep`). -/
structure HexagonResidualData (P : ProductPref X) (j k t : ι) : Prop where
  /-- Transfer-level existence: the `{j,t}`-compensation level `w` exists. -/
  j2 : ∀ (a : Profile X) (x y : X j) (r : X k),
        ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t))
  /-- The `{k,t}` tradeoff-transfer residual. -/
  kz : KzTransfer P j k t
  /-- The `t`-block independence strip residual. -/
  strip : StripTransfer P j k t

/-- **WP-C1.a sound reduction: the hexagon from the named residual.**

`DoubleCancellation P j k` follows from `HexagonResidualData P j k t` (distinct
`j,k,t`) by composing the two WP-C1.a forward steps:
`thirdCoordinateTransfer_of_components` assembles the transfer from the bundle,
then `doubleCancellation_of_thirdCoordinateTransfer` closes the hexagon by pure
weak-order transitivity.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem doubleCancellation_of_hexagonResidualData
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjt : j ≠ t) (hkt : k ≠ t)
    (H : HexagonResidualData P j k t) :
    DoubleCancellation P j k :=
  doubleCancellation_of_thirdCoordinateTransfer hjt hkt
    (thirdCoordinateTransfer_of_components H.j2 H.kz H.strip)

/-- **Necessity of the whole hexagon residual (soundness witness).**

Under an additive representation `R`, if the `t`-utility realizes the level forced
by P1 (`htlevel` — the honest restricted-solvability residual the probes showed is
not free), then all three pieces of `HexagonResidualData` hold:

* `j2` — choose `w` with `V_t w = V_t (a t) + (V_j y − V_j x)`; the scored
  indifference `[x|r|w] ∼ [y|r|c]` is then an algebraic identity;
* `kz` — `kzTransfer_of_additiveRep`;
* `strip` — `stripTransfer_of_additiveRep`.

So the residual hides nothing false: every representation (with adequate
`t`-coverage) supplies it. -/
theorem hexagonResidualData_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (htlevel : ∀ (a : Profile X) (x y : X j),
      ∃ w : X t, R.V t w = R.V t (a t) + (R.V j y - R.V j x)) :
    HexagonResidualData P j k t := by
  have hkj : k ≠ j := Ne.symm hjk
  have htj : t ≠ j := Ne.symm hjt
  have htk : t ≠ k := Ne.symm hkt
  -- Score of a `tri` profile (the standard three-coordinate split).
  have score_tri : ∀ (a : Profile X) (u : X j) (v : X k) (c : X t),
      (∑ i, R.V i (tri a j k t u v c i))
        = R.V j u + R.V k v + R.V t c
          + ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
    intro a u v c
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
      have hij : i ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij]
    rw [hrest]; ring
  refine ⟨?_, kzTransfer_of_additiveRep R hjk hjt hkt,
            stripTransfer_of_additiveRep R hjk hjt hkt⟩
  -- J2 existence from `htlevel`.
  intro a x y r
  obtain ⟨w, hw⟩ := htlevel a x y
  refine ⟨w, ?_⟩
  rw [indiff_iff_score R, score_tri, score_tri, hw]; ring

/-- **Sanity capstone: the hexagon's own necessity factors through the residual.**

`doubleCancellation_of_additiveRep` already proves the hexagon is necessary under
a representation.  Here we re-derive it *through* `HexagonResidualData` (given the
`t`-coverage), confirming the residual is exactly the right strength: composing
`hexagonResidualData_of_additiveRep` with `doubleCancellation_of_hexagonResidualData`
recovers `DoubleCancellation`.  Audit foundational-only. -/
theorem doubleCancellation_of_additiveRep_via_residual
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (htlevel : ∀ (a : Profile X) (x y : X j),
      ∃ w : X t, R.V t w = R.V t (a t) + (R.V j y - R.V j x)) :
    DoubleCancellation P j k :=
  doubleCancellation_of_hexagonResidualData hjt hkt
    (hexagonResidualData_of_additiveRep R hjk hjt hkt htlevel)

end ProductPref
end WakkerInfra

/-! ## WP-C1.a endpoint audit -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_hexagonResidualData
#print axioms WakkerInfra.ProductPref.hexagonResidualData_of_additiveRep
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_additiveRep_via_residual
