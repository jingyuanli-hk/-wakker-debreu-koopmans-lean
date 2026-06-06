/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 groundwork: `StripTransfer` from weakPref-level `t`-block
  independence

This file makes a further genuine reduction on **R1.1** (the §IV.5 cross-pair
cancellation crux) of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`, building on the
level-independence result (`OptionB_C1aStripLevels.lean`).

## The reduction

`StripTransfer` is an *indifference* statement (`∼ → ∼`).  The standard
Krantz–Luce–Suppes–Tversky separability vocabulary states `t`-block independence at
the **weak-preference** level: shifting the common `t`-value preserves `≽` between
two profiles that differ off `t`.  This file introduces that named condition,
`TBlockWeakIndependent`, and proves:

* `stripTransfer_of_tBlockWeakIndependent` — `StripTransfer` follows from
  `TBlockWeakIndependent` (an indifference is two weak preferences; apply the
  block condition to each, using the `(x,r)↔(z,p)` symmetry of its quantifier);
* `tBlockWeakIndependent_of_additiveRep` — **necessity**: under a representation
  the common `V_t` term cancels for `≽` too, so the weakPref block condition holds;
* `tBlockWeakIndependent_allLevels` — like the strip, it is level-independent
  (the background's `t`-value is irrelevant), so it is `t`-block independence at
  *all* levels.

## Why this is real progress on R1.1

It pins the `StripTransfer` half of `CrossPairCancellationData` to the **standard
separability condition** `TBlockWeakIndependent` (weakPref `t`-block independence),
proved necessary and level-independent.  This is the exact KLST object the §IV.5
forward construction (R1.2) targets, stated in the standard vocabulary — a cleaner
and stronger target than the bare indifference strip, with the indifference strip
now a proved consequence.

This file imports `OptionB_C1aStripLevels` and `OptionB_CoordinateIndependence`
(for `indiff_iff_score`) and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aStripLevels
import WakkerDebreuKoopmans.OptionB_CoordinateIndependence

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

/-- **Weak-preference `t`-block independence (the KLST separability form).**

Shifting the common `t`-value from `w` to `c` preserves `≽` between two profiles
that differ in `{j,k}`:
`[x|r|w] ≽ [z|p|w] → [x|r|c] ≽ [z|p|c]`.

This is the standard coordinate-independence statement for the `t`-block at the
weak-preference level (Krantz–Luce–Suppes–Tversky).  `StripTransfer` is its
indifference shadow. -/
def TBlockWeakIndependent (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (x z : X j) (p r : X k) (w c : X t),
    P.weakPref (tri a j k t x r w) (tri a j k t z p w) →
    P.weakPref (tri a j k t x r c) (tri a j k t z p c)

/-- **`StripTransfer` from weakPref-level `t`-block independence.**

An indifference is two weak preferences; apply `TBlockWeakIndependent` to each
direction (the reverse direction instantiates the `(x,r) ↔ (z,p)` symmetry of the
block condition's quantifier).  So the standard separability condition implies the
bare strip.  Audit `[propext, Quot.sound]`. -/
theorem stripTransfer_of_tBlockWeakIndependent
    {j k t : ι} (hTB : TBlockWeakIndependent P j k t) :
    StripTransfer P j k t := by
  intro a x z p r w hw
  rcases hw with ⟨hfwd, hbwd⟩
  refine ⟨?_, ?_⟩
  · -- [x|r|·] ≽ [z|p|·] transported.
    exact hTB a x z p r w (a t) hfwd
  · -- [z|p|·] ≽ [x|r|·] transported (swap roles x↔z, r↔p).
    exact hTB a z x r p w (a t) hbwd

/-- **Necessity of `TBlockWeakIndependent` (soundness witness).**

Under an additive representation, the scored comparison of `[x|r|c]` vs `[z|p|c]`
differs from that of `[x|r|w]` vs `[z|p|w]` only by the common `V_t`-term, which
cancels.  So the weakPref block condition holds for any preference with a
representation.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockWeakIndependent_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    TBlockWeakIndependent P j k t := by
  intro a x z p r w c hw
  have hkj : k ≠ j := Ne.symm hjk
  have htj : t ≠ j := Ne.symm hjt
  have htk : t ≠ k := Ne.symm hkt
  -- Score of a `tri` profile (standard three-coordinate split).
  have score_tri : ∀ (u : X j) (v : X k) (cc : X t),
      (∑ i, R.V i (tri a j k t u v cc i))
        = R.V j u + R.V k v + R.V t cc
          + ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
    intro u v cc
    unfold tri
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (show k ∈ Finset.univ.erase j from
          Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩),
        ← Finset.add_sum_erase _ _ (show t ∈ (Finset.univ.erase j).erase k from
          Finset.mem_erase.mpr ⟨htk, Finset.mem_erase.mpr ⟨htj, Finset.mem_univ t⟩⟩)]
    have hj : (Function.update (Function.update (Function.update a j u) k v) t cc) j = u := by
      rw [Function.update_of_ne hjt, Function.update_of_ne hjk, Function.update_self]
    have hk : (Function.update (Function.update (Function.update a j u) k v) t cc) k = v := by
      rw [Function.update_of_ne hkt, Function.update_self]
    have ht : (Function.update (Function.update (Function.update a j u) k v) t cc) t = cc := by
      rw [Function.update_self]
    rw [hj, hk, ht]
    have hrest : (∑ i ∈ ((Finset.univ.erase j).erase k).erase t,
          R.V i (Function.update (Function.update (Function.update a j u) k v) t cc i))
        = ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hit : i ≠ t := Finset.ne_of_mem_erase hi
      have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      have hij : i ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij]
    rw [hrest]; ring
  -- Decode the level-`w` weak preference into a scored inequality, shift to `c`.
  rw [R.represents] at hw
  rw [R.represents]
  rw [score_tri, score_tri] at hw
  rw [score_tri, score_tri]
  linarith

/-- **`TBlockWeakIndependent` is level-independent.**

Like the strip, the background's `t`-value is irrelevant (`tri_bg_update_t`), so
the condition transports `≽` between *every* pair of levels, not merely from `w`
to `a t`.  (Here the definition already quantifies `w c` freely, so this is the
observation that the `tri` background plays no role — recorded for parity with
`stripTransfer_allLevels`.)  Audit `[propext, Quot.sound]`. -/
theorem tBlockWeakIndependent_allLevels
    {j k t : ι} (hTB : TBlockWeakIndependent P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (hw : P.weakPref (tri a j k t x r w) (tri a j k t z p w)) :
    P.weakPref (tri a j k t x r c) (tri a j k t z p c) :=
  hTB a x z p r w c hw

end ProductPref
end WakkerInfra

/-! ## R1.1 block-independence audit -/

#print axioms WakkerInfra.ProductPref.stripTransfer_of_tBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.tBlockWeakIndependent_of_additiveRep
#print axioms WakkerInfra.ProductPref.tBlockWeakIndependent_allLevels
