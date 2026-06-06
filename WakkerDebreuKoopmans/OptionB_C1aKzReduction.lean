/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 forward step: `KzTransfer` from an anchor + j-block independence

This file makes a genuine forward reduction on the **`KzTransfer`** half of the
§IV.5 cross-pair residual `CrossPairCancellationData` (R1.1 of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`), paralleling the
`StripTransfer` reduction (`OptionB_C1aBlockIndependence.lean`).

## The observation

`KzTransfer`'s conclusion `[z|q|c] ∼ [z|p|w]` is **independent of `x, y, r`** and
varies only in the common `j`-value `z`.  So once it holds at the anchor `j`-value
(`z := x`, the value the premises P1/J2 fix), the standard **`j`-block
independence** condition transports it to *every* `z`.

## What this file delivers (machine-checked, sound)

* `JBlockWeakIndependent P j k t` — standard `j`-block independence: the `≽`-order
  between two profiles agreeing on `j` (and differing in `{k,t}`) is independent of
  the common `j`-value.  The companion to `TBlockWeakIndependent`.
* `KzAnchorTransfer P j k t` — `KzTransfer` with the conclusion taken at the anchor
  `j`-value `z := x` only.
* `kzTransfer_of_anchor_and_jBlock` — **the reduction**: `KzTransfer` from the
  anchor transfer + `j`-block independence (transport the anchor indifference
  across the common `j`-value via `JBlockWeakIndependent`).
* `jBlockWeakIndependent_of_additiveRep` — **necessity** of `j`-block independence
  (the common `V_j` term cancels).
* `kzAnchorTransfer_of_kzTransfer` — the anchor transfer is a specialization of
  `KzTransfer` (so it is necessary, via `kzTransfer_of_additiveRep`).

## Net effect on R1.1

Both halves of `CrossPairCancellationData` are now reduced to **standard KLST
block-independence conditions** plus a small anchor core:
* `StripTransfer` ⟸ `TBlockWeakIndependent` (`t`-block independence);
* `KzTransfer` ⟸ `KzAnchorTransfer` + `JBlockWeakIndependent` (`j`-block
  independence).
Each block-independence condition is proved necessary and level/base-independent.
This is the clean separability-vocabulary target for the §IV.5 forward
construction.

This file imports `OptionB_C1aThirdCoordinate` and `OptionB_CoordinateIndependence`
(for `indiff_iff_score`) and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aThirdCoordinate
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

/-- **`j`-block (weak-preference) independence.**

The `≽`-order between two profiles that agree on coordinate `j` (and may differ in
`{k,t}`) is independent of the common `j`-value: shifting `u → u'` preserves it.
The companion to `TBlockWeakIndependent`; standard KLST separability of the `{k,t}`
block from `j`. -/
def JBlockWeakIndependent (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (u u' : X j) (v₁ v₂ : X k) (c₁ c₂ : X t),
    P.weakPref (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂) →
    P.weakPref (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂)

/-- **`KzTransfer` with the conclusion at the anchor `j`-value `z := x`.**

The same premises (P1, J2 at level `w`) but concluding the `{k,t}`-compensation
only at the `j`-value `x` fixed by the premises. -/
def KzAnchorTransfer (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (x y : X j) (p q r : X k) (w : X t),
    P.indiff (tri a j k t x q (a t)) (tri a j k t y p (a t)) →
    P.indiff (tri a j k t x r w) (tri a j k t y r (a t)) →
    P.indiff (tri a j k t x q (a t)) (tri a j k t x p w)

/-- **R1.1 reduction: `KzTransfer` from the anchor transfer + `j`-block
independence.**

`KzTransfer` follows from `KzAnchorTransfer` (the `{k,t}`-compensation at the
anchor `j`-value `x`) and `JBlockWeakIndependent` (transport across the common
`j`-value to any `z`).  The anchor gives `[x|q|c] ∼ [x|p|w]`; `j`-block
independence shifts the common `j`-value `x → z` in both `≽`-directions to yield
`[z|q|c] ∼ [z|p|w]`.  Audit `[propext, Quot.sound]`. -/
theorem kzTransfer_of_anchor_and_jBlock
    {j k t : ι}
    (hAnchor : KzAnchorTransfer P j k t)
    (hJB : JBlockWeakIndependent P j k t) :
    KzTransfer P j k t := by
  intro a x y z p q r w hP1 hJ2
  -- Anchor: [x|q|c] ∼ [x|p|w].
  have hx := hAnchor a x y p q r w hP1 hJ2
  rcases hx with ⟨hfwd, hbwd⟩
  -- Transport the common j-value x → z in both directions.
  refine ⟨?_, ?_⟩
  · -- weakPref [z|q|c] [z|p|w]  from  weakPref [x|q|c] [x|p|w].
    exact hJB a x z q p (a t) w hfwd
  · -- weakPref [z|p|w] [z|q|c]  from  weakPref [x|p|w] [x|q|c].
    exact hJB a x z p q w (a t) hbwd

/-- **The anchor transfer is a specialization of `KzTransfer`.**

`KzAnchorTransfer` is `KzTransfer` with `z := x`, so it is implied by `KzTransfer`
(and hence necessary under a representation via `kzTransfer_of_additiveRep`).
Audit `[propext, Quot.sound]`. -/
theorem kzAnchorTransfer_of_kzTransfer
    {j k t : ι} (hKz : KzTransfer P j k t) :
    KzAnchorTransfer P j k t := by
  intro a x y p q r w hP1 hJ2
  exact hKz a x y x p q r w hP1 hJ2

/-- **Necessity of `j`-block independence (soundness witness).**

Under an additive representation, the scored comparison of two profiles agreeing
on `j` differs only by the common `V_j`-term, which cancels — so shifting the
common `j`-value preserves `≽`.  Hence `JBlockWeakIndependent` holds for any
preference with a representation.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem jBlockWeakIndependent_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    JBlockWeakIndependent P j k t := by
  intro a u u' v₁ v₂ c₁ c₂ hw
  have hkj : k ≠ j := Ne.symm hjk
  have htj : t ≠ j := Ne.symm hjt
  have htk : t ≠ k := Ne.symm hkt
  have score_tri : ∀ (uu : X j) (vv : X k) (cc : X t),
      (∑ i, R.V i (tri a j k t uu vv cc i))
        = R.V j uu + R.V k vv + R.V t cc
          + ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
    intro uu vv cc
    unfold tri
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (show k ∈ Finset.univ.erase j from
          Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩),
        ← Finset.add_sum_erase _ _ (show t ∈ (Finset.univ.erase j).erase k from
          Finset.mem_erase.mpr ⟨htk, Finset.mem_erase.mpr ⟨htj, Finset.mem_univ t⟩⟩)]
    have hj : (Function.update (Function.update (Function.update a j uu) k vv) t cc) j = uu := by
      rw [Function.update_of_ne hjt, Function.update_of_ne hjk, Function.update_self]
    have hk : (Function.update (Function.update (Function.update a j uu) k vv) t cc) k = vv := by
      rw [Function.update_of_ne hkt, Function.update_self]
    have ht : (Function.update (Function.update (Function.update a j uu) k vv) t cc) t = cc := by
      rw [Function.update_self]
    rw [hj, hk, ht]
    have hrest : (∑ i ∈ ((Finset.univ.erase j).erase k).erase t,
          R.V i (Function.update (Function.update (Function.update a j uu) k vv) t cc i))
        = ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hit : i ≠ t := Finset.ne_of_mem_erase hi
      have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      have hij : i ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij]
    rw [hrest]; ring
  rw [R.represents] at hw
  rw [R.represents]
  rw [score_tri, score_tri] at hw
  rw [score_tri, score_tri]
  linarith

end ProductPref
end WakkerInfra

/-! ## R1.1 KzTransfer-reduction audit -/

#print axioms WakkerInfra.ProductPref.kzTransfer_of_anchor_and_jBlock
#print axioms WakkerInfra.ProductPref.kzAnchorTransfer_of_kzTransfer
#print axioms WakkerInfra.ProductPref.jBlockWeakIndependent_of_additiveRep
