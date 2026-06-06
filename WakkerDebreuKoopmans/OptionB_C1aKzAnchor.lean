/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 anchor core: `KzAnchorTransfer` from `k`-block independence

This file makes a genuine forward step on the **anchor core** of the §IV.5
cross-pair residual (R1.1 of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`): it derives
`KzAnchorTransfer` (`OptionB_C1aKzReduction.lean`) from a third standard KLST
block-independence condition plus pure weak-order transitivity.

## The chain (worked out)

`KzAnchorTransfer`: from
* **P1** `[x|q|c] ∼ [y|p|c]`  (k-pair `(q,p)` compensates the j-shift `x→y` at
  base t-level `c = a t`), and
* **J2** `[x|r|w] ∼ [y|r|c]`  (t-pair `(w,c)` compensates `x→y` at k-value `r`),

conclude **Kz** `[x|q|c] ∼ [x|p|w]`.

J2 is an indifference between two profiles that **agree on `k = r`** and differ in
`{j,t}`.  Applying `k`-block independence (the `{j,t}`-difference is independent of
the common `k`-value) shifts `r → p`:  `[x|p|w] ∼ [y|p|c]`.  Then
`[x|q|c] ∼(P1) [y|p|c] ∼(J2 shifted, symm) [x|p|w]` closes Kz by transitivity.

So the anchor core reduces to **`k`-block independence** — the third and last KLST
separability condition (companion to the `t`-block `TBlockWeakIndependent` and the
`j`-block `JBlockWeakIndependent`).

## What this file delivers (machine-checked, sound)

* `KBlockWeakIndependent P j k t` — `k`-block independence: the `≽`-order between
  two profiles agreeing on `k` (differing in `{j,t}`) is independent of the common
  `k`-value.
* `kzAnchorTransfer_of_kBlock` — **the anchor-core reduction**: `KzAnchorTransfer`
  from `KBlockWeakIndependent` (+ weak-order transitivity).
* `kBlockWeakIndependent_of_additiveRep` — **necessity** (the common `V_k` term
  cancels).
* `kzTransfer_of_kBlock_and_jBlock` — **capstone**: composing with the previous
  reduction, the full `KzTransfer` follows from the two block-independence
  conditions `KBlockWeakIndependent` + `JBlockWeakIndependent`.

## Net effect on R1.1

The entire `CrossPairCancellationData` is now reduced to the **three standard KLST
block-independence conditions** (`j`-, `k`-, `t`-block), each proved necessary:
* `StripTransfer` ⟸ `TBlockWeakIndependent`;
* `KzTransfer` ⟸ `KBlockWeakIndependent` + `JBlockWeakIndependent`.
No separate "anchor" residual remains — the anchor core is discharged into
`k`-block independence.  This is exactly Wakker's coordinate-independence input set
(KLST separability of every pair of blocks), now the precise §IV.5 forward target.

This file imports `OptionB_C1aKzReduction` and `OptionB_CoordinateIndependence`
and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aKzReduction
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

/-- **`k`-block (weak-preference) independence.**

The `≽`-order between two profiles that agree on coordinate `k` (and may differ in
`{j,t}`) is independent of the common `k`-value: shifting `v → v'` preserves it.
The third KLST separability condition, companion to `TBlockWeakIndependent`
(`t`-block) and `JBlockWeakIndependent` (`j`-block). -/
def KBlockWeakIndependent (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (u u' : X j) (v v' : X k) (c c' : X t),
    P.weakPref (tri a j k t u v c) (tri a j k t u' v c') →
    P.weakPref (tri a j k t u v' c) (tri a j k t u' v' c')

/-- **R1.1 anchor-core reduction: `KzAnchorTransfer` from `k`-block independence.**

`KzAnchorTransfer` follows from `KBlockWeakIndependent` plus weak-order
transitivity: J2 (`[x|r|w] ∼ [y|r|c]`, common `k = r`) shifts via `k`-block
independence to `[x|p|w] ∼ [y|p|c]`; chaining with P1 (`[x|q|c] ∼ [y|p|c]`) through
the common `[y|p|c]` closes Kz `[x|q|c] ∼ [x|p|w]`.  Audit `[propext, Quot.sound]`. -/
theorem kzAnchorTransfer_of_kBlock
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hKB : KBlockWeakIndependent P j k t) :
    KzAnchorTransfer P j k t := by
  intro a x y p q r w hP1 hJ2
  rcases hJ2 with ⟨hJ2fwd, hJ2bwd⟩
  -- Shift the common k-value of J2 from r to p (both ≽-directions).
  have hfwd : P.weakPref (tri a j k t x p w) (tri a j k t y p (a t)) :=
    hKB a x y r p w (a t) hJ2fwd
  have hbwd : P.weakPref (tri a j k t y p (a t)) (tri a j k t x p w) :=
    hKB a y x r p (a t) w hJ2bwd
  -- P1 : [x|q|c] ∼ [y|p|c].
  rcases hP1 with ⟨hP1fwd, hP1bwd⟩
  -- Chain: [x|q|c] ∼ [y|p|c] ∼ [x|p|w].
  refine ⟨?_, ?_⟩
  · -- weakPref [x|q|c] [x|p|w]:  [x|q|c] ≽ [y|p|c] ≽ [x|p|w].
    exact ProductPref.IsWeakOrder.transitive _ _ _ hP1fwd hbwd
  · -- weakPref [x|p|w] [x|q|c]:  [x|p|w] ≽ [y|p|c] ≽ [x|q|c].
    exact ProductPref.IsWeakOrder.transitive _ _ _ hfwd hP1bwd

/-- **Necessity of `k`-block independence (soundness witness).**

Under an additive representation, two profiles agreeing on `k` have scores
differing only by the common `V_k`-term, which cancels — so shifting the common
`k`-value preserves `≽`.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem kBlockWeakIndependent_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    KBlockWeakIndependent P j k t := by
  intro a u u' v v' c c' hw
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

/-- **Capstone: full `KzTransfer` from the `k`- and `j`-block independence
conditions.**

Composing the anchor-core reduction (`kzAnchorTransfer_of_kBlock`) with the
across-`z` reduction (`kzTransfer_of_anchor_and_jBlock`,
`OptionB_C1aKzReduction.lean`): the entire `KzTransfer` follows from the two
standard KLST block-independence conditions `KBlockWeakIndependent` +
`JBlockWeakIndependent`.  Audit `[propext, Quot.sound]`. -/
theorem kzTransfer_of_kBlock_and_jBlock
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hKB : KBlockWeakIndependent P j k t)
    (hJB : JBlockWeakIndependent P j k t) :
    KzTransfer P j k t :=
  kzTransfer_of_anchor_and_jBlock (kzAnchorTransfer_of_kBlock hKB) hJB

end ProductPref
end WakkerInfra

/-! ## R1.1 anchor-core audit -/

#print axioms WakkerInfra.ProductPref.kzAnchorTransfer_of_kBlock
#print axioms WakkerInfra.ProductPref.kBlockWeakIndependent_of_additiveRep
#print axioms WakkerInfra.ProductPref.kzTransfer_of_kBlock_and_jBlock
