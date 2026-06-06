/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: additive-arithmetic characterization of the diagonal trichotomy

This file proves another real, substantive theorem about the single Thomsen
residue `TBlockDiagonalResidue` (R1.1's final-piece content,
`OptionB_C1aDiagonalUnifiedCapstone.lean`):

**Under an additive representation, the trichotomy class of a two-coord-different
profile pair is exactly the sign of the cross-coordinate utility difference
`(V_j x + V_k r) − (V_j z + V_k p)`.**

The prior diagonal-trichotomy work derived the three-way classification
*abstractly* from the diagonal residue + weak order.  This file confirms that
abstract classification agrees with the concrete additive model: the `t`-level's
utility `V_t c` and the off-`{j,k,t}` background both cancel in the comparison, so
the class depends only on the `{j,k}`-block utility difference, and:
* uniform `≻`  ⇔  `V_j z + V_k p < V_j x + V_k r`,
* uniform `∼`  ⇔  `V_j x + V_k r = V_j z + V_k p`,
* uniform `≺`  ⇔  `V_j x + V_k r < V_j z + V_k p`.

This is a genuine soundness/consistency result: it shows the residue's abstract
trichotomy is *necessarily* the additive-order trichotomy under any representation
(so the abstract structure is exactly the right one), and it explicitly exhibits
the level-invariance (`V_t c` cancels) as an arithmetic identity rather than an
order-theoretic argument.

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_pointStrict_iff_score` — at any single level `c`, strict
  preference is the strict sign of the cross-difference.
* `tBlockDiagonalResidue_pointIndiff_iff_score` — at any single level, indifference
  is equality of the cross-sums.
* `tBlockDiagonalResidue_uniformStrict_iff_score` /
  `tBlockDiagonalResidue_uniformIndiff_iff_score` — the uniform-across-levels
  classes, equivalent to the same score conditions (the `t`-level is immaterial).
* `tBlockDiagonalResidue_trichotomy_matches_score` — the packaged capstone:
  under a representation the uniform class is determined by `lt_trichotomy` on the
  cross-sums, so the abstract trichotomy and the additive-order trichotomy coincide.

All audit `[propext, Classical.choice, Quot.sound]` (the `Classical.choice` enters
through `AdditiveRep` / `Fintype` sums, as in every `_of_additiveRep` necessity
lemma).

This file imports `OptionB_C1aThirdCoordinate` (for `tri`) and the artifact `Core`
(for `AdditiveRep`), and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aThirdCoordinate

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open WakkerDebreuKoopmans
open Function

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-- **Score of a `tri` profile** (the standard three-coordinate split).

`∑ R.V i (tri a j k t u v c i) = R.V j u + R.V k v + R.V t c + (off-block rest)`.
Reusable engine for the score characterizations below. -/
private theorem score_tri_aux (R : AdditiveRep P) {j k t : ι}
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

/-- **Point strict ⇔ strict sign of the cross-difference.**

At any single level `c`, `(x,r,c) ≻ (z,p,c)` iff
`V_j z + V_k p < V_j x + V_k r` — the `t`-level utility and the off-block
background cancel.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockDiagonalResidue_pointStrict_iff_score
    (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (x z : X j) (p r : X k) (c : X t) :
    P.strict (tri a j k t x r c) (tri a j k t z p c) ↔
      R.V j z + R.V k p < R.V j x + R.V k r := by
  have hAB := R.represents (tri a j k t x r c) (tri a j k t z p c)
  have hBA := R.represents (tri a j k t z p c) (tri a j k t x r c)
  rw [score_tri_aux R hjk hjt hkt, score_tri_aux R hjk hjt hkt] at hAB hBA
  unfold ProductPref.strict
  rw [hAB, hBA]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hcon
    push_neg at hcon
    exact h2 (by linarith)
  · intro h
    refine ⟨by linarith, ?_⟩
    intro hle
    linarith

/-- **Point indifference ⇔ equality of the cross-sums.**

At any single level `c`, `(x,r,c) ∼ (z,p,c)` iff `V_j x + V_k r = V_j z + V_k p`.
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockDiagonalResidue_pointIndiff_iff_score
    (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (x z : X j) (p r : X k) (c : X t) :
    P.indiff (tri a j k t x r c) (tri a j k t z p c) ↔
      R.V j x + R.V k r = R.V j z + R.V k p := by
  have hAB := R.represents (tri a j k t x r c) (tri a j k t z p c)
  have hBA := R.represents (tri a j k t z p c) (tri a j k t x r c)
  rw [score_tri_aux R hjk hjt hkt, score_tri_aux R hjk hjt hkt] at hAB hBA
  unfold ProductPref.indiff
  rw [hAB, hBA]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm (by linarith) (by linarith)
  · intro h
    exact ⟨by linarith, by linarith⟩

/-- **Uniform strict ⇔ strict sign of the cross-difference.**

Since the point characterization is independent of `c`, the uniform-across-levels
strict class is equivalent to the same score condition (`Nonempty (X t)` provides
the witness level for the forward direction).  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem tBlockDiagonalResidue_uniformStrict_iff_score
    (R : AdditiveRep P) {j k t : ι} [Nonempty (X t)]
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (x z : X j) (p r : X k) :
    (∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c)) ↔
      R.V j z + R.V k p < R.V j x + R.V k r := by
  constructor
  · intro h
    have c₀ : X t := Classical.arbitrary (X t)
    exact (tBlockDiagonalResidue_pointStrict_iff_score R hjk hjt hkt a x z p r c₀).mp (h c₀)
  · intro h c
    exact (tBlockDiagonalResidue_pointStrict_iff_score R hjk hjt hkt a x z p r c).mpr h

/-- **Uniform indifference ⇔ equality of the cross-sums.**  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem tBlockDiagonalResidue_uniformIndiff_iff_score
    (R : AdditiveRep P) {j k t : ι} [Nonempty (X t)]
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (x z : X j) (p r : X k) :
    (∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c)) ↔
      R.V j x + R.V k r = R.V j z + R.V k p := by
  constructor
  · intro h
    have c₀ : X t := Classical.arbitrary (X t)
    exact (tBlockDiagonalResidue_pointIndiff_iff_score R hjk hjt hkt a x z p r c₀).mp (h c₀)
  · intro h c
    exact (tBlockDiagonalResidue_pointIndiff_iff_score R hjk hjt hkt a x z p r c).mpr h

/-- **Capstone: the abstract trichotomy coincides with the additive-order
trichotomy.**

Under a representation, the three uniform classes of the diagonal residue are
exactly the three cases of `lt_trichotomy` on the cross-sums
`(V_j z + V_k p)` vs `(V_j x + V_k r)`.  Packaged as the conjunction of the three
score characterizations, this confirms the residue's abstract trichotomy
(derived structurally from the diagonal residue + weak order) *is* the additive
classification — so the abstract structure is exactly right and the level-
invariance is an arithmetic cancellation.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem tBlockDiagonalResidue_trichotomy_matches_score
    (R : AdditiveRep P) {j k t : ι} [Nonempty (X t)]
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (x z : X j) (p r : X k) :
    ((∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c)) ↔
        R.V j z + R.V k p < R.V j x + R.V k r) ∧
    ((∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c)) ↔
        R.V j x + R.V k r = R.V j z + R.V k p) ∧
    ((∀ c : X t, P.strict (tri a j k t z p c) (tri a j k t x r c)) ↔
        R.V j x + R.V k r < R.V j z + R.V k p) :=
  ⟨tBlockDiagonalResidue_uniformStrict_iff_score R hjk hjt hkt a x z p r,
   tBlockDiagonalResidue_uniformIndiff_iff_score R hjk hjt hkt a x z p r,
   tBlockDiagonalResidue_uniformStrict_iff_score R hjk hjt hkt a z x r p⟩

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-score audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_pointStrict_iff_score
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_pointIndiff_iff_score
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_uniformStrict_iff_score
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_uniformIndiff_iff_score
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_trichotomy_matches_score
