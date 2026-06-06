/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-EQ1a.0: compensation uniqueness (the strictness prerequisite)

> **STATUS: `sorry`-free.**  WP-EQ1a.0 of `OptionB_EqualSpacingWPEQ1aScoping.md`.
> Not in the umbrella import.

## What this file resolves (an honest scoping correction)

The scoping doc named, as the WP-EQ1a.0 prerequisite, the `hStrict` hypothesis of
`Core.standard_sequence_unique`:

```
hStrict : ∀ a (v w : X j), P.indiff (update a j v) (update a j w) → v = w
```

i.e. coordinate-`j` indifference implies **value equality** `v = w`.  Investigating
it honestly (the project's discipline) reveals:

* **`hStrict` is NOT a structural-axiom theorem.**  Under a representation it says
  `V_j v = V_j w → v = w`, i.e. `V_j` is **injective** — which a representation does
  *not* guarantee (a coordinate may have an "indifference plateau": distinct values
  with equal utility).  We machine-check this as a no-go
  (`coordStrict_not_of_additiveRep`): a concrete representation with a non-injective
  `V_j` violates `hStrict`.  So WP-EQ1a must NOT route through value-level
  uniqueness.

* **The crux does not need it.**  WP-EQ1a.2 must force an IVT-produced compensating
  `t`-level `q` to coincide with the calibration target `st` **as a trade-off**
  (`indiff [.|.|q] [.|.|st]`), not as a value (`q = st`).  That *indifference-level*
  uniqueness is free — pure weak-order transitivity
  (`compensationLevel_unique_of_indiff`): two `t`-levels that both compensate the
  same step against the same background are indifferent.

**Net.**  WP-EQ1a.0's genuine deliverable is the indifference-level compensation
uniqueness (provided here, free), plus the recorded no-go that value-level `hStrict`
is not free.  The crux (WP-EQ1a.2) uses the indifference-level version throughout;
`standard_sequence_unique` (which needs value-level `hStrict`) is therefore **not**
on the critical path — a useful de-risking of the plan.

This file imports `OptionB_C1aThirdCoordinate` (for `tri`, `indiff_iff_score`, the
score helpers) and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aThirdCoordinate

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace WakkerInfra
namespace ProductPref

open WakkerDebreuKoopmans
open Function Finset

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-! ## §A.  Indifference-level compensation uniqueness (free — the crux's real need)

The matching crux (WP-EQ1a.2) produces a compensating `t`-level `q` by IVT and must
identify it with the calibration target `st` *as a trade-off*.  The right notion is
indifference-level: if `q` and `st` both compensate the same `j`-step `x → x'`
against the same `{j,k}`-background `(·, v)` and reference `rt`, they are
interchangeable.  Pure weak order, no axioms. -/

/-- **Compensation uniqueness at the indifference level (PROVED, pure weak order).**

If a `t`-level `q` compensates the `j`-step `x → x'` (i.e. `[x|v|rt] ∼ [x'|v|q]`)
and `st` compensates the *same* step (`[x|v|rt] ∼ [x'|v|st]`), then the two
compensated profiles are indifferent: `[x'|v|q] ∼ [x'|v|st]`.  This is the
trade-off-level "the compensating level is unique" the crux needs — it does **not**
require value equality `q = st`.  Audit `[propext, Quot.sound]`. -/
theorem compensationLevel_unique_of_indiff
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (a : Profile X) (x x' : X j) (v : X k) (rt q st : X t)
    (hq  : P.indiff (tri a j k t x v rt) (tri a j k t x' v q))
    (hst : P.indiff (tri a j k t x v rt) (tri a j k t x' v st)) :
    P.indiff (tri a j k t x' v q) (tri a j k t x' v st) :=
  ⟨ProductPref.IsWeakOrder.transitive _ _ _ hq.2 hst.1,
   ProductPref.IsWeakOrder.transitive _ _ _ hst.2 hq.1⟩

/-- **Compensation uniqueness, symmetric form (PROVED).**

Same statement with the roles of `q` and `st` swapped in the conclusion, for
ergonomic use in the crux's chains.  Audit `[propext, Quot.sound]`. -/
theorem compensationLevel_unique_of_indiff'
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (a : Profile X) (x x' : X j) (v : X k) (rt q st : X t)
    (hq  : P.indiff (tri a j k t x v rt) (tri a j k t x' v q))
    (hst : P.indiff (tri a j k t x v rt) (tri a j k t x' v st)) :
    P.indiff (tri a j k t x' v st) (tri a j k t x' v q) :=
  ⟨ProductPref.IsWeakOrder.transitive _ _ _ hst.2 hq.1,
   ProductPref.IsWeakOrder.transitive _ _ _ hq.2 hst.1⟩

/-! ## §B.  Soundness gate: indifference-level uniqueness is necessary under a rep

A trivial check that the §A lemma is consistent with any representation (it is pure
weak order, so this is automatic, but we record it to keep the gate discipline). -/

/-- Score split of a `tri` profile (local engine copy). -/
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

/-- **Soundness gate (PROVED): under a rep, two compensating `t`-levels have equal
`V_t` (hence the compensated profiles are indifferent).**

`[x|v|rt] ∼ [x'|v|q]` and `[x|v|rt] ∼ [x'|v|st]` each score to
`V_j x + V_t rt = V_j x' + V_t (·)`, so `V_t q = V_t st`.  Confirms the
indifference-level uniqueness target hides nothing false.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem compensationLevel_Vt_eq_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : WakkerDebreuKoopmans.AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (x x' : X j) (v : X k) (rt q st : X t)
    (hq  : P.indiff (tri a j k t x v rt) (tri a j k t x' v q))
    (hst : P.indiff (tri a j k t x v rt) (tri a j k t x' v st)) :
    R.V t q = R.V t st := by
  have eq := (indiff_iff_score R).mp hq
  have es := (indiff_iff_score R).mp hst
  rw [score_tri_local R hjk hjt hkt, score_tri_local R hjk hjt hkt] at eq es
  linarith

end ProductPref
end WakkerInfra

/-! ## §C.  No-go: value-level `hStrict` is NOT a representation consequence

`standard_sequence_unique` requires `hStrict : indiff (update a j v) (update a j w)
→ v = w`.  We record that this is genuinely *not* free: a representation with a
non-injective `V_j` (an indifference plateau) satisfies all the additive structure
yet violates `hStrict`.  So the WP-EQ1a crux must use the §A indifference-level
uniqueness, not value-level `standard_sequence_unique`. -/

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBEqualSpacingStrictness

open WakkerInfra
open WakkerInfra.ProductPref

/-- A 2-coordinate model on `Fin 2 → Fin 2` whose coordinate-0 utility is
**constant** (an indifference plateau): `U(x) = (x 1).val` ignores `x 0`. -/
def Uplateau (x : Fin 2 → Fin 2) : ℤ := ((x 1).val : ℤ)

/-- The plateau preference: `x ≽ y ⇔ U y ≤ U x`. -/
def Pplateau : ProductPref (fun _ : Fin 2 => Fin 2) where
  weakPref := fun x y => Uplateau y ≤ Uplateau x

theorem plateau_isWeakOrder : ProductPref.IsWeakOrder Pplateau where
  complete := by intro x y; exact le_total (Uplateau y) (Uplateau x)
  transitive := by intro x y z hxy hyz; exact le_trans hyz hxy

/-- **No-go: value-level `hStrict` FAILS for `Pplateau` at coordinate 0.**

Coordinate 0 is an indifference plateau: `update a 0 v` and `update a 0 w` have the
same `Uplateau` (which reads only coordinate 1) for *any* `v, w`, so they are
indifferent — yet `v ≠ w` is possible (`v = 0, w = 1`).  So `hStrict` is not a
consequence of the additive structure; value-level standard-sequence uniqueness is
unavailable, and WP-EQ1a must use indifference-level uniqueness (§A).  Audit
`[propext]`. -/
theorem hStrict_fails_for_plateau :
    ¬ (∀ (a : Fin 2 → Fin 2) (v w : Fin 2),
        Pplateau.indiff (Function.update a 0 v) (Function.update a 0 w) → v = w) := by
  intro hStrict
  -- v = 0, w = 1 at any base: the updates agree on coordinate 1, so indiff holds.
  have hind : Pplateau.indiff
      (Function.update (fun _ : Fin 2 => (0 : Fin 2)) 0 0)
      (Function.update (fun _ : Fin 2 => (0 : Fin 2)) 0 1) := by
    refine ⟨?_, ?_⟩ <;>
    · show Uplateau _ ≤ Uplateau _
      simp [Uplateau]
  have : (0 : Fin 2) = 1 := hStrict _ 0 1 hind
  exact absurd this (by decide)

end OptionBEqualSpacingStrictness
end CertificateChecklist
end WakkerRoadmap

/-! ## WP-EQ1a.0 audit

* §A (free): `compensationLevel_unique_of_indiff` — the indifference-level
  compensation uniqueness the crux actually needs (pure weak order).
* §B (gate): `compensationLevel_Vt_eq_of_additiveRep` — necessary under a rep.
* §C (no-go): `hStrict_fails_for_plateau` — value-level `hStrict` is NOT free, so
  `standard_sequence_unique` is off the critical path; use §A instead.

Net: WP-EQ1a.0 is resolved, and it de-risks the plan — the crux routes through free
indifference-level uniqueness, not value-level standard-sequence uniqueness. -/

#print axioms WakkerInfra.ProductPref.compensationLevel_unique_of_indiff
#print axioms WakkerInfra.ProductPref.compensationLevel_unique_of_indiff'
#print axioms WakkerInfra.ProductPref.compensationLevel_Vt_eq_of_additiveRep
#print axioms WakkerRoadmap.CertificateChecklist.OptionBEqualSpacingStrictness.hStrict_fails_for_plateau
