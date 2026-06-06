/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-C1.a derivability probe (hexagon / double cancellation)

Before investing in the WP-C1.a forward proof, this file runs the mandated
**derivability probe** (the discipline that §5, WP-CI, and WP-density all
vindicated): test whether the *target* — the hexagon / Thomsen
`DoubleCancellation` — is implied by the *input we have*, namely single-coordinate
independence A1 (`CoordinateOrderIndependent`, = `CoordinateWeakSeparable`).

## The probe question

The roadmap's WP-C1.a plan says "derive `DoubleCancellation P j k` from A1 via the
`n ≥ 3` third coordinate (Debreu 1960 / KLST 1971 Thm 6.2)."  But that classical
derivation uses **restricted solvability** and the third coordinate as a
*measuring stick* — it is **not** "A1 ⟹ hexagon" on the nose.  Does A1 *alone*
(all coordinates, even with `n = 3` and all coordinates essential) already force
`DoubleCancellation`?

## The probe verdict (proved below): NO.

We exhibit a concrete `n = 3` preference `Pcm` on `Fin 3 → Fin 3` that:

* is a weak order (`cm_isWeakOrder`);
* satisfies single-coordinate independence A1 on **every** coordinate
  (`cm_coordinateOrderIndependent`); and
* **violates** `DoubleCancellation` on the `{0,1}` pair (`cm_not_doubleCancellation`).

The model is `U(x) = g(x₀, x₁) + x₂` where `g` is the comonotone-but-non-additive
3×3 matrix
```
        x₁=0  x₁=1  x₁=2
 x₀=0 [  0     2     3  ]
 x₀=1 [  2     5    10  ]
 x₀=2 [  4    10    11  ]
```
`g` is *strictly increasing in each index with index-order matching value-order
uniformly* (so A1 holds on coordinates 0 and 1), and `x₂` enters additively (so A1
holds on coordinate 2).  But `g` violates Thomsen: `g(0,1)=g(1,0)=2` and
`g(1,2)=g(2,1)=10`, yet `g(0,2)=3 ≠ 4=g(2,0)`.

## Consequence for WP-C1.a (honest determination)

Single-coordinate A1 does **not** imply the hexagon, even at `n = 3` with all
coordinates essential.  Therefore the WP-C1.a derivation **cannot** be "A1 ⟹
hexagon"; it *must* use the additional structural inputs — **restricted
solvability + the third coordinate** (the genuine Debreu/KLST `n ≥ 3` argument),
which the countermodel lacks (it has finite, non-solvable coordinates).

This pins the WP-C1.a target precisely: prove
`DoubleCancellation` from {A1 + RestrictedSolvability + Archimedean + topology +
`n ≥ 3`}.  It is a genuine multi-step Debreu construction, not a one-line A1
projection.  The probe has saved us from attempting the wrong (false) lemma.

This file imports only `OptionB_CoordinateIndependence` and is **not** in the
umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_CoordinateIndependence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBC1aHexagonProbe

open WakkerInfra
open WakkerInfra.ProductPref

/-- The comonotone-but-non-additive 3×3 payoff matrix `g`. -/
def gMat : Fin 3 → Fin 3 → ℤ := ![![0, 2, 3], ![2, 5, 10], ![4, 10, 11]]

/-- The countermodel utility: `U(x) = g(x₀, x₁) + x₂`. -/
def Ucm (x : Fin 3 → Fin 3) : ℤ := gMat (x 0) (x 1) + ((x 2).val : ℤ)

/-- The countermodel preference: `x ≽ y ⇔ U(y) ≤ U(x)`. -/
def Pcm : ProductPref (fun _ : Fin 3 => Fin 3) where
  weakPref := fun x y => Ucm y ≤ Ucm x

/-- `Pcm` is a weak order (completeness + transitivity of `≤` on ℤ). -/
theorem cm_isWeakOrder : ProductPref.IsWeakOrder Pcm where
  complete := by
    intro x y
    exact le_total (Ucm y) (Ucm x)
  transitive := by
    intro x y z hxy hyz
    exact le_trans hyz hxy

/-- `Ucm` of a coordinate-0 update depends only on `(v, a 1, a 2)`. -/
lemma Ucm_update0 (a : Fin 3 → Fin 3) (v : Fin 3) :
    Ucm (Function.update a 0 v) = gMat v (a 1) + ((a 2).val : ℤ) := by
  simp [Ucm, Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide),
        Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide)]

/-- `Ucm` of a coordinate-1 update depends only on `(a 0, v, a 2)`. -/
lemma Ucm_update1 (a : Fin 3 → Fin 3) (v : Fin 3) :
    Ucm (Function.update a 1 v) = gMat (a 0) v + ((a 2).val : ℤ) := by
  simp [Ucm, Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
        Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide)]

/-- `Ucm` of a coordinate-2 update depends only on `(a 0, a 1, v)`. -/
lemma Ucm_update2 (a : Fin 3 → Fin 3) (v : Fin 3) :
    Ucm (Function.update a 2 v) = gMat (a 0) (a 1) + ((v).val : ℤ) := by
  simp [Ucm, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
        Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]

/-- **A1 holds: single-coordinate independence on every coordinate.**

Each coordinate's `coordPref` reduces to a `gMat`-comparison whose truth is
background-independent (the off-coordinate terms cancel), so the order transfers
across backgrounds.  The finite `gMat`-monotonicity facts are `decide`d. -/
theorem cm_coordinateOrderIndependent :
    ∀ i, CoordinateOrderIndependent Pcm i := by
  intro i a b v w hab
  -- `coordPref i x v w` unfolds to `Pcm.weakPref (update x i v) (update x i w)`,
  -- i.e. `Ucm (update x i w) ≤ Ucm (update x i v)`.
  fin_cases i
  · -- coordinate 0: gMat v (·1) vs gMat w (·1); background-1 value is free.
    show Ucm (Function.update b 0 w) ≤ Ucm (Function.update b 0 v)
    have hab' : Ucm (Function.update a 0 w) ≤ Ucm (Function.update a 0 v) := hab
    rw [Ucm_update0, Ucm_update0] at hab' ⊢
    -- hab' : gMat w (a 1) + a2 ≤ gMat v (a 1) + a2  ⟹  gMat w (a1) ≤ gMat v (a1).
    have hcol : gMat w (a 1) ≤ gMat v (a 1) := by linarith
    -- Both columns are uniformly ordered: a fully-closed finite fact.
    have key : ∀ vv ww c1 d1 : Fin 3,
        gMat ww c1 ≤ gMat vv c1 → gMat ww d1 ≤ gMat vv d1 := by decide
    have := key v w (a 1) (b 1) hcol
    linarith
  · -- coordinate 1: gMat (·0) v vs gMat (·0) w; background-0 value is free.
    show Ucm (Function.update b 1 w) ≤ Ucm (Function.update b 1 v)
    have hab' : Ucm (Function.update a 1 w) ≤ Ucm (Function.update a 1 v) := hab
    rw [Ucm_update1, Ucm_update1] at hab' ⊢
    have hrow : gMat (a 0) w ≤ gMat (a 0) v := by linarith
    have key : ∀ vv ww c0 d0 : Fin 3,
        gMat c0 ww ≤ gMat c0 vv → gMat d0 ww ≤ gMat d0 vv := by decide
    have := key v w (a 0) (b 0) hrow
    linarith
  · -- coordinate 2: additive; order is `w.val ≤ v.val`, background-free.
    show Ucm (Function.update b 2 w) ≤ Ucm (Function.update b 2 v)
    have hab' : Ucm (Function.update a 2 w) ≤ Ucm (Function.update a 2 v) := hab
    rw [Ucm_update2, Ucm_update2] at hab' ⊢
    have hval : ((w : Fin 3).val : ℤ) ≤ ((v : Fin 3).val : ℤ) := by linarith
    linarith

/-- **Double cancellation FAILS on the `{0,1}` pair.**

The Thomsen witness: background `a = 0`, `(x,y,z) = (0,1,2)`, `(p,q,r) = (0,1,2)`.
Premises `g(0,1)=g(1,0)` and `g(1,2)=g(2,1)` hold (both `Ucm`-equalities);
conclusion would force `g(0,2)=g(2,0)`, i.e. `3 = 4` — false. -/
theorem cm_not_doubleCancellation :
    ¬ DoubleCancellation Pcm 0 1 := by
  intro hDC
  -- Helper: Ucm of a {0,1}-double-update over background `const 0`.
  have hval : ∀ u v : Fin 3,
      Ucm (Function.update (Function.update (fun _ : Fin 3 => (0 : Fin 3)) 0 u) 1 v)
        = gMat u v := by
    intro u v
    rw [Ucm_update1]
    have h0 : (Function.update (fun _ : Fin 3 => (0 : Fin 3)) 0 u) 0 = u := by simp
    have h2 : (Function.update (fun _ : Fin 3 => (0 : Fin 3)) 0 u) 2 = 0 := by
      rw [Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide)]
    rw [h0, h2]
    norm_num
  -- Premises as indiffs (Ucm-equalities).
  -- Indiff from Ucm-equality.
  have indiff_of_Ucm_eq : ∀ x y : Fin 3 → Fin 3, Ucm x = Ucm y → Pcm.indiff x y := by
    intro x y h
    exact ⟨le_of_eq h.symm, le_of_eq h⟩
  -- Premises as indiffs (Ucm-equalities via hval).
  have prem1 : Pcm.indiff
      (Function.update (Function.update (fun _ : Fin 3 => (0:Fin 3)) 0 0) 1 1)
      (Function.update (Function.update (fun _ : Fin 3 => (0:Fin 3)) 0 1) 1 0) := by
    apply indiff_of_Ucm_eq
    rw [hval, hval]; decide
  have prem2 : Pcm.indiff
      (Function.update (Function.update (fun _ : Fin 3 => (0:Fin 3)) 0 1) 1 2)
      (Function.update (Function.update (fun _ : Fin 3 => (0:Fin 3)) 0 2) 1 1) := by
    apply indiff_of_Ucm_eq
    rw [hval, hval]; decide
  -- Apply DC: x=0 y=1 z=2, p=0 q=1 r=2 over background `const 0`.
  have hconcl := hDC (fun _ => 0) 0 1 2 0 1 2 prem1 prem2
  -- Conclusion: (0@0,2@1) ∼ (2@0,0@1), forcing gMat 0 2 = gMat 2 0, i.e. 3 = 4.
  obtain ⟨h1, _h2⟩ := hconcl
  have e1 : Ucm (Function.update (Function.update (fun _ : Fin 3 => (0:Fin 3)) 0 2) 1 0)
              ≤ Ucm (Function.update (Function.update (fun _ : Fin 3 => (0:Fin 3)) 0 0) 1 2) := h1
  rw [hval, hval] at e1
  -- e1 : gMat 2 0 ≤ gMat 0 2.  Evaluate both: gMat 2 0 = 4, gMat 0 2 = 3.
  have g20 : gMat 2 0 = 4 := by decide
  have g02 : gMat 0 2 = 3 := by decide
  rw [g20, g02] at e1
  -- e1 : (4 : ℤ) ≤ 3 — contradiction.
  norm_num at e1

/-- **The probe verdict, packaged.**

There is an `n = 3` weak order satisfying single-coordinate independence on every
coordinate yet violating `DoubleCancellation` on `{0,1}`.  Hence A1 alone does not
imply the hexagon: WP-C1.a must use restricted solvability + the third coordinate
(the genuine Debreu/KLST `n ≥ 3` construction). -/
theorem a1_does_not_imply_doubleCancellation :
    (∃ (Y : Fin 3 → Type) (Q : ProductPref Y),
      ProductPref.IsWeakOrder Q ∧
      (∀ i, CoordinateOrderIndependent Q i) ∧
      ¬ DoubleCancellation Q 0 1) :=
  ⟨fun _ => Fin 3, Pcm,
   cm_isWeakOrder, cm_coordinateOrderIndependent, cm_not_doubleCancellation⟩

end OptionBC1aHexagonProbe
end CertificateChecklist
end WakkerRoadmap

/-! ## WP-C1.a probe audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aHexagonProbe.cm_coordinateOrderIndependent
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aHexagonProbe.cm_not_doubleCancellation
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aHexagonProbe.a1_does_not_imply_doubleCancellation
