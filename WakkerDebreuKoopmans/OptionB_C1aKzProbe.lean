/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: `KzTransfer` is NOT an A1 consequence either (probe)

This completes the soundness characterization of the §IV.5 cross-pair residual
`CrossPairCancellationData = KzTransfer ∧ StripTransfer` (R1.1 of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`).

The `StripTransfer` half already has a machine-checked non-A1-derivability probe
(`OptionB_C1aStripProbe.lean`, model `Pstrip`).  This file supplies the matching
probe for the **`KzTransfer`** half, following the same discipline.

## The probe verdict (proved below): NO — A1 does not imply `KzTransfer`.

`KzTransfer P 0 1 2` (the `{k,t}` tradeoff-transfer): from a `{0,1}`-indifference
P1 and a `{0,2}`-indifference J2, conclude a `{1,2}`-indifference Kz.  Under an
additive model this always holds; it is the genuine cross-coordinate (Thomsen)
content.

Countermodel `Pkz` on `Fin 3 → Fin 3`, utility `U(x) = gKz (x 0) (x 1) + x 2`
with the comonotone-but-Thomsen-violating matrix
```
  gKz =  k=0  k=1  k=2
   j=0 [  0    1    2 ]
   j=1 [  1    2    4 ]
   j=2 [  2    3    5 ]
```
`gKz` is strictly increasing in each coordinate (so **A1 holds on every
coordinate**: the order of a value swap is background-independent, the `x 2`
term cancelling).  With witnesses `x=0,y=1,z=0`, `p=0,q=1,r=2`, transfer level
`w=2`, background `a = const 0` (so `c = a 2 = 0`):
* **P1** `[0|1|0] ∼ [1|0|0]`: `gKz 0 1 = 1 = gKz 1 0` ✓;
* **J2** `[0|2|2] ∼ [1|2|0]`: `gKz 0 2 + 2 = 4 = gKz 1 2 + 0` ✓;
* **Kz** `[0|1|0] ∼ [0|0|2]` would need `gKz 0 1 + 0 = gKz 0 0 + 2`, i.e.
  `1 = 2` — **fails**.

So `KzTransfer` is genuine §IV.5 cancellation content, **not** an A1 consequence —
matching `StripTransfer`.  Both halves of `CrossPairCancellationData` are now
machine-checked to be non-A1-derivable (and both are proved necessary under a
representation, `kzTransfer_of_additiveRep` / `stripTransfer_of_additiveRep`).

This file imports `OptionB_C1aThirdCoordinate` (for `tri`, `KzTransfer`) and
`OptionB_CoordinateIndependence` (for `CoordinateOrderIndependent`), and is **not**
in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aThirdCoordinate
import WakkerDebreuKoopmans.OptionB_CoordinateIndependence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBC1aKzProbe

open WakkerInfra
open WakkerInfra.ProductPref

/-- Comonotone, Thomsen-violating payoff matrix: `gKz j k`, strictly increasing in
each coordinate. -/
def gKz : Fin 3 → Fin 3 → ℤ :=
  ![![0, 1, 2], ![1, 2, 4], ![2, 3, 5]]

/-- Countermodel utility on `Fin 3 → Fin 3`: `U(x) = gKz (x 0) (x 1) + x 2`. -/
def Ukz (x : Fin 3 → Fin 3) : ℤ := gKz (x 0) (x 1) + ((x 2).val : ℤ)

/-- Countermodel preference: `x ≽ y ⇔ U y ≤ U x`. -/
def Pkz : ProductPref (fun _ : Fin 3 => Fin 3) where
  weakPref := fun x y => Ukz y ≤ Ukz x

theorem kz_isWeakOrder : ProductPref.IsWeakOrder Pkz where
  complete := by intro x y; exact le_total (Ukz y) (Ukz x)
  transitive := by intro x y z hxy hyz; exact le_trans hyz hxy

/-- `Ukz` of a coordinate-0 update depends only on `(v, a 1, a 2)`. -/
lemma Ukz_update0 (a : Fin 3 → Fin 3) (v : Fin 3) :
    Ukz (Function.update a 0 v) = gKz v (a 1) + ((a 2).val : ℤ) := by
  simp [Ukz, Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide),
        Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide)]

/-- `Ukz` of a coordinate-1 update depends only on `(a 0, v, a 2)`. -/
lemma Ukz_update1 (a : Fin 3 → Fin 3) (v : Fin 3) :
    Ukz (Function.update a 1 v) = gKz (a 0) v + ((a 2).val : ℤ) := by
  simp [Ukz, Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
        Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide)]

/-- `Ukz` of a coordinate-2 update depends only on `(a 0, a 1, v)`. -/
lemma Ukz_update2 (a : Fin 3 → Fin 3) (v : Fin 3) :
    Ukz (Function.update a 2 v) = gKz (a 0) (a 1) + ((v).val : ℤ) := by
  simp [Ukz, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
        Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]

/-- **A1 holds on every coordinate.**

Each coordinate's `coordPref` reduces to a `gKz`-comparison uniformly ordered
across the other coordinates' values (the `x 2` term cancels; `gKz` is strictly
monotone in each coordinate).  The finite uniform-order facts are `decide`d. -/
theorem kz_coordinateOrderIndependent :
    ∀ i, CoordinateOrderIndependent Pkz i := by
  intro i a b v w hab
  fin_cases i
  · -- coordinate 0
    show Ukz (Function.update b 0 w) ≤ Ukz (Function.update b 0 v)
    have hab' : Ukz (Function.update a 0 w) ≤ Ukz (Function.update a 0 v) := hab
    rw [Ukz_update0, Ukz_update0] at hab' ⊢
    have hkey : ∀ vv ww c1 c2 : Fin 3,
        gKz ww c1 ≤ gKz vv c1 → gKz ww c2 ≤ gKz vv c2 := by decide
    have hstep : gKz w (a 1) ≤ gKz v (a 1) := by linarith
    have := hkey v w (a 1) (b 1) hstep
    linarith
  · -- coordinate 1
    show Ukz (Function.update b 1 w) ≤ Ukz (Function.update b 1 v)
    have hab' : Ukz (Function.update a 1 w) ≤ Ukz (Function.update a 1 v) := hab
    rw [Ukz_update1, Ukz_update1] at hab' ⊢
    have hkey : ∀ vv ww j1 j2 : Fin 3,
        gKz j1 ww ≤ gKz j1 vv → gKz j2 ww ≤ gKz j2 vv := by decide
    have hstep : gKz (a 0) w ≤ gKz (a 0) v := by linarith
    have := hkey v w (a 0) (b 0) hstep
    linarith
  · -- coordinate 2
    show Ukz (Function.update b 2 w) ≤ Ukz (Function.update b 2 v)
    have hab' : Ukz (Function.update a 2 w) ≤ Ukz (Function.update a 2 v) := hab
    rw [Ukz_update2, Ukz_update2] at hab' ⊢
    have hstep : ((w).val : ℤ) ≤ ((v).val : ℤ) := by linarith
    linarith

/-- `Ukz` of a `tri` profile.  Since `ι = Fin 3` and `tri` updates all three
coordinates, the background `a` is irrelevant: the value is `gKz u v + c`. -/
private lemma Ukz_tri (a : Fin 3 → Fin 3) (u v c : Fin 3) :
    Ukz (tri a 0 1 2 u v c) = gKz u v + ((c).val : ℤ) := by
  unfold tri Ukz
  have e0 : (Function.update (Function.update (Function.update a 0 u) 1 v) 2 c) 0 = u := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  have e1 : (Function.update (Function.update (Function.update a 0 u) 1 v) 2 c) 1 = v := by
    rw [Function.update_of_ne (by decide), Function.update_self]
  have e2 : (Function.update (Function.update (Function.update a 0 u) 1 v) 2 c) 2 = c := by
    rw [Function.update_self]
  rw [e0, e1, e2]

/-- **`KzTransfer` FAILS on `(j,k,t) = (0,1,2)`.**

Witness over background `a = const 0` (so `c = a 2 = 0`): `x = 0, y = 1, z = 0`,
`p = 0, q = 1, r = 2`, transfer level `w = 2`.
* P1 `[0|1|0] ∼ [1|0|0]`: `gKz 0 1 = 1 = gKz 1 0` — holds.
* J2 `[0|2|2] ∼ [1|2|0]`: `gKz 0 2 + 2 = 4 = gKz 1 2 + 0` — holds.
* Kz `[0|1|0] ∼ [0|0|2]` would need `gKz 0 1 + 0 = gKz 0 0 + 2`, i.e. `1 = 2` —
  fails.
All `gKz` arithmetic settled by `decide`. -/
theorem kz_not_kzTransfer :
    ¬ KzTransfer Pkz 0 1 2 := by
  intro hKz
  have hat : (fun _ : Fin 3 => (0 : Fin 3)) 2 = 0 := rfl
  -- P1 at background level c = 0.
  have hP1 : Pkz.indiff
      (tri (fun _ : Fin 3 => (0 : Fin 3)) 0 1 2 0 1 0)
      (tri (fun _ : Fin 3 => (0 : Fin 3)) 0 1 2 1 0 0) := by
    refine ⟨?_, ?_⟩ <;>
    · show Ukz _ ≤ Ukz _
      rw [Ukz_tri, Ukz_tri]; decide
  -- J2 at transfer level w = 2.
  have hJ2 : Pkz.indiff
      (tri (fun _ : Fin 3 => (0 : Fin 3)) 0 1 2 0 2 2)
      (tri (fun _ : Fin 3 => (0 : Fin 3)) 0 1 2 1 2 0) := by
    refine ⟨?_, ?_⟩ <;>
    · show Ukz _ ≤ Ukz _
      rw [Ukz_tri, Ukz_tri]; decide
  -- KzTransfer args: (a) (x y z) (p q r) (w); P1 = indiff (tri a x q c)(tri a y p c),
  -- J2 = indiff (tri a x r w)(tri a y r c).  Here x=0,y=1,z=0,p=0,q=1,r=2,w=2.
  have hKzc := hKz (fun _ => 0) 0 1 0 0 1 2 2 hP1 hJ2
  -- Conclusion indiff fails: its first leg forces `2 ≤ 1`.
  obtain ⟨h1, _⟩ := hKzc
  have e1 : Ukz (tri (fun _ : Fin 3 => (0:Fin 3)) 0 1 2 0 0 2)
              ≤ Ukz (tri (fun _ : Fin 3 => (0:Fin 3)) 0 1 2 0 1 ((fun _ : Fin 3 => (0:Fin 3)) 2)) := h1
  rw [hat, Ukz_tri, Ukz_tri] at e1
  revert e1; decide

/-- **The probe verdict, packaged.**

A1 holds on every coordinate of `Pkz`, yet `KzTransfer 0 1 2` fails.  Hence the
`{k,t}` tradeoff-transfer is genuine §IV.5 cancellation content, not an A1
consequence — matching the `StripTransfer` probe `Pstrip`. -/
theorem a1_does_not_imply_kzTransfer :
    (∃ (Y : Fin 3 → Type) (Q : ProductPref Y),
      ProductPref.IsWeakOrder Q ∧
      (∀ i, CoordinateOrderIndependent Q i) ∧
      ¬ KzTransfer Q 0 1 2) :=
  ⟨fun _ => Fin 3, Pkz, kz_isWeakOrder, kz_coordinateOrderIndependent, kz_not_kzTransfer⟩

end OptionBC1aKzProbe
end CertificateChecklist
end WakkerRoadmap

/-! ## R1.1 KzTransfer-probe audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aKzProbe.kz_coordinateOrderIndependent
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aKzProbe.kz_not_kzTransfer
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aKzProbe.a1_does_not_imply_kzTransfer
