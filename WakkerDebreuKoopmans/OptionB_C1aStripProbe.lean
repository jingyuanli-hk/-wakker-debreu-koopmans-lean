/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-C1.a strip probe (block independence is NOT free from A1)

Before attempting a forward proof of `StripTransfer` (the `t`-block independence
sub-residual of the third-coordinate transfer), this file runs the mandated
derivability probe (the discipline §5/WP-CI/WP-density/WP-C1.a-probe all
vindicated).

## Correcting the earlier framing

The roadmap conjectured `StripTransfer` is "a pure single-coordinate-independence
(A1) consequence at `n ≥ 3`".  That framing is **wrong**, and the probe proves it.

`StripTransfer P j k t`:
`[x|r|w] ∼ [z|p|w] → [x|r|c] ∼ [z|p|c]` — an indifference between two profiles
(differing in `j` and `k`) is preserved when their **common** third-coordinate
value moves `w → c`.  A1 fixes only the *direction* of each coordinate's order,
not increment *magnitudes*.  The strip additionally needs the `t`-increment to be
**equal** at the two backgrounds `(x,r)` and `(z,p)` — genuine cancellation
content, strictly stronger than A1.

## The probe verdict (proved below): NO — A1 does not imply `StripTransfer`.

Countermodel `Pstrip` on `Fin 3 → Fin 2`, utility `U(x) = M (x 0) (x 1) (x 2)`
with two `2×2` layers (third coordinate `t = 2` selects the layer):
```
  t=0 layer A:   k=0  k=1            t=1 layer B:   k=0  k=1
          j=0 [  0    1  ]                   j=0 [  1    2  ]
          j=1 [  1    3  ]                   j=1 [  5    7  ]
```
Both layers are strictly increasing in `j` and in `k`, and `B > A` cellwise (so
strictly increasing in `t`) — hence **A1 holds on every coordinate**.  But cells
`(j,k) = (0,1)` and `(1,0)` are `A`-equal (`1 = 1`) yet `B`-unequal (`2 ≠ 5`):
the indifference `[0|1|0] ∼ [1|0|0]` is **not** preserved when `t` moves `0 → 1`.
With `(x,z) = (0,1)`, `(r,p) = (1,0)`, `w = 1`, `c = 0`: `[x|r|w]=[0|1|1]` and
`[z|p|w]=[1|0|1]` have `U = 2` vs `5` — wait, we need the *premise* indifference at
the common level `w`, so we read the table the other way: take the layer where the
two cells agree as `w`, and the layer where they disagree as `c`.

Concretely (matching `StripTransfer`'s shape with level `w` in the premise and `a t`
in the conclusion): set background `a` with `a 2 = 0` (so `c = a t = 0`, the
disagreeing layer) and transfer level `w = 1` (the agreeing layer).  Premise
`[0|1|1] ∼ [1|0|1]` holds (`B`-values `2`… ) — we instead pick the matrix so the
agreeing layer is `t=1`.  The file's actual matrix is chosen so that the premise
holds at `w` and the conclusion fails at `c`; see `mStrip` below.

## Consequence for WP-C1.a (honest determination)

`StripTransfer` is **not** an A1 consequence; like `KzTransfer` it is genuine
§IV.5 cancellation content whose **necessity** is already proved
(`stripTransfer_of_additiveRep`).  So both sub-residuals of the third-coordinate
transfer are irreducible-from-A1 cancellation conditions.  The honest WP-C1.a
endpoint is therefore: carry the transfer's cancellation content as a
**necessary, named structural residual** (it joins coordinate independence and the
§IV.2.6 escape content), unless the *full* solvability-based Wakker §IV.5
construction is mechanized — the genuine multi-month frontier.

This file imports only `OptionB_C1aThirdCoordinate` and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_C1aThirdCoordinate

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace OptionBC1aStripProbe

open WakkerInfra
open WakkerInfra.ProductPref

/-- Layered payoff: `mStrip c j k` is the value of cell `(j,k)` in layer `c` (the
third-coordinate value).  Layer `0` is the *agreeing* layer (cells `(0,1)` and
`(1,0)` both `1`); layer `1` is the *disagreeing* layer (`2` vs `5`). -/
def mStrip : Fin 2 → Fin 2 → Fin 2 → ℤ :=
  ![ -- c = 0 (agreeing layer A)
     ![![0, 1], ![1, 3]],
     -- c = 1 (disagreeing layer B)
     ![![1, 2], ![5, 7]] ]

/-- Countermodel utility on `Fin 3 → Fin 2`: `U(x) = mStrip (x 2) (x 0) (x 1)`. -/
def Ustrip (x : Fin 3 → Fin 2) : ℤ := mStrip (x 2) (x 0) (x 1)

/-- Countermodel preference: `x ≽ y ⇔ U y ≤ U x`. -/
def Pstrip : ProductPref (fun _ : Fin 3 => Fin 2) where
  weakPref := fun x y => Ustrip y ≤ Ustrip x

theorem strip_isWeakOrder : ProductPref.IsWeakOrder Pstrip where
  complete := by intro x y; exact le_total (Ustrip y) (Ustrip x)
  transitive := by intro x y z hxy hyz; exact le_trans hyz hxy

/-- `Ustrip` of a coordinate-0 update depends only on `(v, a 1, a 2)`. -/
lemma Ustrip_update0 (a : Fin 3 → Fin 2) (v : Fin 2) :
    Ustrip (Function.update a 0 v) = mStrip (a 2) v (a 1) := by
  simp [Ustrip, Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide),
        Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide)]

/-- `Ustrip` of a coordinate-1 update depends only on `(a 0, v, a 2)`. -/
lemma Ustrip_update1 (a : Fin 3 → Fin 2) (v : Fin 2) :
    Ustrip (Function.update a 1 v) = mStrip (a 2) (a 0) v := by
  simp [Ustrip, Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide),
        Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide)]

/-- `Ustrip` of a coordinate-2 update depends only on `(a 0, a 1, v)`. -/
lemma Ustrip_update2 (a : Fin 3 → Fin 2) (v : Fin 2) :
    Ustrip (Function.update a 2 v) = mStrip v (a 0) (a 1) := by
  simp [Ustrip, Function.update_of_ne (show (0 : Fin 3) ≠ 2 by decide),
        Function.update_of_ne (show (1 : Fin 3) ≠ 2 by decide)]

/-- **A1 holds on every coordinate.**

Each coordinate's `coordPref` reduces to an `mStrip`-comparison that is uniformly
ordered across the other two coordinates' values (all layers strictly increase in
`j` and `k`, and `B > A` cellwise so `t` is monotone too).  The finite uniform-
order facts are fully-closed and `decide`d. -/
theorem strip_coordinateOrderIndependent :
    ∀ i, CoordinateOrderIndependent Pstrip i := by
  intro i a b v w hab
  fin_cases i
  · -- coordinate 0
    show Ustrip (Function.update b 0 w) ≤ Ustrip (Function.update b 0 v)
    have hab' : Ustrip (Function.update a 0 w) ≤ Ustrip (Function.update a 0 v) := hab
    rw [Ustrip_update0, Ustrip_update0] at hab' ⊢
    have key : ∀ vv ww t1 c1 t2 c2 : Fin 2,
        mStrip t1 ww c1 ≤ mStrip t1 vv c1 → mStrip t2 ww c2 ≤ mStrip t2 vv c2 := by decide
    exact key v w (a 2) (a 1) (b 2) (b 1) hab'
  · -- coordinate 1
    show Ustrip (Function.update b 1 w) ≤ Ustrip (Function.update b 1 v)
    have hab' : Ustrip (Function.update a 1 w) ≤ Ustrip (Function.update a 1 v) := hab
    rw [Ustrip_update1, Ustrip_update1] at hab' ⊢
    have key : ∀ vv ww t1 j1 t2 j2 : Fin 2,
        mStrip t1 j1 ww ≤ mStrip t1 j1 vv → mStrip t2 j2 ww ≤ mStrip t2 j2 vv := by decide
    exact key v w (a 2) (a 0) (b 2) (b 0) hab'
  · -- coordinate 2
    show Ustrip (Function.update b 2 w) ≤ Ustrip (Function.update b 2 v)
    have hab' : Ustrip (Function.update a 2 w) ≤ Ustrip (Function.update a 2 v) := hab
    rw [Ustrip_update2, Ustrip_update2] at hab' ⊢
    have key : ∀ vv ww j1 c1 j2 c2 : Fin 2,
        mStrip ww j1 c1 ≤ mStrip vv j1 c1 → mStrip ww j2 c2 ≤ mStrip vv j2 c2 := by decide
    exact key v w (a 0) (a 1) (b 0) (b 1) hab'

/-- `Ustrip` of a `tri` profile.  Since `ι = Fin 3` and `tri` updates all three
coordinates, the background `a` is irrelevant: the value is `mStrip c u v`. -/
private lemma Ustrip_tri (a : Fin 3 → Fin 2) (u v c : Fin 2) :
    Ustrip (tri a 0 1 2 u v c) = mStrip c u v := by
  unfold tri Ustrip
  have e0 : (Function.update (Function.update (Function.update a 0 u) 1 v) 2 c) 0 = u := by
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]
  have e1 : (Function.update (Function.update (Function.update a 0 u) 1 v) 2 c) 1 = v := by
    rw [Function.update_of_ne (by decide), Function.update_self]
  have e2 : (Function.update (Function.update (Function.update a 0 u) 1 v) 2 c) 2 = c := by
    rw [Function.update_self]
  rw [e0, e1, e2]

/-- **`StripTransfer` FAILS on `(j,k,t) = (0,1,2)`.**

Witness over background `a = const 1` (so `c = a 2 = 1`, the *disagreeing* layer):
`x = 0, z = 1`, `r = 1, p = 0`, transfer level `w = 0` (the *agreeing* layer).
* Premise `[0|1|0] ∼ [1|0|0]` (level `w = 0`): `mStrip 0 0 1 = 1 = mStrip 0 1 0` —
  holds.
* Conclusion `[0|1|1] ∼ [1|0|1]` (level `c = 1`): would need
  `mStrip 1 0 1 = mStrip 1 1 0`, i.e. `2 = 5` — fails.
All `mStrip` arithmetic settled by `decide`. -/
theorem strip_not_stripTransfer :
    ¬ StripTransfer Pstrip 0 1 2 := by
  intro hStrip
  have hat : (fun _ : Fin 3 => (1:Fin 2)) 2 = 1 := rfl
  -- Premise at level w = 0 (agreeing layer).
  have prem : Pstrip.indiff
      (tri (fun _ : Fin 3 => (1:Fin 2)) 0 1 2 0 1 0)
      (tri (fun _ : Fin 3 => (1:Fin 2)) 0 1 2 1 0 0) := by
    refine ⟨?_, ?_⟩ <;>
    · show Ustrip _ ≤ Ustrip _
      rw [Ustrip_tri, Ustrip_tri]; decide
  -- Apply strip at level c = a 2 = 1 (disagreeing layer).
  -- StripTransfer args: (a) (x z : X j) (p r : X k) (w : X t); premise is
  -- indiff (tri a x r w) (tri a z p w).  Here x=0,z=1,p=0,r=1,w=0.
  have hconcl := hStrip (fun _ => 1) 0 1 0 1 0 prem
  -- The conclusion indiff fails: its first leg forces `5 ≤ 2`.
  obtain ⟨h1, _⟩ := hconcl
  have e1 : Ustrip (tri (fun _ : Fin 3 => (1:Fin 2)) 0 1 2 1 0 ((fun _ : Fin 3 => (1:Fin 2)) 2))
              ≤ Ustrip (tri (fun _ : Fin 3 => (1:Fin 2)) 0 1 2 0 1 ((fun _ : Fin 3 => (1:Fin 2)) 2)) := h1
  rw [hat, Ustrip_tri, Ustrip_tri] at e1
  revert e1; decide

/-- **The probe verdict, packaged.**

A1 holds on every coordinate of `Pstrip`, yet `StripTransfer 0 1 2` fails.  Hence
the strip is genuine cancellation content, not an A1 consequence — correcting the
roadmap's earlier "pure A1 consequence" framing. -/
theorem a1_does_not_imply_stripTransfer :
    (∃ (Y : Fin 3 → Type) (Q : ProductPref Y),
      ProductPref.IsWeakOrder Q ∧
      (∀ i, CoordinateOrderIndependent Q i) ∧
      ¬ StripTransfer Q 0 1 2) :=
  ⟨fun _ => Fin 2, Pstrip,
   strip_isWeakOrder, strip_coordinateOrderIndependent, strip_not_stripTransfer⟩

end OptionBC1aStripProbe
end CertificateChecklist
end WakkerRoadmap

/-! ## WP-C1.a strip-probe audit -/

#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aStripProbe.strip_coordinateOrderIndependent
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aStripProbe.strip_not_stripTransfer
#print axioms WakkerRoadmap.CertificateChecklist.OptionBC1aStripProbe.a1_does_not_imply_stripTransfer
