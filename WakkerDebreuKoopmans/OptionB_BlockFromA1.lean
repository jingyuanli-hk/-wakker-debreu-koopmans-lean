/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — final piece: A1 gives the single-coordinate-difference part of the
  KLST block conditions; the irreducible Thomsen residue is the two-coordinate part

This file makes a genuine, sharp forward step on the **final open piece** of the
Option B construction (`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`):
deriving the three KLST block-independence conditions
(`TBlockWeakIndependent`, `KBlockWeakIndependent`, `JBlockWeakIndependent`,
`OptionB_C1aKLSTCapstone.lean`) from the structural axioms.

## What A1 alone gives (proved here)

Single-coordinate independence A1 (`CoordinateOrderIndependent`, the structural
field) says the `≽`-order of a value swap at one coordinate is background-
independent.  Each KLST block condition compares two profiles differing in **two**
coordinates of the complementary block (e.g. `TBlockWeakIndependent` compares
`[x|r|·]` vs `[z|p|·]`, differing in both `j` and `k`).  When the two profiles
differ in only **one** block-coordinate, the comparison *is* a single-coordinate
`coordPref`, and shifting the third coordinate's common value is just a background
change — which A1 absorbs.

So A1 yields exactly the **single-coordinate-difference restriction** of each
block condition.  The genuine Thomsen content is precisely the step from
one-coordinate to two-coordinate differences — which the probes
(`OptionB_C1aHexagonProbe`/`StripProbe`/`KzProbe`) confirm A1 cannot make.

## What this file delivers (machine-checked, sound)

* `tri_eq_update_k` / `tri_eq_update_j` — reassociation lemmas writing a `tri`
  profile as a single coordinate-`k` (resp. `j`) update over a packed background.
* `tBlockWeakIndependentRestricted_of_a1` — the `x = z` (differ-only-in-`k`)
  restriction of `TBlockWeakIndependent` from A1 on `k`.
* `kBlockWeakIndependentRestricted_of_a1` — the `u = u'` (differ-only-in-`t`)
  restriction of `KBlockWeakIndependent` from A1 on `t`.
* `jBlockWeakIndependentRestricted_of_a1` — the `v₁ = v₂` (differ-only-in-`t`)
  restriction of `JBlockWeakIndependent` from A1 on `t`.

Each restricted condition is the part of the block condition that **is** free from
A1; the complementary two-coordinate-difference part is the irreducible §IV.5
Thomsen residue (the precise, now-isolated open content).

This file imports `OptionB_C1aKzAnchor` (for the three block defs) and
`OptionB_CoordinateIndependence` (A1, `coordPref`) and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_C1aKzAnchor
import WakkerDebreuKoopmans.OptionB_CoordinateIndependence

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

/-- A `tri` profile is a single coordinate-`k` update over the packed background
`update (update a j u) t c` (valid since `k ≠ t`: the `k`- and `t`-updates
commute). -/
theorem tri_eq_update_k (a : Profile X) {j k t : ι} (hkt : k ≠ t)
    (u : X j) (v : X k) (c : X t) :
    tri a j k t u v c
      = Function.update (Function.update (Function.update a j u) t c) k v := by
  unfold tri
  rw [Function.update_comm hkt]

/-- A `tri` profile is a single coordinate-`j` update over the packed background
`update (update a k v) t c` (valid since `j ≠ k` and `j ≠ t`). -/
theorem tri_eq_update_j (a : Profile X) {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t)
    (u : X j) (v : X k) (c : X t) :
    tri a j k t u v c
      = Function.update (Function.update (Function.update a k v) t c) j u := by
  unfold tri
  -- Goal: update (update (update a j u) k v) t c = update (update (update a k v) t c) j u.
  -- Strategy: pull `j u` outermost step by step.
  -- Step 1: swap the inner pair (update _ j u) (update _ k v).
  -- update (update (update a j u) k v) t c
  --   = update (update (update a k v) j u) t c    by update_comm hjk on the inner pair
  rw [Function.update_comm hjk u v a]
  -- Now: update (update (update a k v) j u) t c = update (update (update a k v) t c) j u.
  -- Step 2: swap the outer pair (update _ j u) (update _ t c).
  rw [Function.update_comm hjt u c (Function.update a k v)]

/-- **`TBlockWeakIndependent` (restricted to `x = z`) from A1 on `k`.**

When the two profiles differ only in coordinate `k` (common `j`-value `x`), the
`t`-block comparison `[x|r|w] ≽ [x|p|w]` is the single-coordinate `k`-comparison
`coordPref k _ r p`; shifting the common `t`-value `w → c` only changes the
background, which A1 on `k` absorbs.  Audit `[propext, Quot.sound]`. -/
theorem tBlockWeakIndependentRestricted_of_a1
    {j k t : ι} (hkt : k ≠ t)
    (hA1k : CoordinateOrderIndependent P k)
    (a : Profile X) (x : X j) (p r : X k) (w c : X t)
    (hw : P.weakPref (tri a j k t x r w) (tri a j k t x p w)) :
    P.weakPref (tri a j k t x r c) (tri a j k t x p c) := by
  -- Rewrite both `tri`s as coordinate-`k` updates over packed backgrounds.
  rw [tri_eq_update_k a hkt, tri_eq_update_k a hkt] at hw
  rw [tri_eq_update_k a hkt, tri_eq_update_k a hkt]
  -- `hw` is `coordPref k Bw r p`; goal is `coordPref k Bc r p`; apply A1 on `k`.
  exact hA1k (Function.update (Function.update a j x) t w)
             (Function.update (Function.update a j x) t c) r p hw

/-- **`KBlockWeakIndependent` (restricted to `u = u'`) from A1 on `t`.**

When the two profiles differ only in coordinate `t` (common `j`-value `u`), the
`k`-block comparison is the single-coordinate `t`-comparison; shifting the common
`k`-value `v → v'` only changes the background, absorbed by A1 on `t`.  Audit
`[propext, Quot.sound]`. -/
theorem kBlockWeakIndependentRestricted_of_a1
    {j k t : ι} (hkt : k ≠ t)
    (hA1t : CoordinateOrderIndependent P t)
    (a : Profile X) (u : X j) (v v' : X k) (c c' : X t)
    (hw : P.weakPref (tri a j k t u v c) (tri a j k t u v c')) :
    P.weakPref (tri a j k t u v' c) (tri a j k t u v' c') := by
  -- Rewrite as coordinate-`t` updates: tri a j k t u v c = update (update (update a j u) k v) t c.
  have key : ∀ (vv : X k) (cc : X t),
      tri a j k t u vv cc
        = Function.update (Function.update (Function.update a j u) k vv) t cc := by
    intro vv cc; rfl
  rw [key, key] at hw
  rw [key, key]
  -- coordPref t Bv c c' → coordPref t Bv' c c' via A1 on t.
  exact hA1t (Function.update (Function.update a j u) k v)
             (Function.update (Function.update a j u) k v') c c' hw

/-- **`JBlockWeakIndependent` (restricted to `v₁ = v₂`) from A1 on `t`.**

When the two profiles differ only in coordinate `t` (common `k`-value `v`), the
`j`-block comparison is the single-coordinate `t`-comparison; shifting the common
`j`-value `u → u'` only changes the background, absorbed by A1 on `t`.  Audit
`[propext, Quot.sound]`. -/
theorem jBlockWeakIndependentRestricted_of_a1
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t)
    (hA1t : CoordinateOrderIndependent P t)
    (a : Profile X) (u u' : X j) (v : X k) (c₁ c₂ : X t)
    (hw : P.weakPref (tri a j k t u v c₁) (tri a j k t u v c₂)) :
    P.weakPref (tri a j k t u' v c₁) (tri a j k t u' v c₂) := by
  have key : ∀ (uu : X j) (cc : X t),
      tri a j k t uu v cc
        = Function.update (Function.update (Function.update a j uu) k v) t cc := by
    intro uu cc; rfl
  rw [key, key] at hw
  rw [key, key]
  -- coordPref t (Bu) c₁ c₂ → coordPref t (Bu') c₁ c₂ via A1 on t.
  exact hA1t (Function.update (Function.update a j u) k v)
             (Function.update (Function.update a j u') k v) c₁ c₂ hw

end ProductPref
end WakkerInfra

/-! ## Final piece — A1-restricted block independence audit -/

#print axioms WakkerInfra.ProductPref.tri_eq_update_k
#print axioms WakkerInfra.ProductPref.tri_eq_update_j
#print axioms WakkerInfra.ProductPref.tBlockWeakIndependentRestricted_of_a1
#print axioms WakkerInfra.ProductPref.kBlockWeakIndependentRestricted_of_a1
#print axioms WakkerInfra.ProductPref.jBlockWeakIndependentRestricted_of_a1
