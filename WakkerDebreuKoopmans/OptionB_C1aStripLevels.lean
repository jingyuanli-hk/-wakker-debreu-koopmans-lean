/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 groundwork: the strip residual is level-independent

This file makes a genuine structural advance on **R1.1** (the §IV.5 cross-pair
cancellation crux, `CrossPairCancellationData = KzTransfer ∧ StripTransfer`) of
`OptionB_ResidualForwardConstructionInfrastructureRoadmap.md`.

## The observation

`StripTransfer P j k t` transports a `{j,k}`-difference indifference at a transfer
level `w` down to the **background** level `a t`:
`[x|r|w] ∼ [z|p|w] → [x|r|(a t)] ∼ [z|p|(a t)]`.

The "to `a t`" looks like it privileges the background's `t`-value.  It does not:
`tri a j k t · · c` *overwrites* coordinate `t` with `c` regardless of `a t`, and
the background `a` only enters off `{j,k,t}`.  So replacing `a` by
`Function.update a t c` (which agrees with `a` off `t`, and is overwritten at `t`)
shows the strip actually transports to **every** target level `c`, and likewise
between any two levels.

## What this file delivers (machine-checked, sound)

* `tri_bg_update_t` — `tri (Function.update a t c') j k t u v c = tri a j k t u v c`
  (the background's `t`-value is irrelevant — pure `Function.update` algebra).
* `stripTransfer_allLevels` — from `StripTransfer P j k t` (distinct `j,k,t`), the
  **all-levels** strip: `[x|r|w] ∼ [z|p|w] → [x|r|c] ∼ [z|p|c]` for *every* target
  level `c`, not just `a t`.
* `stripTransfer_betweenLevels` — consequently the indifference at any one level
  `w` transports to any other level `c` (both via the common-`w` premise).

This sharpens the residual: `StripTransfer` is exactly `t`-block independence at
*all* levels, the genuine KLST block-independence statement.  It is the clean
target for the §IV.5 forward construction (and confirms the residual is stated at
full strength, hiding nothing).

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
open Function

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-- **The background's `t`-value is irrelevant to `tri`.**

Updating the background at `t` (to any `c'`) before forming `tri … c` gives the
same profile, since `tri` overwrites coordinate `t` with `c` last.  Pure
`Function.update` algebra.  Audit `[propext]`-class (no choice). -/
theorem tri_bg_update_t (a : Profile X) (j k t : ι)
    (u : X j) (v : X k) (c c' : X t) :
    tri (Function.update a t c') j k t u v c = tri a j k t u v c := by
  unfold tri
  funext i
  by_cases hit : i = t
  · subst hit; simp [Function.update_self]
  · rw [Function.update_of_ne hit, Function.update_of_ne hit]
    by_cases hik : i = k
    · subst hik; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hik, Function.update_of_ne hik]
      by_cases hij : i = j
      · subst hij; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hij, Function.update_of_ne hij,
            Function.update_of_ne hit]

/-- **`StripTransfer` is level-independent: the all-levels strip.**

From `StripTransfer P j k t`, a `{j,k}`-difference indifference at any transfer
level `w` transports to **every** target level `c` (not merely the background's
`a t`):
`[x|r|w] ∼ [z|p|w] → [x|r|c] ∼ [z|p|c]`.

Proof: apply `StripTransfer` at the modified background `a' = Function.update a t c`
(whose `t`-value is `c`), then erase the background modification with
`tri_bg_update_t`.  Audit foundational-only. -/
theorem stripTransfer_allLevels
    [DecidableEq ι] {j k t : ι}
    (hStrip : StripTransfer P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (hw : P.indiff (tri a j k t x r w) (tri a j k t z p w)) :
    P.indiff (tri a j k t x r c) (tri a j k t z p c) := by
  -- Work at background a' := update a t c, where a' t = c.
  set a' : Profile X := Function.update a t c with ha'
  have hat : a' t = c := by rw [ha']; simp
  -- Premise at level w over a' (backgrounds agree via tri_bg_update_t).
  have hw' : P.indiff (tri a' j k t x r w) (tri a' j k t z p w) := by
    rw [ha', tri_bg_update_t, tri_bg_update_t]; exact hw
  -- Strip to level a' t = c.
  have hconcl := hStrip a' x z p r w hw'
  rw [hat] at hconcl
  rw [ha', tri_bg_update_t, tri_bg_update_t] at hconcl
  exact hconcl

/-- **`StripTransfer` transports between any two levels.**

A `{j,k}`-difference indifference at any level `w` transports to any other level
`c`.  Immediate from `stripTransfer_allLevels`.  Audit foundational-only. -/
theorem stripTransfer_betweenLevels
    [DecidableEq ι] {j k t : ι}
    (hStrip : StripTransfer P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (hw : P.indiff (tri a j k t x r w) (tri a j k t z p w)) :
    P.indiff (tri a j k t x r c) (tri a j k t z p c) :=
  stripTransfer_allLevels hStrip a x z p r w c hw

end ProductPref
end WakkerInfra

/-! ## R1.1 strip-levels audit -/

#print axioms WakkerInfra.ProductPref.tri_bg_update_t
#print axioms WakkerInfra.ProductPref.stripTransfer_allLevels
#print axioms WakkerInfra.ProductPref.stripTransfer_betweenLevels
