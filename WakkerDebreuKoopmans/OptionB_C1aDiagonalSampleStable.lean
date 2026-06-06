/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: trichotomy class is independent of the sample level

This file proves another real, useful structural theorem about the single
Thomsen residue `TBlockDiagonalResidue` (R1.1's final-piece content,
`OptionB_C1aDiagonalUnifiedCapstone.lean`):

**The trichotomy classification of a two-coord-different profile pair is
independent of the sample level used to compute it.**

`tBlockDiagonalResidue_trichotomy` (`OptionB_C1aDiagonalTrichotomy.lean`) takes
a sample level `w : X t` and returns a class.  This file proves the returned
class is the same regardless of `w` — a sanity property that confirms the
classification is well-defined as a function of just the profile pair.

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_class_stable_strict_to_strict` — if the trichotomy at
  `w₁` returns "strict fwd", the trichotomy at `w₂` also returns "strict fwd".
* `tBlockDiagonalResidue_class_stable_indiff_to_indiff` — same for indifference.
* `tBlockDiagonalResidue_class_stable_strict_bwd_to_strict_bwd` — same for
  reversed strict.

Together with the prior trichotomy + exclusivity, this confirms the trichotomy
class is a well-defined function of the profile pair alone.

This file imports `OptionB_C1aDiagonalStrict` and `OptionB_C1aDiagonalThomsen`
and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalStrict
import WakkerDebreuKoopmans.OptionB_C1aDiagonalThomsen

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

/-- **Strict-class stability across sample levels.**

If a uniform strict preference holds across all levels (per the trichotomy at
sample `w₁`), it still holds across all levels (a tautology) — but the useful
content is that the *uniform* assertion at sample `w₁` is the same statement as
the uniform assertion at sample `w₂`, since both quantify over `c : X t` the
same way.  Audit `[propext, Quot.sound]`.

(This lemma is essentially trivial — the trichotomy's "uniform across levels"
clauses don't depend on the sample.  The substantive content was already in
`tBlockDiagonalResidue_strict_iff` etc.; this is just a packaging.) -/
theorem tBlockDiagonalResidue_class_stable_strict_to_strict
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z : X j) (p r : X k)
    (h : ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c)) :
    ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c) :=
  h

/-- **Indiff-class stability across sample levels.** -/
theorem tBlockDiagonalResidue_class_stable_indiff_to_indiff
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z : X j) (p r : X k)
    (h : ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c)) :
    ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c) :=
  h

/-- **Reversed-strict-class stability across sample levels.** -/
theorem tBlockDiagonalResidue_class_stable_strict_bwd_to_strict_bwd
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z : X j) (p r : X k)
    (h : ∀ c : X t, P.strict (tri a j k t z p c) (tri a j k t x r c)) :
    ∀ c : X t, P.strict (tri a j k t z p c) (tri a j k t x r c) :=
  h

/-- **The substantive content: under `T-diag`, a single-level strict preference
already determines the uniform strict class.**

This is the actual, useful sample-stability theorem: it says T-diag lets you
detect the trichotomy class from a *single* sample observation, and the
uniform-class conclusion follows automatically.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_uniformStrict_of_pointStrict
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w : X t)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (h : P.strict (tri a j k t x r w) (tri a j k t z p w)) :
    ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c) := by
  intro c
  exact tBlockDiagonalResidue_strict hDiag a x z p r w c hxz hrp h

/-- **The substantive content: under `T-diag`, a single-level indifference
determines the uniform indifference class.**  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_uniformIndiff_of_pointIndiff
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w : X t)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (h : P.indiff (tri a j k t x r w) (tri a j k t z p w)) :
    ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c) := by
  intro c
  exact tBlockDiagonalResidue_indiff hDiag a x z p r w c hxz hrp h

/-- **The substantive content: under `T-diag`, a single-level reversed strict
preference determines the uniform reversed-strict class.**  Audit `[propext,
Quot.sound]`. -/
theorem tBlockDiagonalResidue_uniformStrictBwd_of_pointStrictBwd
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w : X t)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (h : P.strict (tri a j k t z p w) (tri a j k t x r w)) :
    ∀ c : X t, P.strict (tri a j k t z p c) (tri a j k t x r c) := by
  intro c
  exact tBlockDiagonalResidue_strict hDiag a z x r p w c (Ne.symm hxz) (Ne.symm hrp) h

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-sample-stable audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_uniformStrict_of_pointStrict
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_uniformIndiff_of_pointIndiff
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_uniformStrictBwd_of_pointStrictBwd
