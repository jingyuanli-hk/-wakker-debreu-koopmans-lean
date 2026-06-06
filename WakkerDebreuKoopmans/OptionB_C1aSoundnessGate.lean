/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — §5 C1.a soundness gate

This file runs the soundness gate mandated by §5 of
`OptionB_UnconditionalConstructionRoadmap.md`, **before** any investment in the
C1.a slice-calibration work package.

## The gate question

The roadmap's WP-C1.a plan is: "extract the hexagon / Thomsen double-cancellation
condition as the genuine cross-coordinate consequence of `TradeoffConsistency`."
This only works if the *formalized* `WakkerInfra.ProductPref.TradeoffConsistency`
is actually strong enough to imply the hexagon condition.  If it is strictly
weaker, the additive representation cannot honestly be claimed "from the six
axioms" without an explicit coordinate-independence / hexagon hypothesis.

## The gate verdict (proved below): NEGATIVE

The formalized `TradeoffConsistency.consistent` is **logically equivalent** to
single-coordinate *indifference base-independence*:

> if the value swap `v ↦ w` at one coordinate `j` is indifferent at *some*
> background, it is indifferent at *every* background.

We prove this equivalence (`tradeoffConsistency_iff_indiffBaseIndependent`).
The three "extra" premise indifferences (`indiff c d`, `indiff e f`) and all the
cross-equalities in `consistent` are therefore **redundant**: a single premise
indifference already forces the conclusion.

Consequences for the gate:

* The formalized axiom carries **no** content relating two *different* value
  pairs or two *different* coordinates.  The standard additive-conjoint
  **Thomsen double-cancellation** `StandardThomsen` relates three indifferences
  across different value pairs, so it is **not** a logical consequence of
  `consistent`.  (This re-confirms, at the axiom level, the no-go results
  `RawAxiomDischargersHexagon` §11 and
  `Certificates.tradeoffConsistency_and_assemblyInput_not_sufficient_for_pairwiseStep4TradeoffMachinery`
  already in the repo.)
* Therefore **WP-C1.a as a pure derivation is impossible.**  The hexagon /
  coordinate-independence content is genuinely additional structural input.

## What Option B must do (honest determination)

Discharging C1 requires adding coordinate independence (equivalently the hexagon
condition, or Wakker's actual cross-pair tradeoff-equivalence relation `≽*`) as
an **explicit named structural hypothesis**, matching Wakker (1989)'s real
hypothesis set — whose "tradeoff consistency / cardinal coordinate independence"
is the cross-pair relation, *strictly stronger* than the single-coordinate
`consistent` formalized here.  Both papers' headline claim must then read "from
Wakker's structural axioms **including coordinate independence**", not "from the
six axioms" simpliciter.

This file is standalone (imports only `Core`) and is **not** in the umbrella
import; it is the gate record.
-/

import WakkerDebreuKoopmans.Core

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v}

open Function

/-- **Single-coordinate indifference base-independence.**

If a value swap `v ↦ w` at coordinate `j` is indifferent at one background
profile, it is indifferent at every background profile.  This is a purely
single-coordinate property: it never mentions a second coordinate or a second
value pair. -/
def IndiffBaseIndependent (P : ProductPref X) : Prop :=
  ∀ (j : ι) (base base' : Profile X) (v w : X j),
    P.indiff (Function.update base j v) (Function.update base j w) →
    P.indiff (Function.update base' j v) (Function.update base' j w)

/-- A profile agreeing with `x` off `{j}` is exactly `x` updated at `j`. -/
private lemma eq_update_of_agreeOff_singleton
    {x y : Profile X} {j : ι} (h : Profile.agreeOff {j} x y) :
    y = Function.update x j (y j) := by
  funext i
  by_cases hij : i = j
  · subst hij; rw [Function.update_self]
  · rw [Function.update_of_ne hij]
    exact (h i (by simpa using hij)).symm

/-- **Forward direction of the gate: `TradeoffConsistency ⇒ indifference
base-independence.**

Instantiating `consistent` with `c = a, d = b, e = a, f = b` shows the swap
transfers from background `base` to background `base'`. -/
theorem indiffBaseIndependent_of_tradeoffConsistency
    (P : ProductPref X) [TradeoffConsistency P] :
    IndiffBaseIndependent P := by
  intro j base base' v w hbase
  -- a, b at background `base`; g, h at background `base'`; c=a,d=b,e=a,f=b.
  have hagree_ab :
      Profile.agreeOff {j} (Function.update base j v) (Function.update base j w) := by
    intro i hi
    have hij : i ≠ j := by simpa using hi
    rw [Function.update_of_ne hij, Function.update_of_ne hij]
  have hagree_gh :
      Profile.agreeOff {j} (Function.update base' j v) (Function.update base' j w) := by
    intro i hi
    have hij : i ≠ j := by simpa using hi
    rw [Function.update_of_ne hij, Function.update_of_ne hij]
  refine TradeoffConsistency.consistent
    (P := P) j
    (Function.update base j v) (Function.update base j w)
    (Function.update base j v) (Function.update base j w)
    (Function.update base j v) (Function.update base j w)
    (Function.update base' j v) (Function.update base' j w)
    hagree_ab hagree_ab hagree_ab hagree_gh
    hbase hbase hbase
    ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [Function.update_self]
  · simp [Function.update_self]

/-- **Reverse direction of the gate: indifference base-independence ⇒
`TradeoffConsistency`.**

Only the *first* premise indifference `indiff a b` is used; `indiff c d` and
`indiff e f` are discarded.  This is the precise sense in which the three
premise indifferences of `consistent` are redundant. -/
theorem tradeoffConsistency_of_indiffBaseIndependent
    (P : ProductPref X) (hbi : IndiffBaseIndependent P) :
    TradeoffConsistency P := by
  refine ⟨?_⟩
  intro j a b c d e f g h hab _hcd _hef hgh hiab _hicd _hief
    hac hbd _hce _hdf hag hbh
  -- Rewrite a, b, g, h as single-coordinate updates of their backgrounds.
  have ha : a = Function.update a j (a j) := (Function.update_eq_self j a).symm
  have hb : b = Function.update a j (b j) := eq_update_of_agreeOff_singleton hab
  have hg : g = Function.update g j (g j) := (Function.update_eq_self j g).symm
  have hh : h = Function.update g j (h j) := eq_update_of_agreeOff_singleton hgh
  -- The swap values `(a j, b j)` at backgrounds `a` and `g` coincide with
  -- `(g j, h j)` because `a j = g j` and `b j = h j`.
  have hindiff_a : P.indiff (Function.update a j (a j)) (Function.update a j (b j)) := by
    rw [← ha, ← hb]; exact hiab
  have hindiff_g :
      P.indiff (Function.update g j (a j)) (Function.update g j (b j)) :=
    hbi j a g (a j) (b j) hindiff_a
  -- Transport `(a j, b j)` to `(g j, h j)` via `a j = g j`, `b j = h j`.
  rw [hg, hh, ← hag, ← hbh]
  exact hindiff_g

/-- **The gate verdict, as an iff.**

`TradeoffConsistency P ↔ IndiffBaseIndependent P`.  The formalized tradeoff
consistency axiom is *exactly* single-coordinate indifference base-independence —
nothing more.  In particular it contains no cross-pair double-cancellation
(Thomsen) content, so the hexagon condition is not a consequence of it; the
C1.a "extract the hexagon from `TradeoffConsistency`" route is therefore
impossible, and Option B must take coordinate independence as an explicit
structural input. -/
theorem tradeoffConsistency_iff_indiffBaseIndependent
    (P : ProductPref X) :
    TradeoffConsistency P ↔ IndiffBaseIndependent P :=
  ⟨fun _ => indiffBaseIndependent_of_tradeoffConsistency P,
   tradeoffConsistency_of_indiffBaseIndependent P⟩

end ProductPref
end WakkerInfra

/-! ## Gate audit

The equivalence and both directions are sorry-free and depend only on the
standard foundations.  This is the machine-checked record that the formalized
`TradeoffConsistency` is *exactly* single-coordinate indifference
base-independence — the negative verdict of the §5 gate. -/

#print axioms WakkerInfra.ProductPref.indiffBaseIndependent_of_tradeoffConsistency
#print axioms WakkerInfra.ProductPref.tradeoffConsistency_of_indiffBaseIndependent
#print axioms WakkerInfra.ProductPref.tradeoffConsistency_iff_indiffBaseIndependent
