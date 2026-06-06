/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1: indifference-substitution rules for the diagonal trichotomy

This file proves another real, structural theorem about the single Thomsen
residue `TBlockDiagonalResidue` (R1.1's final-piece content,
`OptionB_C1aDiagonalUnifiedCapstone.lean`):

**The trichotomy class of a two-coord-different profile pair is invariant under
indifference-substitution at either endpoint.**

`OptionB_C1aDiagonalMixedTrans.lean` proved the cross-class transitivity rules
(`≻∘∼ = ≻`, `∼∘≽ = ≽`, etc.).  This file packages them as the standard
"well-defined on the indifference quotient" substitution rules: if you replace
the start (or end) of a uniform `≻` / `≽` / `∼` chain by an indifferent profile
pair, the relation still holds.

These are exactly the "preorder respects the equivalence relation" content —
the standard preorder-on-quotient calculus on the trade-off space.  The
substitution shape makes them directly usable for proof rewriting in any future
forward construction that wants to operate modulo the indifference class.

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_strict_subst_left` — substitute at the start of a `≻`.
* `tBlockDiagonalResidue_strict_subst_right` — substitute at the end of a `≻`.
* `tBlockDiagonalResidue_weakPref_subst_left` / `…_subst_right` — same for `≽`.
* `tBlockDiagonalResidue_indiff_subst_left` / `…_subst_right` — same for `∼`
  (these are direct from indifference symmetry + transitivity, but stated in
  the substitution shape for uniform usability).

All audit `[propext, Quot.sound]`.

This file imports `OptionB_C1aDiagonalMixedTrans` and is **not** in the
umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalMixedTrans

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

/-- **Left substitution for uniform `≻`.**

If `(x',r',·) ∼ (x,r,·)` uniformly and `(x,r,·) ≻ (z,p,·)` uniformly, then
`(x',r',·) ≻ (z,p,·)` uniformly.  Direct application of mixed-class transitivity
`∼∘≻ = ≻`.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_strict_subst_left
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x x' z : X j) (p r r' : X k)
    (hSub : ∀ c : X t, P.indiff (tri a j k t x' r' c) (tri a j k t x r c))
    (hRel : ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c)) :
    ∀ c : X t, P.strict (tri a j k t x' r' c) (tri a j k t z p c) :=
  tBlockDiagonalResidue_trans_indiff_strict a x' x z r p r' hSub hRel

/-- **Right substitution for uniform `≻`.**

If `(x,r,·) ≻ (z,p,·)` uniformly and `(z,p,·) ∼ (z',p',·)` uniformly, then
`(x,r,·) ≻ (z',p',·)` uniformly.  Direct application of mixed-class transitivity
`≻∘∼ = ≻`.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_strict_subst_right
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z z' : X j) (p p' r : X k)
    (hRel : ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c))
    (hSub : ∀ c : X t, P.indiff (tri a j k t z p c) (tri a j k t z' p' c)) :
    ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z' p' c) :=
  tBlockDiagonalResidue_trans_strict_indiff a x z z' p p' r hRel hSub

/-- **Left substitution for uniform `≽`.**

If `(x',r',·) ∼ (x,r,·)` uniformly and `(x,r,·) ≽ (z,p,·)` uniformly, then
`(x',r',·) ≽ (z,p,·)` uniformly.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_weakPref_subst_left
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x x' z : X j) (p r r' : X k)
    (hSub : ∀ c : X t, P.indiff (tri a j k t x' r' c) (tri a j k t x r c))
    (hRel : ∀ c : X t, P.weakPref (tri a j k t x r c) (tri a j k t z p c)) :
    ∀ c : X t, P.weakPref (tri a j k t x' r' c) (tri a j k t z p c) :=
  tBlockDiagonalResidue_trans_indiff_weakPref a x' x z r p r' hSub hRel

/-- **Right substitution for uniform `≽`.**

If `(x,r,·) ≽ (z,p,·)` uniformly and `(z,p,·) ∼ (z',p',·)` uniformly, then
`(x,r,·) ≽ (z',p',·)` uniformly.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_weakPref_subst_right
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z z' : X j) (p p' r : X k)
    (hRel : ∀ c : X t, P.weakPref (tri a j k t x r c) (tri a j k t z p c))
    (hSub : ∀ c : X t, P.indiff (tri a j k t z p c) (tri a j k t z' p' c)) :
    ∀ c : X t, P.weakPref (tri a j k t x r c) (tri a j k t z' p' c) :=
  tBlockDiagonalResidue_trans_weakPref_indiff a x z z' p p' r hRel hSub

/-- **Left substitution for uniform `∼`.**

If `(x',r',·) ∼ (x,r,·)` uniformly and `(x,r,·) ∼ (z,p,·)` uniformly, then
`(x',r',·) ∼ (z,p,·)` uniformly.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_indiff_subst_left
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x x' z : X j) (p r r' : X k)
    (hSub : ∀ c : X t, P.indiff (tri a j k t x' r' c) (tri a j k t x r c))
    (hRel : ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c)) :
    ∀ c : X t, P.indiff (tri a j k t x' r' c) (tri a j k t z p c) :=
  tBlockDiagonalResidue_trans_indiff a x' x z r p r' hSub hRel

/-- **Right substitution for uniform `∼`.**

If `(x,r,·) ∼ (z,p,·)` uniformly and `(z,p,·) ∼ (z',p',·)` uniformly, then
`(x,r,·) ∼ (z',p',·)` uniformly.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_indiff_subst_right
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x z z' : X j) (p p' r : X k)
    (hRel : ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c))
    (hSub : ∀ c : X t, P.indiff (tri a j k t z p c) (tri a j k t z' p' c)) :
    ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z' p' c) :=
  tBlockDiagonalResidue_trans_indiff a x z z' p p' r hRel hSub

/-- **Two-sided substitution for uniform `≻`.**

The packaged form: substituting at *both* endpoints simultaneously preserves
the uniform strict class.  This is the most operationally useful shape for any
future forward construction that wants to operate modulo the indifference
class.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_strict_subst_both
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x x' z z' : X j) (p p' r r' : X k)
    (hSubL : ∀ c : X t, P.indiff (tri a j k t x' r' c) (tri a j k t x r c))
    (hRel : ∀ c : X t, P.strict (tri a j k t x r c) (tri a j k t z p c))
    (hSubR : ∀ c : X t, P.indiff (tri a j k t z p c) (tri a j k t z' p' c)) :
    ∀ c : X t, P.strict (tri a j k t x' r' c) (tri a j k t z' p' c) :=
  tBlockDiagonalResidue_strict_subst_right a x' z z' p p' r'
    (tBlockDiagonalResidue_strict_subst_left a x x' z p r r' hSubL hRel)
    hSubR

/-- **Two-sided substitution for uniform `≽`.**  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_weakPref_subst_both
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x x' z z' : X j) (p p' r r' : X k)
    (hSubL : ∀ c : X t, P.indiff (tri a j k t x' r' c) (tri a j k t x r c))
    (hRel : ∀ c : X t, P.weakPref (tri a j k t x r c) (tri a j k t z p c))
    (hSubR : ∀ c : X t, P.indiff (tri a j k t z p c) (tri a j k t z' p' c)) :
    ∀ c : X t, P.weakPref (tri a j k t x' r' c) (tri a j k t z' p' c) :=
  tBlockDiagonalResidue_weakPref_subst_right a x' z z' p p' r'
    (tBlockDiagonalResidue_weakPref_subst_left a x x' z p r r' hSubL hRel)
    hSubR

/-- **Two-sided substitution for uniform `∼`.**  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_indiff_subst_both
    [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (a : Profile X) (x x' z z' : X j) (p p' r r' : X k)
    (hSubL : ∀ c : X t, P.indiff (tri a j k t x' r' c) (tri a j k t x r c))
    (hRel : ∀ c : X t, P.indiff (tri a j k t x r c) (tri a j k t z p c))
    (hSubR : ∀ c : X t, P.indiff (tri a j k t z p c) (tri a j k t z' p' c)) :
    ∀ c : X t, P.indiff (tri a j k t x' r' c) (tri a j k t z' p' c) :=
  tBlockDiagonalResidue_indiff_subst_right a x' z z' p p' r'
    (tBlockDiagonalResidue_indiff_subst_left a x x' z p r r' hSubL hRel)
    hSubR

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-subst audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_subst_left
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_subst_right
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_weakPref_subst_left
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_weakPref_subst_right
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_subst_left
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_subst_right
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_strict_subst_both
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_weakPref_subst_both
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff_subst_both
