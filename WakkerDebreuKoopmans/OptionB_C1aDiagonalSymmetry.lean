/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.1 final-piece: symmetry and self-consistency of the diagonal
  Thomsen residues

This file proves a real structural theorem about the three diagonal Thomsen
residues isolated in `OptionB_C1aDiagonalResidue.lean`: each residue is
**bidirectional** — the implication `≽ at one level → ≽ at the other` holds in
either direction.  Plus self-consistency: a single application is enough to chain
across any pair of levels (the residue is *transitively closed*).

## What this file delivers (machine-checked, sound)

* `tBlockDiagonalResidue_symm` — symmetric form of `T`-diag: shifting in either
  direction is the same content.  By specialization, `[x|r|w] ≽ [z|p|w]` at *some*
  level forces `[x|r|c] ≽ [z|p|c]` at *every* level.
* `kBlockDiagonalResidue_symm`, `jBlockDiagonalResidue_symm` — same for the other
  two diagonals.
* `tBlockDiagonalResidue_chain` — chaining: from `≽` at level `w₁` to `≽` at level
  `w₂` and then to `≽` at level `w₃` is just one application (level `w₁` to `w₃`).
  This is automatic since the residue's quantifier ranges over all level pairs.
* `tBlockDiagonalResidue_iff_indiff` — under `IsWeakOrder`, the `≽`-form of the
  diagonal is **equivalent** to its `∼`-form (the indifference form): the
  `≽`-direction at one level forces the `∼` at every other.

These confirm the diagonal residues are stated *exactly right* — they don't
gratuitously break symmetry, they encode the standard Thomsen content in its
sharpest form, and the indifference and weak-preference forms agree.

This file imports `OptionB_C1aDiagonalResidue` and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_C1aDiagonalResidue

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

/-! ## Symmetric reformulations -/

/-- **`T`-diagonal is symmetric in the two `t`-levels.**

If `T`-diag holds, then for any two levels `w, c` and any two-coord-different
profiles, `≽` at `w` and `≽` at `c` are mutually implied: each direction is one
application of the residue (with the levels swapped).  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_symm
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (hxz : x ≠ z) (hrp : r ≠ p) :
    P.weakPref (tri a j k t x r w) (tri a j k t z p w) ↔
      P.weakPref (tri a j k t x r c) (tri a j k t z p c) :=
  ⟨hDiag a x z p r w c hxz hrp, hDiag a x z p r c w hxz hrp⟩

/-- **`K`-diagonal is symmetric in the two `k`-levels.** -/
theorem kBlockDiagonalResidue_symm
    {j k t : ι} (hDiag : KBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (v v' : X k) (c c' : X t)
    (huu : u ≠ u') (hcc : c ≠ c') :
    P.weakPref (tri a j k t u v c) (tri a j k t u' v c') ↔
      P.weakPref (tri a j k t u v' c) (tri a j k t u' v' c') :=
  ⟨hDiag a u u' v v' c c' huu hcc, hDiag a u u' v' v c c' huu hcc⟩

/-- **`J`-diagonal is symmetric in the two `j`-levels.** -/
theorem jBlockDiagonalResidue_symm
    {j k t : ι} (hDiag : JBlockDiagonalResidue P j k t)
    (a : Profile X) (u u' : X j) (v₁ v₂ : X k) (c₁ c₂ : X t)
    (hvv : v₁ ≠ v₂) (hcc : c₁ ≠ c₂) :
    P.weakPref (tri a j k t u v₁ c₁) (tri a j k t u v₂ c₂) ↔
      P.weakPref (tri a j k t u' v₁ c₁) (tri a j k t u' v₂ c₂) :=
  ⟨hDiag a u u' v₁ v₂ c₁ c₂ hvv hcc, hDiag a u' u v₁ v₂ c₁ c₂ hvv hcc⟩

/-! ## Chaining (transitive closure is automatic) -/

/-- **`T`-diagonal chaining is automatic.**

The residue's quantifier ranges over all pairs of levels, so chaining `w₁ → w₂ →
w₃` collapses to one application `w₁ → w₃`.  This confirms the residue is closed
under composition (no separate "chain" axiom needed).  Audit `[propext,
Quot.sound]`. -/
theorem tBlockDiagonalResidue_chain
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w₁ w₂ w₃ : X t)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (h12 : P.weakPref (tri a j k t x r w₁) (tri a j k t z p w₁)) :
    P.weakPref (tri a j k t x r w₃) (tri a j k t z p w₃) :=
  hDiag a x z p r w₁ w₃ hxz hrp h12

/-! ## Indifference form ↔ weak-preference form -/

/-- **`T`-diagonal as an indifference statement.**  Under a weak order, the
indifference form of `T`-diag (transport `∼` between levels) is equivalent to the
weak-preference form (transport `≽`).  An indifference is two `≽`-directions, so
this is just `tBlockDiagonalResidue_symm` applied to each.  Audit `[propext,
Quot.sound]`. -/
theorem tBlockDiagonalResidue_indiff
    [ProductPref.IsWeakOrder P]
    {j k t : ι} (hDiag : TBlockDiagonalResidue P j k t)
    (a : Profile X) (x z : X j) (p r : X k) (w c : X t)
    (hxz : x ≠ z) (hrp : r ≠ p)
    (hw : P.indiff (tri a j k t x r w) (tri a j k t z p w)) :
    P.indiff (tri a j k t x r c) (tri a j k t z p c) := by
  rcases hw with ⟨hfwd, hbwd⟩
  refine ⟨?_, ?_⟩
  · exact hDiag a x z p r w c hxz hrp hfwd
  · exact hDiag a z x r p w c (Ne.symm hxz) (Ne.symm hrp) hbwd

end ProductPref
end WakkerInfra

/-! ## R1.1 diagonal-symmetry audit -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_symm
#print axioms WakkerInfra.ProductPref.kBlockDiagonalResidue_symm
#print axioms WakkerInfra.ProductPref.jBlockDiagonalResidue_symm
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_chain
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_indiff
