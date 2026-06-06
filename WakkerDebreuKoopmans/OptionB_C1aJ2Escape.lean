/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-C1.a forward step 3: J2 transfer-level existence from the
  Archimedean escape grid

This file advances the `HexagonResidualData` frontier (WP-C1.a) by discharging
its **J2 transfer-level existence** field from the §IV.2.6 Archimedean escape
grid, eliminating the explicit `t`-coordinate bracket that
`thirdCoordinateTransfer_J2_of_IVT` (`OptionB_C1aThirdCoordinate.lean`) took as a
hypothesis.

## What J2 asks

`HexagonResidualData.j2` (per Thomsen datum) requires a transfer level `w : X t`
with `[x|r|w] ∼ [y|r|c]` (`c = a t`).  `thirdCoordinateTransfer_J2_of_IVT`
produced `w` from the WP-T IVT engine *given* a `t`-bracket (`cHi ≽`-above,
`cLo ≼`-below).  The bracket reach was left as a hypothesis — exactly the
Archimedean residual the roadmap flagged.

## What this file delivers (machine-checked)

* `j2Exists_of_archimedeanEscape` — J2 existence from: connectedness of `X t`,
  preference continuity at the reference `[y|r|c]` (closed contour sets), and a
  **strict Archimedean standard sequence** in coordinate `t` *based at the slice*
  `[x|r|·]` that **escapes** the reference on both sides.  The bracket is derived
  from the escape via the engine-B reach lemmas (`archimedean_reach_above/below`)
  composed with the engine-A IVT (`archimedean_slice_crossing`).  No explicit
  bracket hypothesis remains; the only genuine input is the two-sided escape (the
  §IV.2.6 / WP-density content, proved necessary in
  `OptionB_EscapeGridNecessity.lean`).

This is the honest reduction: J2 is **not** an independent residual — it reduces
to the escape-grid content already carried by WP-density/WP-B1 (plus topology),
so the `HexagonResidualData` frontier is really the *two* cross-pair cancellation
residuals (`KzTransfer`, `StripTransfer`) plus the shared escape grid.

This file imports `OptionB_C1aThirdCoordinate` (for `tri` and the transfer defs)
and is **not** in the umbrella import.
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

/-- **J2 transfer-level existence from the Archimedean escape grid.**

Given coordinates `j, k, t`, a background `a`, slice values `x : X j`, `r : X k`,
and reference value `y : X j`, the transfer level `w : X t` with
`[x|r|w] ∼ [y|r|c]` (`c = a t`) exists, from:

* `ConnectedSpace (X t)` and preference continuity at the reference
  `b = [y|r|c]` (the closed upper/lower contour sets `hUpper`/`hLower`);
* a **strict Archimedean standard sequence** `σ` in coordinate `t` whose base
  realises the slice (`hbase : ∀ w, update σ.base t w = [x|r|w]`);
* the **two-sided escape** of the grid past `b` (`habove`, `hbelow`).

The bracket is derived from the escape (engine B,
`archimedean_reach_above/below`) and the crossing from connectedness +
continuity (engine A IVT, `archimedean_slice_crossing`).  So J2 reduces to the
§IV.2.6 escape-grid content (shared with WP-density/WP-B1) — it is not an
independent residual.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem j2Exists_of_archimedeanEscape
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι}
    [ConnectedSpace (X t)]
    (a : Profile X) (x y : X j) (r : X k)
    (σ : ProductPref.StandardSequence P t) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P t)
    (hbase : ∀ w : X t, Function.update σ.base t w = tri a j k t x r w)
    (hUpper : IsClosed {z : Profile X | P.weakPref z (tri a j k t y r (a t))})
    (hLower : IsClosed {z : Profile X | P.weakPref (tri a j k t y r (a t)) z})
    (habove : ∃ n : ℕ,
      ¬ P.weakPref (tri a j k t y r (a t)) (Function.update σ.base t (σ.α n)))
    (hbelow : ∃ n : ℕ,
      ¬ P.weakPref (Function.update σ.base t (σ.α n)) (tri a j k t y r (a t))) :
    ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t)) := by
  obtain ⟨c, hc⟩ :=
    WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_slice_crossing
      P σ hσ harchim (tri a j k t y r (a t)) hUpper hLower habove hbelow
  refine ⟨c, ?_⟩
  rw [hbase] at hc
  exact hc

/-- **`ThirdCoordinateTransfer` from the escape-grid J2 supplier + the two
cross-pair residuals.**

A convenience assembly: feed `j2Exists_of_archimedeanEscape` (uniformly over the
datum, packaged as `hJ2`) together with `KzTransfer` and `StripTransfer` into
`thirdCoordinateTransfer_of_components`.  This records that, with the escape grid
discharging J2, the third-coordinate transfer rests on exactly the two cross-pair
cancellation residuals.  Audit foundational-only. -/
theorem thirdCoordinateTransfer_of_escapeJ2_and_crossPair
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι}
    (hJ2 : ∀ (a : Profile X) (x y : X j) (r : X k),
      ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t)))
    (hKz : KzTransfer P j k t)
    (hStrip : StripTransfer P j k t) :
    ThirdCoordinateTransfer P j k t :=
  thirdCoordinateTransfer_of_components hJ2 hKz hStrip

/-- **J2 existence from a weakly-descending Archimedean grid seeded above the
reference (the leanest engine-B form).**

The fully-reduced J2 supplier: for a **strict, weakly-descending** Archimedean
standard sequence in coordinate `t` whose base realises the slice `[x|r|·]`, if
the grid's first point is **not weakly below** the reference `[y|r|c]`
(`hseed` — the natural seed condition), then the transfer level exists.  The
lower escape is automatic from descent, the upper escape is the seed, and the
crossing is the IVT.  **No two-sided escape hypothesis** — only the seed-above
condition plus the monotone grid (the §IV.2.6 standard-sequence content).  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem j2Exists_of_weaklyDescendingSeededAbove
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι}
    [ConnectedSpace (X t)]
    (a : Profile X) (x y : X j) (r : X k)
    (σ : ProductPref.StandardSequence P t) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P t)
    (hdesc : ∀ n, P.weakPref (Function.update σ.base t (σ.α n))
                             (Function.update σ.base t (σ.α (n + 1))))
    (hbase : ∀ w : X t, Function.update σ.base t w = tri a j k t x r w)
    (hUpper : IsClosed {z : Profile X | P.weakPref z (tri a j k t y r (a t))})
    (hLower : IsClosed {z : Profile X | P.weakPref (tri a j k t y r (a t)) z})
    (hseed : ¬ P.weakPref (tri a j k t y r (a t))
                          (Function.update σ.base t (σ.α 0))) :
    ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t)) := by
  obtain ⟨c, hc⟩ :=
    WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_weaklyDescending_slice_crossing_of_seedAbove
      P σ hσ harchim hdesc (tri a j k t y r (a t)) hUpper hLower hseed
  refine ⟨c, ?_⟩
  rw [hbase] at hc
  exact hc

end ProductPref
end WakkerInfra

/-! ## WP-C1.a J2-escape audit -/

#print axioms WakkerInfra.ProductPref.j2Exists_of_archimedeanEscape
#print axioms WakkerInfra.ProductPref.thirdCoordinateTransfer_of_escapeJ2_and_crossPair
#print axioms WakkerInfra.ProductPref.j2Exists_of_weaklyDescendingSeededAbove
