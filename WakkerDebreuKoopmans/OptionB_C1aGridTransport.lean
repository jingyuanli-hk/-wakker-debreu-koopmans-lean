/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — R1.2 transport (DRAFT SCAFFOLD): grid-restricted residue ⟹ full residue

> **⚠ STATUS: forward-construction scaffold for the R1.2 transport.**  Like
> `OptionB_C1aGridThomsen.lean`, this file is deliberately **NOT** in the umbrella
> import.  It is **`sorry`-free**: the transport from the grid-restricted
> `TBlockDiagonalResidue` to the full residue is reduced — by pure weak order — to
> a single named **level-stable grid-coverage** residual (every `{j,k}`-slice
> value has a grid representative whose indices are independent of the `t`-level),
> which is proved *necessary* under a representation (the soundness gate) and is
> exactly the §IV.2.6 Archimedean-density content the project already carries
> elsewhere.  Everything else is theorem-backed at
> `[propext, Classical.choice, Quot.sound]`.

## The R1.2 problem

`OptionB_C1aGridThomsen.gridTBlockDiagonalResidue_of_frontier` produces the
`t`-level invariance of the `{j,k}`-comparison on **grid points** `(αⱼ m, αₖ n)`:
```
[αⱼ m | αₖ n | w] ≽ [αⱼ m' | αₖ n' | w]  →  [αⱼ m | αₖ n | c] ≽ [αⱼ m' | αₖ n' | c].
```
The full `TBlockDiagonalResidue P j k t` is the same statement for **arbitrary**
`x, z : X j` and `r, p : X k`.  R1.2 lifts the former to the latter.

## The honest decomposition

The transport is *pure weak order* once each off-grid `{j,k}`-slice value is
replaced by a `tri`-indifferent grid representative **whose indices do not depend
on the `t`-level** (so the same grid comparison serves at both `w` and `c`).  That
replacement is the genuine content, isolated as `StableGridIndifferentCover`:

* **`StableGridIndifferentCover`** — a function `rep : X j → X k → ℕ × ℕ` such that
  for every `(x, v)` and **every** level `c`, `[x | v | c] ∼ [αⱼ (rep x v).1 | αₖ
  (rep x v).2 | c]`.  Level-stability (one index pair per `(x,v)`, all levels) is
  what makes the transport work; it holds under a rep because the matching is the
  level-independent equation `V_j (αⱼ m) + V_k (αₖ n) = V_j x + V_k v`.
* **`tBlockDiagonalResidue_of_gridRestricted_and_stableCover`** — the transport:
  full residue from {grid-restricted residue + stable cover}, by replacing each
  profile's `{j,k}`-values with their (level-stable) grid representatives and
  applying the grid-restricted residue to the resulting grid comparison.

Imports `OptionB_C1aGridThomsen` (for `CalibratedJKGrid`, `tri`, the grid
helpers, and the frontier capstone `gridTBlockDiagonalResidue_of_frontier`).
-/

import WakkerDebreuKoopmans.OptionB_C1aGridThomsen
import WakkerDebreuKoopmans.OptionB_C1aDiagonalBaseIndep
import WakkerDebreuKoopmans.OptionB_C1aDiagonalUnifiedCapstone
import WakkerDebreuKoopmans.OptionB_C1aDiagonalHexagon
import WakkerDebreuKoopmans.OptionB_C1aJ2Escape
import WakkerDebreuKoopmans.OptionB_ResidualSharedInfrastructure
import WakkerDebreuKoopmans.Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open WakkerDebreuKoopmans
open Function Finset

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-! ## §A.  Indifference is `≽`-substitutable (theorem-backed, weak order only) -/

/-- Substitute the left profile of a `≽` by an indifferent one (weak order). -/
private theorem weakPref_subst_left
    [ProductPref.IsWeakOrder P] {x x' y : Profile X}
    (hx : P.indiff x x') (hxy : P.weakPref x y) : P.weakPref x' y :=
  ProductPref.IsWeakOrder.transitive _ _ _ hx.2 hxy

/-- Substitute the right profile of a `≽` by an indifferent one (weak order). -/
private theorem weakPref_subst_right
    [ProductPref.IsWeakOrder P] {x y y' : Profile X}
    (hy : P.indiff y y') (hxy : P.weakPref x y) : P.weakPref x y' :=
  ProductPref.IsWeakOrder.transitive _ _ _ hxy hy.1

/-- Local indifference symmetry. -/
private theorem indiff_symm {x y : Profile X} (h : P.indiff x y) : P.indiff y x :=
  ⟨h.2, h.1⟩

/-! ## §B.  The level-stable grid-coverage residual (the §IV.2.6 named input) -/

/-- **Level-stable grid-indifferent cover.**

A representative-index function `rep : X j → X k → ℕ × ℕ` such that for every
`{j,k}`-slice value `(x, v)` and **every** `t`-level `c`,
```
[x | v | c] ∼ [αⱼ (rep x v).1 | αₖ (rep x v).2 | c].
```
The level-stability — the indices depend only on `(x, v)`, not on `c` — is the
content that makes the R1.2 transport pure weak order.  Under a representation it
holds because the matching is the level-independent slice-utility equation
`V_j (αⱼ m) + V_k (αₖ n) = V_j x + V_k v`.  This is the §IV.2.6
Archimedean-density / solvability residual (bracket every value between
consecutive grid points; restricted solvability selects the indifferent grid
representative; base-independence makes it level-stable). -/
structure StableGridIndifferentCover (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) where
  /-- The representative grid indices for each `{j,k}`-slice value. -/
  rep   : X j → X k → ℕ × ℕ
  /-- Each value is indifferent to its grid representative, at every level. -/
  spec  : ∀ (x : X j) (v : X k) (c : X t),
    P.indiff (tri G.a j k t x v c)
             (tri G.a j k t (G.αj (rep x v).1) (G.αk (rep x v).2) c)

/-- **Soundness gate: the stable cover is necessary under a rep, modulo
grid-utility reach (PROVED).**

Under a representation, `[x|v|c] ∼ [αⱼ m|αₖ n|c]` iff `V_j (αⱼ m) + V_k (αₖ n) =
V_j x + V_k v` (the `V_t c` and background terms cancel — level-independently).
So a *choice* of matching grid indices for each `(x,v)` (the grid-utility reach,
the §IV.2.6 density content) yields a level-stable cover.  Confirms the stable
cover hides nothing false; the reach is the §IV.2.6 density residual.  This is a
`def` (it constructs the cover data).  Audit `[propext, Classical.choice,
Quot.sound]`. -/
noncomputable def stableGridIndifferentCover_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t)
    (rep : X j → X k → ℕ × ℕ)
    (hreach : ∀ (x : X j) (v : X k),
      R.V j (G.αj (rep x v).1) + R.V k (G.αk (rep x v).2) = R.V j x + R.V k v) :
    StableGridIndifferentCover P j k t G where
  rep  := rep
  spec := by
    intro x v c
    -- Score split of a `tri` profile (local copy of the standard engine; the
    -- private `score_tri_eq` of `OptionB_C1aGridThomsen` is not exported).
    have score_tri : ∀ (u : X j) (vv : X k) (cc : X t),
        (∑ i, R.V i (tri G.a j k t u vv cc i))
          = R.V j u + R.V k vv + R.V t cc
            + ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (G.a i) := by
      intro u vv cc
      have hkj : k ≠ j := Ne.symm hjk
      have htj : t ≠ j := Ne.symm hjt
      have htk : t ≠ k := Ne.symm hkt
      unfold tri
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
          ← Finset.add_sum_erase _ _ (show k ∈ Finset.univ.erase j from
            Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩),
          ← Finset.add_sum_erase _ _ (show t ∈ (Finset.univ.erase j).erase k from
            Finset.mem_erase.mpr ⟨htk, Finset.mem_erase.mpr ⟨htj, Finset.mem_univ t⟩⟩)]
      have hj : (Function.update (Function.update (Function.update G.a j u) k vv) t cc) j = u := by
        rw [Function.update_of_ne hjt, Function.update_of_ne hjk, Function.update_self]
      have hk : (Function.update (Function.update (Function.update G.a j u) k vv) t cc) k = vv := by
        rw [Function.update_of_ne hkt, Function.update_self]
      have ht : (Function.update (Function.update (Function.update G.a j u) k vv) t cc) t = cc := by
        rw [Function.update_self]
      rw [hj, hk, ht]
      have hrest : (∑ i ∈ ((Finset.univ.erase j).erase k).erase t,
            R.V i (Function.update (Function.update (Function.update G.a j u) k vv) t cc i))
          = ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (G.a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hit : i ≠ t := Finset.ne_of_mem_erase hi
        have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
        have hij : i ≠ j :=
          Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
        rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij]
      rw [hrest]; ring
    rw [indiff_iff_score R, score_tri, score_tri]
    have := hreach x v
    linarith

/-! ## §C.  The transport (theorem-backed from {grid-restricted residue + stable cover}) -/

/-- **R1.2 transport (PROVED): the full `TBlockDiagonalResidue` from the
grid-restricted residue + the level-stable grid cover.**

For arbitrary `x, z : X j`, `r, p : X k` and levels `w, c`:
1. replace `(x, r)` by its level-stable grid rep `(m, n) := cover.rep x r` and
   `(z, p)` by `(m', n') := cover.rep z p`, at level `w` — transporting `hw` to a
   pure grid comparison `[αⱼ m|αₖ n|w] ≽ [αⱼ m'|αₖ n'|w]`;
2. apply the grid-restricted residue to move that comparison to level `c`;
3. substitute back at level `c` using the **same** rep indices (level-stability!).

Pure weak order beyond the cover.  The `gridRestricted` hypothesis is exactly the
conclusion of `OptionB_C1aGridThomsen.gridTBlockDiagonalResidue_of_frontier`.
Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_of_gridRestricted_and_stableCover
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (cover : StableGridIndifferentCover P j k t G)
    (gridRestricted : ∀ (m n m' n' : ℕ) (w c : X t),
      P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  w)
                 (tri G.a j k t (G.αj m') (G.αk n') w) →
      P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  c)
                 (tri G.a j k t (G.αj m') (G.αk n') c))
    (x z : X j) (p r : X k) (w c : X t)
    (hw : P.weakPref (tri G.a j k t x r w) (tri G.a j k t z p w)) :
    P.weakPref (tri G.a j k t x r c) (tri G.a j k t z p c) := by
  -- Level-stable representatives (same indices at every level).
  set mn  := cover.rep x r with hmn
  set mn' := cover.rep z p with hmn'
  -- Step 1: transport `hw` to the grid comparison at level `w`.
  have hxr_w := cover.spec x r w
  have hzp_w := cover.spec z p w
  have hgrid_w : P.weakPref (tri G.a j k t (G.αj mn.1) (G.αk mn.2) w)
                            (tri G.a j k t (G.αj mn'.1) (G.αk mn'.2) w) :=
    weakPref_subst_right hzp_w (weakPref_subst_left hxr_w hw)
  -- Step 2: move the grid comparison to level `c`.
  have hgrid_c : P.weakPref (tri G.a j k t (G.αj mn.1) (G.αk mn.2) c)
                            (tri G.a j k t (G.αj mn'.1) (G.αk mn'.2) c) :=
    gridRestricted mn.1 mn.2 mn'.1 mn'.2 w c hgrid_w
  -- Step 3: substitute back at level `c` using the SAME rep indices.
  have hxr_c := cover.spec x r c
  have hzp_c := cover.spec z p c
  exact weakPref_subst_right (indiff_symm hzp_c)
    (weakPref_subst_left (indiff_symm hxr_c) hgrid_c)

/-! ## §D.  Full-residue capstone from the grid-Thomsen frontier + stable cover

Composing §C with the grid-Thomsen frontier capstone
(`gridTBlockDiagonalResidue_of_frontier`) gives the full `TBlockDiagonalResidue`
from the calibrated grid + the bundled forward frontier + the stable cover —
the complete R1.1+R1.2 grid route to the project's downstream residue. -/

/-- **R1.1+R1.2 capstone (PROVED): the full `TBlockDiagonalResidue` from the
calibrated grid + the grid-Thomsen frontier + the stable cover.**

Feeds the frontier capstone's grid-restricted residue into the §C transport.
This is the grid route's endpoint at full strength: the unrestricted
`TBlockDiagonalResidue P j k t` (the single Thomsen residue the R1.1 unified
capstone `crossPairCancellationData_of_a1_and_oneThomsenResidue` consumes at the
three permuted triples).  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockDiagonalResidue_of_frontier_and_stableCover
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (hfrontier : GridThomsenForwardFrontier P j k t G)
    (cover : StableGridIndifferentCover P j k t G)
    (a' : Profile X)
    (hbg : ∀ i, i ≠ j → i ≠ k → i ≠ t → a' i = G.a i) :
    ∀ (x z : X j) (p r : X k) (w c : X t),
      x ≠ z → r ≠ p →
      P.weakPref (tri a' j k t x r w) (tri a' j k t z p w) →
      P.weakPref (tri a' j k t x r c) (tri a' j k t z p c) := by
  -- The grid-restricted residue from the frontier capstone.
  have gridRestricted : ∀ (m n m' n' : ℕ) (w c : X t),
      P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  w)
                 (tri G.a j k t (G.αj m') (G.αk n') w) →
      P.weakPref (tri G.a j k t (G.αj m)  (G.αk n)  c)
                 (tri G.a j k t (G.αj m') (G.αk n') c) := by
    intro m n m' n' w c hw
    exact gridTBlockDiagonalResidue_of_frontier hjk hjt hkt hA1j hA1k hsolv htop G
      hfrontier m n m' n' w c hw
  -- Transport to the full residue over the grid's own background `G.a`.
  intro x z p r w c hxz hrp hw
  -- Reduce the arbitrary background `a'` to `G.a` by base-independence
  -- (`tri` overwrites `j,k,t`; backgrounds agreeing off `{j,k,t}` give equal `tri`).
  have hbridge : ∀ (u : X j) (vv : X k) (cc : X t),
      tri a' j k t u vv cc = tri G.a j k t u vv cc := by
    intro u vv cc
    exact tri_eq_of_agreeOff a' G.a j k t hbg u vv cc
  rw [hbridge x r w, hbridge z p w] at hw
  have hfull := tBlockDiagonalResidue_of_gridRestricted_and_stableCover G cover
    gridRestricted x z p r w c hw
  rw [hbridge x r c, hbridge z p c]
  exact hfull

/-! ## §E.  Full residue over all backgrounds, and the hexagon capstone

`tBlockDiagonalResidue_of_frontier_and_stableCover` produces the residue for
backgrounds agreeing with a *fixed* grid's base off `{j,k,t}`.  The full
`TBlockDiagonalResidue P j k t` quantifies over **all** backgrounds, so we package
a **background-indexed grid-route family**: one calibrated grid (+ frontier +
stable cover) per background, with the grid's base agreeing with that background
off `{j,k,t}`.  This is the honest object — each background class needs its own
measuring-stick grid — and it yields the full residue directly.

Feeding the full residue at the three coordinate role-assignments `(j,k,t)`,
`(j,t,k)`, `(t,k,j)` into the unified one-Thomsen hexagon capstone
(`doubleCancellation_of_a1_and_oneThomsenResidue`) closes R1.1 in the classical
additive-conjoint vocabulary: the hexagon `DoubleCancellation P j k`. -/

/-- **Background-indexed grid-route family.**

For every background `a`, a calibrated `{j,k,t}` grid whose base agrees with `a`
off `{j,k,t}`, together with the grid-Thomsen forward frontier and the level-stable
cover for that grid.  This is the per-background measuring-stick data the full
residue needs (the residue is base-independent off `{j,k,t}`, so one grid per
off-`{j,k,t}` class suffices). -/
structure TBlockGridRouteData (P : ProductPref X) (j k t : ι) where
  /-- The calibrated grid for each background. -/
  grid     : Profile X → CalibratedJKGrid P j k t
  /-- The grid's base agrees with the background off `{j,k,t}`. -/
  agree    : ∀ (a : Profile X) (i : ι), i ≠ j → i ≠ k → i ≠ t → a i = (grid a).a i
  /-- The grid-Thomsen forward frontier for each grid. -/
  frontier : ∀ a : Profile X, GridThomsenForwardFrontier P j k t (grid a)
  /-- The level-stable grid cover for each grid. -/
  cover    : ∀ a : Profile X, StableGridIndifferentCover P j k t (grid a)

/-- **R1.1+R1.2 full residue (PROVED): `TBlockDiagonalResidue P j k t` from the
background-indexed grid-route family.**

For each residue background `a`, instantiate the per-background grid (whose base
agrees with `a` off `{j,k,t}`) and apply
`tBlockDiagonalResidue_of_frontier_and_stableCover`.  This is the grid route's full
endpoint: the unrestricted Thomsen residue, over **every** background.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockDiagonalResidue_of_gridRouteData
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (data : TBlockGridRouteData P j k t) :
    TBlockDiagonalResidue P j k t := by
  intro a x z p r w c hxz hrp hw
  exact tBlockDiagonalResidue_of_frontier_and_stableCover hjk hjt hkt hA1j hA1k hsolv htop
    (data.grid a) (data.frontier a) (data.cover a) a (data.agree a)
    x z p r w c hxz hrp hw

/-- **R1.1 hexagon capstone via the grid route (PROVED): `DoubleCancellation P j k`.**

The grid route's classical-vocabulary endpoint.  Takes a grid-route family at each
of the three coordinate role-assignments `(j,k,t)`, `(j,t,k)`, `(t,k,j)` (the
single Thomsen residue at the three permutations, each produced full-strength by
`tBlockDiagonalResidue_of_gridRouteData`), plus A1 on all three coordinates and a
J2 transfer-level supplier (escape-grid-dischargeable, `OptionB_C1aJ2Escape.lean`),
and produces the classical hexagon `DoubleCancellation P j k` via
`doubleCancellation_of_a1_and_oneThomsenResidue`.

So the entire classical hexagon on `{j,k}` follows from the grid-Thomsen +
transport route, modulo the named §IV.5/§IV.2.6 inputs bundled in the three
grid-route families (forward frontiers + stable covers) and the J2 supplier — all
soundness-gated, all A1-non-derivable.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem doubleCancellation_of_gridRoute
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (data_jkt : TBlockGridRouteData P j k t)
    (data_jtk : TBlockGridRouteData P j t k)
    (data_tkj : TBlockGridRouteData P t k j)
    (hJ2 : ∀ (a : Profile X) (x y : X j) (r : X k),
      ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t))) :
    DoubleCancellation P j k :=
  doubleCancellation_of_a1_and_oneThomsenResidue hjk hjt hkt hA1j hA1k hA1t
    (tBlockDiagonalResidue_of_gridRouteData hjk hjt hkt hA1j hA1k hsolv htop data_jkt)
    -- `T-diag P j t k`: stick = k, differing = j,t.  Disequalities j≠t, j≠k, t≠k.
    (tBlockDiagonalResidue_of_gridRouteData hjt hjk (Ne.symm hkt) hA1j hA1t hsolv htop data_jtk)
    -- `T-diag P t k j`: stick = j, differing = t,k.  Disequalities t≠k, t≠j, k≠j.
    (tBlockDiagonalResidue_of_gridRouteData (Ne.symm hkt) (Ne.symm hjt) (Ne.symm hjk)
      hA1t hA1k hsolv htop data_tkj)
    hJ2

/-! ## §F.  Folding J2 into the §IV.2.6 escape grid

The hexagon capstone above still carries the J2 transfer-level supplier `hJ2` as a
bare hypothesis.  The project's `OptionB_C1aJ2Escape.lean` shows J2 is **not** an
independent residual: it is discharged from the §IV.2.6 Archimedean escape grid in
coordinate `t` (`j2Exists_of_archimedeanEscape`) — the same density content the
reach brackets and the stable cover already rest on.  We bundle that escape data
per J2 datum and produce `hJ2`, removing it as a standalone input. -/

/-- **Per-datum J2 escape data (the §IV.2.6 content discharging J2).**

For every J2 datum `(a, x, y, r)`, a strict Archimedean `t`-standard-sequence based
at the slice `[x|r|·]`, with the closed contour sets at the reference `[y|r|(a t)]`
and two-sided grid escape.  This is exactly the input
`j2Exists_of_archimedeanEscape` consumes; it is the §IV.2.6 escape-grid residual,
shared with the reach brackets and the stable cover. -/
structure J2EscapeData (P : ProductPref X) (j k t : ι)
    [∀ i, TopologicalSpace (X i)] where
  /-- The `t`-standard-sequence for each datum. -/
  seq    : Profile X → X j → X j → X k → ProductPref.StandardSequence P t
  /-- It is strict. -/
  strict : ∀ (a : Profile X) (x y : X j) (r : X k), (seq a x y r).IsStrict
  /-- The Archimedean axiom on `t`. -/
  arch   : ProductPref.Archimedean P t
  /-- The sequence's base realises the slice `[x|r|·]`. -/
  base   : ∀ (a : Profile X) (x y : X j) (r : X k) (w : X t),
    Function.update (seq a x y r).base t w = tri a j k t x r w
  /-- Upper contour at the reference is closed. -/
  upper  : ∀ (a : Profile X) (x y : X j) (r : X k),
    IsClosed {z : Profile X | P.weakPref z (tri a j k t y r (a t))}
  /-- Lower contour at the reference is closed. -/
  lower  : ∀ (a : Profile X) (x y : X j) (r : X k),
    IsClosed {z : Profile X | P.weakPref (tri a j k t y r (a t)) z}
  /-- The grid escapes the reference above. -/
  above  : ∀ (a : Profile X) (x y : X j) (r : X k), ∃ n : ℕ,
    ¬ P.weakPref (tri a j k t y r (a t))
                 (Function.update (seq a x y r).base t ((seq a x y r).α n))
  /-- The grid escapes the reference below. -/
  below  : ∀ (a : Profile X) (x y : X j) (r : X k), ∃ n : ℕ,
    ¬ P.weakPref (Function.update (seq a x y r).base t ((seq a x y r).α n))
                 (tri a j k t y r (a t))

/-- **J2 supplier from the escape data (PROVED).**

Each datum's transfer level exists by `j2Exists_of_archimedeanEscape`, fed from the
bundled escape data.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem j2Supplier_of_escapeData
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    [ConnectedSpace (X t)]
    (esc : J2EscapeData P j k t) :
    ∀ (a : Profile X) (x y : X j) (r : X k),
      ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t)) := by
  intro a x y r
  exact j2Exists_of_archimedeanEscape a x y r (esc.seq a x y r) (esc.strict a x y r)
    esc.arch (esc.base a x y r) (esc.upper a x y r) (esc.lower a x y r)
    (esc.above a x y r) (esc.below a x y r)

/-- **R1.1 hexagon capstone via the grid route, with J2 escape-discharged
(PROVED): `DoubleCancellation P j k`.**

The fully-named-input form of the grid-route hexagon capstone: J2 is no longer a
bare hypothesis but is discharged from the §IV.2.6 escape grid `J2EscapeData`.  So
the entire classical hexagon on `{j,k}` follows from the grid-Thomsen + transport
route, modulo exactly the named §IV.5/§IV.2.6 inputs — the three grid-route
families (forward frontiers + stable covers) and the J2 escape grid — all
soundness-gated and A1-non-derivable, with the topology bundle discharging the
continuum content.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem doubleCancellation_of_gridRoute_escapeJ2
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    [ConnectedSpace (X t)]
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (data_jkt : TBlockGridRouteData P j k t)
    (data_jtk : TBlockGridRouteData P j t k)
    (data_tkj : TBlockGridRouteData P t k j)
    (esc : J2EscapeData P j k t) :
    DoubleCancellation P j k :=
  doubleCancellation_of_gridRoute hjk hjt hkt hA1j hA1k hA1t hsolv htop
    data_jkt data_jtk data_tkj (j2Supplier_of_escapeData esc)

/-! ## §G.  Unified single-bundle interface

The hexagon capstone consumes **three** grid-route families — at the three
coordinate role-assignments `(j,k,t)`, `(j,t,k)`, `(t,k,j)` — plus a J2 escape
grid.  Those three families are **not** mathematically collapsible to one: by the
permutation equivalence (`OptionB_C1aDiagonalEquivalence.lean`) the three
`TBlockDiagonalResidue` facts are Thomsen cancellation for the *three distinct*
coordinate pairs (`{j,k}` shifted by `t`, `{j,t}` shifted by `k`, `{t,k}` shifted
by `j`); each must independently hold, so each needs its own measuring-stick grid.
Collapsing them would be **unsound** and is not attempted.

What *is* a sound reduction is the **input interface**: bundle the three families
and the J2 escape grid into a single object `UnifiedGridRouteData`, so the hexagon
capstone takes **one** input instead of four.  This is purely organizational (no
mathematical content is merged), but it is the honest "one bundle" the downstream
R1.1 consumers want — and it makes the grid route's complete frontier a single
named structure. -/

/-- **Unified grid-route data: the grid route's entire frontier in one bundle.**

Packages the three per-triple grid-route families (the genuinely-distinct Thomsen
content at `(j,k,t)`, `(j,t,k)`, `(t,k,j)`) together with the J2 escape grid.  This
is the single object the grid-route hexagon capstone consumes.  Its components are
*not* inter-derivable (the three Thomsen facts are distinct cross-pair cancellation
conditions); the bundle is an interface, not a mathematical merge. -/
structure UnifiedGridRouteData (P : ProductPref X) (j k t : ι)
    [∀ i, TopologicalSpace (X i)] where
  /-- Grid-route family for `(j,k,t)` — Thomsen for `{j,k}` shifted by `t`. -/
  route_jkt : TBlockGridRouteData P j k t
  /-- Grid-route family for `(j,t,k)` — Thomsen for `{j,t}` shifted by `k`. -/
  route_jtk : TBlockGridRouteData P j t k
  /-- Grid-route family for `(t,k,j)` — Thomsen for `{t,k}` shifted by `j`. -/
  route_tkj : TBlockGridRouteData P t k j
  /-- The J2 escape grid (discharges the transfer-level supplier). -/
  j2esc     : J2EscapeData P j k t

/-- **R1.1 hexagon capstone from the single unified bundle (PROVED).**

The cleanest grid-route endpoint: `DoubleCancellation P j k` from A1 + the
structural axioms + the topology bundle + the **single** `UnifiedGridRouteData`.
Pure delegation to `doubleCancellation_of_gridRoute_escapeJ2` with the bundle's
components.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem doubleCancellation_of_unifiedGridRoute
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    [ConnectedSpace (X t)]
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (data : UnifiedGridRouteData P j k t) :
    DoubleCancellation P j k :=
  doubleCancellation_of_gridRoute_escapeJ2 hjk hjt hkt hA1j hA1k hA1t hsolv htop
    data.route_jkt data.route_jtk data.route_tkj data.j2esc

/-! ## §H.  Discharging the `OffCalJBracket` reach from the §IV.2.6 escape grid

`OffCalJBracket` asks, per cell `(m, n, c)`, for two `t`-levels bracketing the
`j`-step reference `[αⱼ(m+1) | αₖ n | c]` from the slice `[αⱼ m | αₖ n | ·]`:
`cHi` over-compensating and `cLo` under-compensating.  Both are single-coordinate-
`t` comparisons over the *same* slice base `[αⱼ m | αₖ n | ·]`.

This bracket is **not** the cross-pair Thomsen content — it is the §IV.2.6
**Archimedean reach**: a strict Archimedean `t`-standard-sequence based at the
slice escapes any reference on both sides (`archimedean_reach_above`/`below`, pure
order theory — no topology, no IVT, no A1).  So `OffCalJBracket` is dischargeable
from bare axioms + the escape grid, exactly like the J2 supplier.  We name the
per-cell escape grid `OffCalJEscapeGrid` and discharge the bracket from it. -/

/-- **Per-cell `j`-bracket escape grid (the §IV.2.6 Archimedean reach data).**

For each off-cal cell `(m, n, c)` with `c ∉ {rt, st}`, a strict Archimedean
`t`-standard-sequence whose base realises the slice `[αⱼ m | αₖ n | ·]` and whose
grid escapes the reference `[αⱼ (m+1) | αₖ n | c]` on **both** sides.  This is the
genuine §IV.2.6 escape content — pure order theory discharges the bracket from it
(no topology, no IVT). -/
structure OffCalJEscapeGrid (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) where
  /-- The `t`-standard-sequence for each cell. -/
  seq    : ℕ → ℕ → X t → ProductPref.StandardSequence P t
  /-- It is strict. -/
  strict : ∀ (m n : ℕ) (c : X t), (seq m n c).IsStrict
  /-- The Archimedean axiom on `t`. -/
  arch   : ProductPref.Archimedean P t
  /-- The sequence's base realises the slice `[αⱼ m | αₖ n | ·]`. -/
  base   : ∀ (m n : ℕ) (c : X t) (w : X t),
    Function.update (seq m n c).base t w = tri G.a j k t (G.αj m) (G.αk n) w
  /-- The grid escapes the reference above (some point not weakly below it). -/
  above  : ∀ (m n : ℕ) (c : X t), ∃ i : ℕ,
    ¬ P.weakPref (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)
                 (Function.update (seq m n c).base t ((seq m n c).α i))
  /-- The grid escapes the reference below (some point not weakly above it). -/
  below  : ∀ (m n : ℕ) (c : X t), ∃ i : ℕ,
    ¬ P.weakPref (Function.update (seq m n c).base t ((seq m n c).α i))
                 (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)

/-- **`OffCalJBracket` from the escape grid (PROVED — discharges a named input).**

The `cHi`/`cLo` witnesses are produced by `archimedean_reach_above`/`below` applied
to the slice sequence, with the reference `[αⱼ (m+1) | αₖ n | c]`; the sequence's
`base` field rewrites the reach witnesses into the `tri`-slice shape.  **Pure order
theory** — no topology, no IVT, no A1.  This discharges the §IV.2.6 reach bracket
from bare axioms (the Archimedean axiom + the escape grid), exactly the move that
discharged J2.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem offCalJBracket_of_escapeGrid
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (esc : OffCalJEscapeGrid P j k t G) :
    OffCalJBracket P j k t G := by
  intro m n c hrt hst
  -- Upper reach: a grid point ≽ reference, rewritten to the slice shape.
  obtain ⟨cHi, hHi⟩ :=
    WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_reach_above
      P (esc.seq m n c) (esc.strict m n c) esc.arch
      (tri G.a j k t (G.αj (m + 1)) (G.αk n) c) (esc.above m n c)
  -- Lower reach: reference ≽ a grid point, rewritten to the slice shape.
  obtain ⟨cLo, hLo⟩ :=
    WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_reach_below
      P (esc.seq m n c) (esc.strict m n c) esc.arch
      (tri G.a j k t (G.αj (m + 1)) (G.αk n) c) (esc.below m n c)
  refine ⟨cHi, cLo, ?_, ?_⟩
  · -- hHi : update (seq.base) t cHi ≽ reference; rewrite base to the slice.
    rw [esc.base m n c cHi] at hHi; exact hHi
  · -- hLo : reference ≽ update (seq.base) t cLo; rewrite base to the slice.
    rw [esc.base m n c cLo] at hLo; exact hLo

/-- **Forward frontier with the bracket discharged from the escape grid (PROVED).**

Builds `GridThomsenForwardFrontier` taking the §IV.2.6 reach **bracket** from the
escape grid (`offCalJBracket_of_escapeGrid`) rather than as an assumed field.  So
the frontier's three components reduce to: the off-axis forward data `fwd`, the
escape grid `esc` (discharging `bracket`), and the matching residual `match'`.
This shrinks the assumed bracket to the canonical §IV.2.6 escape content — the same
family as the J2 escape grid.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridThomsenForwardFrontier_of_escapeGrid
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (fwd : CalibrationOffAxisForwardData P j k t G)
    (esc : OffCalJEscapeGrid P j k t G)
    (hmatch : OffCalCompensationMatch P j k t G) :
    GridThomsenForwardFrontier P j k t G where
  fwd     := fwd
  bracket := offCalJBracket_of_escapeGrid G esc
  match'  := hmatch

/-! ## §I.  End-to-end route data with the bracket escape-discharged

`TBlockGridRouteData.frontier` carries a *pre-built* `GridThomsenForwardFrontier`
(bracket field included).  With §H, the bracket need not be assumed: it is derived
from a per-background escape grid.  `TBlockGridRouteDataEsc` carries the escape
grid instead of the assembled bracket, and `tBlockDiagonalResidue_of_gridRouteDataEsc`
produces the full residue from it — so the reach bracket is discharged
end-to-end (it never appears as an assumed input).  The remaining assumed content
per background is exactly: the off-axis forward data, the escape grid, the matching
residual, and the stable cover. -/

/-- **Escape-grid route data (the bracket derived, not assumed).**

Like `TBlockGridRouteData`, but per background carries the §IV.2.6 escape grid
`OffCalJEscapeGrid` (which *derives* the reach bracket via §H) plus the off-axis
forward data and the matching residual — rather than a pre-assembled
`GridThomsenForwardFrontier`. -/
structure TBlockGridRouteDataEsc (P : ProductPref X) (j k t : ι) where
  /-- The calibrated grid for each background. -/
  grid    : Profile X → CalibratedJKGrid P j k t
  /-- The grid's base agrees with the background off `{j,k,t}`. -/
  agree   : ∀ (a : Profile X) (i : ι), i ≠ j → i ≠ k → i ≠ t → a i = (grid a).a i
  /-- Off-axis calibration forward data (reach brackets + matching residuals). -/
  fwd     : ∀ a : Profile X, CalibrationOffAxisForwardData P j k t (grid a)
  /-- The §IV.2.6 escape grid (derives the level-move reach bracket). -/
  esc     : ∀ a : Profile X, OffCalJEscapeGrid P j k t (grid a)
  /-- The level-move equal-spacing matching residual. -/
  match'  : ∀ a : Profile X, OffCalCompensationMatch P j k t (grid a)
  /-- The level-stable grid cover. -/
  cover   : ∀ a : Profile X, StableGridIndifferentCover P j k t (grid a)

/-- **Escape-grid route data ⟹ the ordinary route data (PROVED).**

Builds `TBlockGridRouteData` from `TBlockGridRouteDataEsc` by assembling each
background's forward frontier via `gridThomsenForwardFrontier_of_escapeGrid` (the
bracket derived from the escape grid).  So the escape-grid form is at least as
strong as the assumed-bracket form.  (A `def`: it constructs route data.)  Audit
`[propext, Quot.sound]`. -/
def tBlockGridRouteData_of_esc
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (data : TBlockGridRouteDataEsc P j k t) :
    TBlockGridRouteData P j k t where
  grid     := data.grid
  agree    := data.agree
  frontier := fun a =>
    gridThomsenForwardFrontier_of_escapeGrid (data.grid a) (data.fwd a) (data.esc a) (data.match' a)
  cover    := data.cover

/-- **Full residue from the escape-grid route data (PROVED, bracket discharged
end-to-end).**

Composes `tBlockGridRouteData_of_esc` with `tBlockDiagonalResidue_of_gridRouteData`.
The reach bracket never appears as an assumed input — it is derived from the escape
grid throughout.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockDiagonalResidue_of_gridRouteDataEsc
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (data : TBlockGridRouteDataEsc P j k t) :
    TBlockDiagonalResidue P j k t :=
  tBlockDiagonalResidue_of_gridRouteData hjk hjt hkt hA1j hA1k hsolv htop
    (tBlockGridRouteData_of_esc data)

/-- **Unified escape-grid bundle (the grid route's frontier, bracket + J2 both
escape-discharged).**

Packages the three per-triple escape-grid route families + the J2 escape grid.
Compared to `UnifiedGridRouteData`, the level-move reach brackets are no longer
assumed (each `route_*` carries an escape grid that derives its bracket), so the
only reach content is the canonical §IV.2.6 escape grids. -/
structure UnifiedGridRouteDataEsc (P : ProductPref X) (j k t : ι)
    [∀ i, TopologicalSpace (X i)] where
  /-- Escape-grid route family for `(j,k,t)`. -/
  route_jkt : TBlockGridRouteDataEsc P j k t
  /-- Escape-grid route family for `(j,t,k)`. -/
  route_jtk : TBlockGridRouteDataEsc P j t k
  /-- Escape-grid route family for `(t,k,j)`. -/
  route_tkj : TBlockGridRouteDataEsc P t k j
  /-- The J2 escape grid. -/
  j2esc     : J2EscapeData P j k t

/-- **R1.1 hexagon from the unified escape-grid bundle (PROVED): the grid route
with ALL reach content escape-discharged.**

`DoubleCancellation P j k` from the single `UnifiedGridRouteDataEsc`: the three
Thomsen residues are produced via `tBlockDiagonalResidue_of_gridRouteDataEsc` (reach
brackets derived from escape grids) and J2 via `j2Supplier_of_escapeData`.  So the
hexagon rests on exactly: the three off-axis forward data + matching residuals +
stable covers (the genuine cross-pair + exact-match content) and the §IV.2.6 escape
grids — with **every** Archimedean-reach obligation discharged by pure order theory.
Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem doubleCancellation_of_unifiedGridRouteEsc
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    [ConnectedSpace (X t)]
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (hsolv : RestrictedSolvability P)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (data : UnifiedGridRouteDataEsc P j k t) :
    DoubleCancellation P j k :=
  doubleCancellation_of_a1_and_oneThomsenResidue hjk hjt hkt hA1j hA1k hA1t
    (tBlockDiagonalResidue_of_gridRouteDataEsc hjk hjt hkt hA1j hA1k hsolv htop data.route_jkt)
    (tBlockDiagonalResidue_of_gridRouteDataEsc hjt hjk (Ne.symm hkt) hA1j hA1t hsolv htop data.route_jtk)
    (tBlockDiagonalResidue_of_gridRouteDataEsc (Ne.symm hkt) (Ne.symm hjt) (Ne.symm hjk)
      hA1t hA1k hsolv htop data.route_tkj)
    (j2Supplier_of_escapeData data.j2esc)

/-! ## §J.  Scoping: does solvability + escape grid close the exact-match cover?

**Question.**  `StableGridIndifferentCover` was flagged (§I) as the one named input
**not** discharged by the escape-grid reach.  Can the project's slice-indifference
selector (`sliceIndiffSelector_of_restrictedSolvability`) + an escape bracket close
it?  This section answers **NO**, with the precise obstruction made
machine-checked: solvability reaches a strictly **weaker** "dense interpolant"
cover, which does not upgrade to the grid-point, level-stable cover the transport
needs.

**What solvability genuinely reaches (the positive partial).**  Given a `j`-axis
bracket of the reference `[x|r|ℓ]` over the slice `[·|αₖ 0|ℓ]`, restricted
solvability yields an **interpolated** `j`-value `x'` with `[x'|αₖ 0|ℓ] ∼ [x|r|ℓ]`.
This is `DenseSliceInterpolantCover` below — collapse to an *axis interpolant*, at a
*single* level.

**Why it does NOT close `StableGridIndifferentCover` (two independent walls).**
1. **Interpolant ≠ grid point.**  `x'` is an arbitrary solvability value in `X j`,
   ranging over a continuum; the grid points `αⱼ m` are countable.  No reach lemma
   turns `x'` into a grid index.
2. **Single-level ≠ level-stable.**  The collapse holds only at the bracket level
   `ℓ`.  Lifting `[x'|αₖ 0|ℓ] ∼ [x|r|ℓ]` to all levels transports a `{j,k}`-**two-
   coordinate** indifference (`x' ≠ x` and `αₖ 0 ≠ r`) across `t` — which is exactly
   `TBlockDiagonalResidue` content.  **Circular** (it is the very residue the cover
   feeds).

So the exact-match, level-stable, grid-point cover genuinely needs a
**continuity+density closure** (the residue holds on the dense grid; both contour
sides continuous ⟹ it extends to the continuum) — the real §IV.2.6 construction,
not a pure-solvability reach. -/

/-- **Dense slice-interpolant cover (what solvability reaches — weaker than the
exact-match cover).**

For every `{j,k}`-slice value `(x, v)` at a *single* level `c`, an **interpolated**
`j`-value `x'` (not necessarily a grid point) with `[x|v|c] ∼ [x'|αₖ 0|c]`.  This
is the honest output of solvability + an escape bracket: it collapses the
`k`-coordinate onto the axis at one level, but lands on an arbitrary `X j` value,
not a grid index, and is not level-stable. -/
def DenseSliceInterpolantCover (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ (x : X j) (v : X k) (c : X t),
    ∃ x' : X j, P.indiff (tri G.a j k t x v c)
                         (tri G.a j k t x' (G.αk 0) c)

/-- **The dense interpolant cover from restricted solvability + a `j`-axis bracket
(PROVED — the positive partial).**

Given, per `(x, v, c)`, a `j`-axis bracket of the reference `[x|v|c]` over the
slice `[·|αₖ 0|c]` (`vHi` over, `vLo` under — the escape content), restricted
solvability selects the interpolant `x'`.  The `tri_eq_update_j` rewrite recasts
the `tri` profiles as single coordinate-`j` updates so `sliceIndiffSelector`
applies.  Audit `[propext, Classical.choice, Quot.sound]`.

This is **strictly weaker** than `StableGridIndifferentCover` (interpolant, not
grid point; single level, not level-stable) — see the §J discussion. -/
theorem denseSliceInterpolantCover_of_solvability_and_bracket
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t)
    (hsolv : RestrictedSolvability P)
    (G : CalibratedJKGrid P j k t)
    (hbr : ∀ (x : X j) (v : X k) (c : X t), ∃ vHi vLo : X j,
      P.weakPref (tri G.a j k t vHi (G.αk 0) c) (tri G.a j k t x v c) ∧
      P.weakPref (tri G.a j k t x v c) (tri G.a j k t vLo (G.αk 0) c)) :
    DenseSliceInterpolantCover P j k t G := by
  intro x v c
  obtain ⟨vHi, vLo, hHi, hLo⟩ := hbr x v c
  -- Recast the slice `[·|αₖ 0|c]` as a single coordinate-`j` update over the packed
  -- background `update (update a k (αₖ 0)) t c`.
  set base : Profile X := Function.update (Function.update G.a k (G.αk 0)) t c with hbase
  have hslice : ∀ u : X j, tri G.a j k t u (G.αk 0) c = Function.update base j u := by
    intro u; rw [hbase, tri_eq_update_j G.a hjk hjt u (G.αk 0) c]
  rw [hslice vHi] at hHi
  rw [hslice vLo] at hLo
  obtain ⟨x', hx'⟩ :=
    sliceIndiffSelector_of_restrictedSolvability hsolv base (tri G.a j k t x v c) j vHi vLo hHi hLo
  refine ⟨x', ?_⟩
  rw [← hslice x'] at hx'
  exact indiff_symm hx'

/-- **The obstruction, machine-checked: an exact-match cover would give the
level-move diagonal step (hence is circular).**

If the exact-match, level-stable cover held, then — combined with the grid's own
axis indifferences — the `{j,k}` two-coordinate indifference at one level would
transport to all levels, i.e. it yields `GridDiagonalStepOffCal`-style content.
Concretely: the cover at two levels for the *same* `(x,v)` lands on the *same* grid
indices (level-stability), so the two-coordinate indifference `[x|v|ℓ] ∼ [grid|ℓ]`
transports `ℓ → c` — the `TBlockDiagonalResidue` content.  This records *why* the
exact-match cover is not solvability-reachable: it already encodes the cross-pair
transport.  (Stated as the precise implication; the cover ⟹ a diagonal-step-shaped
fact.)  Audit `[propext, Quot.sound]`. -/
theorem stableCover_gives_levelTransport
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (G : CalibratedJKGrid P j k t)
    (cover : StableGridIndifferentCover P j k t G)
    (x : X j) (v : X k) (w c : X t) :
    P.indiff (tri G.a j k t x v w)
             (tri G.a j k t (G.αj (cover.rep x v).1) (G.αk (cover.rep x v).2) w) ∧
    P.indiff (tri G.a j k t x v c)
             (tri G.a j k t (G.αj (cover.rep x v).1) (G.αk (cover.rep x v).2) c) :=
  ⟨cover.spec x v w, cover.spec x v c⟩

/-! ## §K.  Scoping the continuity+density closure for the exact-match cover

§J proved the exact-match cover is not solvability-reachable and needs the
continuity+density §IV.2.6 closure.  This section scopes that closure as a
concrete, **compiling** target: it isolates the order-theory + topology skeleton
(theorem-backed) and names the genuine analytic input precisely.

**The closure shape.**  Fix a level `c` and the reference comparison
`[x|r|c] ≽ [z|p|c]` we want to transport.  In the grid-Thomsen route the
grid-restricted residue already gives the comparison's transport on **grid
points**.  The exact-match cover would extend "the `{j,k}`-comparison is
`t`-level-invariant" from grid points to **all** `(x, v)` by:
* the comparison-at-a-fixed-level, viewed as a function of the `{j,k}`-slice value
  through the two **closed** contour sets (preference continuity), and
* **density** of the grid image `{(αⱼ m, αₖ n)}` in `X j × X k`.
Mathlib's `Continuous.ext_on`-style argument then forces agreement everywhere from
agreement on the dense grid — exactly the pattern of
`Certificates.sharedPivotGrid_global_agreement` (which closes the M5 cardinal
agreement the same way).

We make the **two-coordinate `{j,k}`-slice map** and its continuity explicit
(theorem-backed), then name the genuine input: a **dense grid image** in the
`{j,k}`-slice.  The full closure is then a `Continuous.ext_on` instance over that
dense set — the honest §IV.2.6 analytic content, isolated here. -/

/-- **Two-coordinate `{j,k}`-slice map** at fixed level `c` over background `a`:
`(u, v) ↦ tri a j k t u v c`.  Continuous in the product topology. -/
def jkSliceMap [∀ i, TopologicalSpace (X i)] (a : Profile X) (j k t : ι) (c : X t) :
    X j × X k → Profile X :=
  fun uv => tri a j k t uv.1 uv.2 c

/-- **The `{j,k}`-slice map is continuous (PROVED).**

`tri a j k t u v c i` is, for each coordinate `i`, either `u`, `v`, the constant
`c`, or the constant `a i` — each continuous in `(u, v)`.  Audit `[propext]`. -/
theorem continuous_jkSliceMap [∀ i, TopologicalSpace (X i)]
    (a : Profile X) (j k t : ι) (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) (c : X t) :
    Continuous (jkSliceMap a j k t c) := by
  refine continuous_pi (fun i => ?_)
  -- The `i`-th coordinate of `tri a j k t u v c` as a function of `(u, v)`.
  unfold jkSliceMap tri
  by_cases hit : i = t
  · -- i = t: value is the constant `c`.
    subst hit
    simp only [Function.update_self]
    exact continuous_const
  · -- i ≠ t: drop the `t`-update.
    simp only [Function.update_of_ne hit]
    by_cases hik : i = k
    · -- i = k: value is `v` (second projection).
      subst hik
      simp only [Function.update_self]
      exact continuous_snd
    · -- i ≠ k: drop the `k`-update.
      simp only [Function.update_of_ne hik]
      by_cases hij : i = j
      · -- i = j: value is `u` (first projection).
        subst hij
        simp only [Function.update_self]
        exact continuous_fst
      · -- i ∉ {j,k,t}: constant `a i`.
        simp only [Function.update_of_ne hij]
        exact continuous_const

/-- **Dense grid image (the named §IV.2.6 density input).**

The grid image `{(αⱼ m, αₖ n) : m n : ℕ}` is dense in `X j × X k`.  This is the
genuine §IV.2.6 Archimedean-density content (the strict grids' images are dense);
it is the analytic input the continuity closure consumes, in place of the
solvability-unreachable exact-match cover (§J). -/
def GridImageDense [∀ i, TopologicalSpace (X i)] {j k t : ι}
    (G : CalibratedJKGrid P j k t) : Prop :=
  DenseRange (fun mn : ℕ × ℕ => (G.αj mn.1, G.αk mn.2))

/-- **Closure engine (PROVED): an indifference extends from the dense grid image
to the continuum.**

Fix a level `c`.  Suppose two `{j,k}`-slice profiles, parameterised by `(u, v)`
through `jkSliceMap`, are compared by a relation whose graph is **closed** (the
preference contour sets, from preference continuity), and the relation holds on the
**dense** grid image.  Then it holds for **all** `(u, v)`.

Concretely for indifference to a fixed profile `b`: `{uv | [u|v|c] ∼ b}` is the
preimage of the closed indifference set `{z | z ∼ b}` under the continuous
`jkSliceMap`, hence closed; if it contains the dense grid image it is all of
`X j × X k`.  This is the `Continuous.ext_on`-style density extension — the honest
§IV.2.6 closure, here reduced to {closed indiff set + dense grid image}.  Audit
`[propext]`. -/
theorem indiff_extends_of_denseGridImage [∀ i, TopologicalSpace (X i)]
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) (c : X t) (b : Profile X)
    (hdense : GridImageDense G)
    (hclosed : IsClosed {z : Profile X | P.indiff z b})
    (hgrid : ∀ m n : ℕ, P.indiff (tri G.a j k t (G.αj m) (G.αk n) c) b)
    (u : X j) (v : X k) :
    P.indiff (tri G.a j k t u v c) b := by
  -- The set of slice parameters whose profile is indifferent to `b`.
  set S : Set (X j × X k) := {uv | P.indiff (tri G.a j k t uv.1 uv.2 c) b} with hS
  -- S is closed: preimage of the closed indiff set under the continuous slice map.
  have hScl : IsClosed S := by
    have : S = (jkSliceMap G.a j k t c) ⁻¹' {z : Profile X | P.indiff z b} := by
      ext uv; simp [hS, jkSliceMap]
    rw [this]
    exact hclosed.preimage (continuous_jkSliceMap G.a j k t hjk hjt hkt c)
  -- S contains the grid image (the grid hypothesis).
  have hsub : Set.range (fun mn : ℕ × ℕ => (G.αj mn.1, G.αk mn.2)) ⊆ S := by
    rintro _ ⟨mn, rfl⟩
    exact hgrid mn.1 mn.2
  -- A closed set containing a dense set is the whole space.
  have huniv : S = Set.univ :=
    Set.eq_univ_of_univ_subset
      (hdense.closure_eq ▸ (hScl.closure_eq ▸ closure_mono hsub))
  have : (u, v) ∈ S := huniv ▸ Set.mem_univ _
  exact this

/-! ## §L.  Scoping: does the dense-range infrastructure discharge `GridImageDense`?

**Question.**  The project carries `CoordinateDenseRangeCertificate R := ∀ i,
DenseRange (R.V i)` (`M2Frontier.lean`) and a refined-mesh-family chain.  Does that
discharge the §K input `GridImageDense G` (the *single* calibrated grid's image
dense in `X j × X k`)?

**Verdict: NO — and they are about genuinely different objects.**
`GridImageDense G` requires the **single** grid `{(αⱼ m, αₖ n)}` to be dense.  But
the grid sequences are *standard sequences*: under any representation `spaced_j`
forces `V_j (αⱼ (n+1)) = V_j (αⱼ n) + δ` — an **arithmetic progression**, whose
image is **not dense** (the project's machine-checked no-go
`M2Frontier.additiveRealBool_strictStandardSequence_not_dense` /
`…selectedRefinedDenseGrid_target_is_unsound`).  `CoordinateDenseRangeCertificate`
is instead about the **full utility image** `range (R.V i)` being dense — a property
of the coordinate space, realized by a *refinement family / mesh* of sequences with
steps of both signs, **not** by one calibrated grid.  So the infrastructure does
not discharge `GridImageDense`; the genuine input must be reformulated over the
refinement mesh family (§IV.2.6), not the single measuring-stick grid.

We make the obstruction machine-checked: `GridImageDense G` forces the single axis
sequence `G.αj` to have dense range (pure topology, below), which the no-go refutes.
So §K's closure engine is sound but its `GridImageDense` hypothesis is **too strong
for the single grid** — the closure must run over a mesh family. -/

/-- **`GridImageDense` forces single-axis density (PROVED — the obstruction).**

The grid image dense in `X j × X k` projects (via the continuous, surjective first
projection) to the `j`-axis: `DenseRange G.αj`.  Pure topology.  Combined with the
arithmetic-progression no-go (a calibrated grid's axis is a standard sequence, not
dense under a rep), this shows `GridImageDense` is **unsatisfiable for the single
calibrated grid** — confirming the dense-range infrastructure (a refinement-family
notion) does not discharge it.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem gridImageDense_imp_axisDenseRange [∀ i, TopologicalSpace (X i)]
    {j k t : ι} (G : CalibratedJKGrid P j k t)
    (hdense : GridImageDense G) :
    DenseRange G.αj := by
  -- `GridImageDense G = DenseRange (fun mn => (αⱼ mn.1, αₖ mn.2))`.
  -- Project to the first coordinate via the continuous surjection `Prod.fst`.
  have hfst_surj : Function.Surjective (Prod.fst : X j × X k → X j) := by
    intro x; exact ⟨(x, G.αk 0), rfl⟩
  have hcomp : DenseRange
      (Prod.fst ∘ (fun mn : ℕ × ℕ => (G.αj mn.1, G.αk mn.2))) :=
    (hfst_surj.denseRange).comp hdense continuous_fst
  -- `Prod.fst ∘ (fun mn => (αⱼ mn.1, αₖ mn.2)) = fun mn => αⱼ mn.1`, range = range αⱼ.
  have hrange : Set.range (Prod.fst ∘ (fun mn : ℕ × ℕ => (G.αj mn.1, G.αk mn.2)))
      = Set.range G.αj := by
    ext x
    constructor
    · rintro ⟨mn, rfl⟩; exact ⟨mn.1, rfl⟩
    · rintro ⟨m, rfl⟩; exact ⟨(m, 0), rfl⟩
  -- `DenseRange` is density of the range; rewrite the range.
  unfold DenseRange at hcomp ⊢
  rwa [hrange] at hcomp

/-! ## §M.  The generalized closure engine over an abstract dense `{j,k}`-mesh

§L proved the §K engine's `GridImageDense` hypothesis is unsatisfiable for the
single calibrated grid (its axes are arithmetic progressions, not dense).  The fix
is to **generalize the engine** to consume *any* dense family of `{j,k}`-slice
points — in particular a §IV.2.6 **refinement mesh** (`σⱼ : I → X j`, `σₖ : I → X k`
indexed by an arbitrary type `I`, whose image is dense), not just the measuring-
stick grid.  This is the honest, reusable form: the closure is pure topology and
works for whatever dense mesh the §IV.2.6 construction supplies.

The engine below is the §K engine with the grid `(αⱼ, αₖ)` replaced by an abstract
dense mesh `(meshJ, meshK) : I → X j × X k`. -/

/-- **Dense `{j,k}`-mesh: an abstract dense family of slice points.**

A pair of families `meshJ : I → X j`, `meshK : I → X k` (indexed by any `I`) whose
combined image `{(meshJ i, meshK i)}` is dense in `X j × X k`.  This is the general
form of the §IV.2.6 density input — a refinement mesh, not a single arithmetic-
progression grid (which §L proved cannot be dense). -/
def DenseJKMesh [∀ i, TopologicalSpace (X i)] (j k : ι)
    {I : Type*} (meshJ : I → X j) (meshK : I → X k) : Prop :=
  DenseRange (fun i : I => (meshJ i, meshK i))

/-- **Generalized closure engine (PROVED): indifference extends from any dense
`{j,k}`-mesh to the continuum.**

The §K engine with the single grid replaced by an arbitrary dense mesh
`(meshJ, meshK) : I → X j × X k`.  If the comparison `[·|·|c] ∼ b` holds on the
mesh and the indifference set is closed (preference continuity), it holds for all
`(u, v)`.  Pure topology — `IsClosed.preimage` + `DenseRange.closure_eq` +
`closure_mono`.  This is the reusable form the §IV.2.6 refinement-mesh construction
feeds (a single arithmetic-progression grid cannot be dense, §L; a refinement mesh
can).  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem indiff_extends_of_denseJKMesh [∀ i, TopologicalSpace (X i)]
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (c : X t) (b : Profile X)
    {I : Type*} (meshJ : I → X j) (meshK : I → X k)
    (hdense : DenseJKMesh j k meshJ meshK)
    (hclosed : IsClosed {z : Profile X | P.indiff z b})
    (hmesh : ∀ i : I, P.indiff (tri a j k t (meshJ i) (meshK i) c) b)
    (u : X j) (v : X k) :
    P.indiff (tri a j k t u v c) b := by
  set S : Set (X j × X k) := {uv | P.indiff (tri a j k t uv.1 uv.2 c) b} with hS
  have hScl : IsClosed S := by
    have : S = (jkSliceMap a j k t c) ⁻¹' {z : Profile X | P.indiff z b} := by
      ext uv; simp [hS, jkSliceMap]
    rw [this]
    exact hclosed.preimage (continuous_jkSliceMap a j k t hjk hjt hkt c)
  have hsub : Set.range (fun i : I => (meshJ i, meshK i)) ⊆ S := by
    rintro _ ⟨i, rfl⟩
    exact hmesh i
  have huniv : S = Set.univ :=
    Set.eq_univ_of_univ_subset
      (hdense.closure_eq ▸ (hScl.closure_eq ▸ closure_mono hsub))
  have : (u, v) ∈ S := huniv ▸ Set.mem_univ _
  exact this

/-- **The single-grid engine is the mesh engine at `I := ℕ × ℕ` (PROVED).**

Confirms §K's `indiff_extends_of_denseGridImage` is the `I := ℕ × ℕ`,
`(meshJ, meshK) := (αⱼ ∘ fst, αₖ ∘ snd)` instance of the general engine — so the
generalization strictly subsumes it (and the single-grid case is exactly the one
§L proved unsatisfiable, while the general mesh case is satisfiable by a refinement
family).  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem indiff_extends_of_denseGridImage_via_mesh [∀ i, TopologicalSpace (X i)]
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t) (c : X t) (b : Profile X)
    (hdense : GridImageDense G)
    (hclosed : IsClosed {z : Profile X | P.indiff z b})
    (hgrid : ∀ m n : ℕ, P.indiff (tri G.a j k t (G.αj m) (G.αk n) c) b)
    (u : X j) (v : X k) :
    P.indiff (tri G.a j k t u v c) b :=
  indiff_extends_of_denseJKMesh hjk hjt hkt G.a c b
    (fun mn : ℕ × ℕ => G.αj mn.1) (fun mn : ℕ × ℕ => G.αk mn.2)
    hdense hclosed (fun mn => hgrid mn.1 mn.2) u v

/-! ## §N.  Scoping: does the utility-side dense-range infrastructure build a
    usable `DenseJKMesh` for the cover?

§M reduced the cover's analytic closure to a `DenseJKMesh` (a dense `{j,k}`-mesh).
Does the project's per-coordinate dense-range infrastructure
(`CoordinateDenseRangeCertificate := ∀ i, DenseRange (R.V i)`, and the
surjectivity/rational-image chain) build one?

**Two findings, both machine-checked below.**

**(N.1 — positive) A `DenseJKMesh` IS reachable from per-coordinate dense families.**
If each coordinate has a dense family (`DenseRange meshJ`, `DenseRange meshK`),
their **product** over `I × I'` is dense in `X j × X k` (Mathlib `DenseRange.prodMap`).
So the *density input* of the §M engine is reachable from per-coordinate density —
exactly what the surjectivity/rational-image infrastructure provides for ℝ-valued
coordinates.

**(N.2 — the catch) The §M engine's fixed-`b` hypothesis is the wrong shape for the
cover.**  `indiff_extends_of_denseJKMesh` requires `[meshJ i | meshK i | c] ∼ b` for
a **fixed** `b` across the *whole* dense mesh.  Under a representation this forces
`V_j (meshJ i) + V_k (meshK i)` to be **constant** on a dense 2-D set — impossible
for non-degenerate `V_j, V_k`.  So the §M engine extends a *fixed* indifference (a
single level set), **not** the cover's *moving-target* statement `[x|v|c] ∼
[grid rep of (x,v)|c]` (where the right side depends on `(x,v)`).  The cover is a
**relation between two slice points**, not membership in one fixed indifference
class; closing it needs a different engine (continuity of the *comparison map*, or
the grid-restricted residue transported along the mesh), not `indiff_extends`. -/

/-- **(N.1) A `DenseJKMesh` from two per-coordinate dense families (PROVED).**

The product of a dense `j`-family and a dense `k`-family is a dense `{j,k}`-mesh
(`DenseRange.prodMap`).  So the §M density input is reachable from per-coordinate
density — the content the surjectivity/rational-image infrastructure supplies for
ℝ coordinates.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem denseJKMesh_of_coordinateDenseRanges [∀ i, TopologicalSpace (X i)]
    {j k : ι} {I I' : Type*} (meshJ : I → X j) (meshK : I' → X k)
    (hJ : DenseRange meshJ) (hK : DenseRange meshK) :
    DenseJKMesh j k (fun p : I × I' => meshJ p.1) (fun p : I × I' => meshK p.2) :=
  hJ.prodMap hK

/-- **(N.2) The fixed-`b` mesh hypothesis is unsatisfiable on a genuinely dense
mesh under a rep (PROVED — the obstruction).**

If `[meshJ i₁|meshK i₁|c] ∼ b` and `[meshJ i₂|meshK i₂|c] ∼ b` both hold (the §M
engine's hypothesis at two mesh points), then under a representation the two
slice-scores are equal: `V_j (meshJ i₁) + V_k (meshK i₁) = V_j (meshJ i₂) + V_k
(meshK i₂)`.  So the §M hypothesis forces the slice-score **constant** across the
mesh — which a dense mesh with non-constant `V_j + V_k` cannot satisfy.  This
records *why* the §M engine, though sound, is mis-targeted for the cover: the cover
is a moving-target relation, not a fixed indifference class.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem fixedB_meshHypothesis_forces_constant_score
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (c : X t) (b : Profile X)
    (x₁ : X j) (v₁ : X k) (x₂ : X j) (v₂ : X k)
    (h₁ : P.indiff (tri a j k t x₁ v₁ c) b)
    (h₂ : P.indiff (tri a j k t x₂ v₂ c) b) :
    R.V j x₁ + R.V k v₁ = R.V j x₂ + R.V k v₂ := by
  -- Score split of a `tri` profile (local copy of the standard engine).
  have score_tri : ∀ (u : X j) (vv : X k) (cc : X t),
      (∑ i, R.V i (tri a j k t u vv cc i))
        = R.V j u + R.V k vv + R.V t cc
          + ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
    intro u vv cc
    have hkj : k ≠ j := Ne.symm hjk
    have htj : t ≠ j := Ne.symm hjt
    have htk : t ≠ k := Ne.symm hkt
    unfold tri
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (show k ∈ Finset.univ.erase j from
          Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩),
        ← Finset.add_sum_erase _ _ (show t ∈ (Finset.univ.erase j).erase k from
          Finset.mem_erase.mpr ⟨htk, Finset.mem_erase.mpr ⟨htj, Finset.mem_univ t⟩⟩)]
    have hj : (Function.update (Function.update (Function.update a j u) k vv) t cc) j = u := by
      rw [Function.update_of_ne hjt, Function.update_of_ne hjk, Function.update_self]
    have hk : (Function.update (Function.update (Function.update a j u) k vv) t cc) k = vv := by
      rw [Function.update_of_ne hkt, Function.update_self]
    have ht : (Function.update (Function.update (Function.update a j u) k vv) t cc) t = cc := by
      rw [Function.update_self]
    rw [hj, hk, ht]
    have hrest : (∑ i ∈ ((Finset.univ.erase j).erase k).erase t,
          R.V i (Function.update (Function.update (Function.update a j u) k vv) t cc i))
        = ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hit : i ≠ t := Finset.ne_of_mem_erase hi
      have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      have hij : i ≠ j :=
        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij]
    rw [hrest]; ring
  -- Both indifferences decode to "slice profile score = score b"; subtract.
  have e₁ := (indiff_iff_score R).mp h₁
  have e₂ := (indiff_iff_score R).mp h₂
  rw [score_tri] at e₁ e₂
  linarith

/-! ## §O.  The comparison-map closure engine (the engine N.2 calls for)

§N.2 showed the cover is a **moving-target relation**, not a fixed indifference
class, so the §M `indiff_extends` engine is mis-shaped.  The right engine extends a
**`weakPref` comparison between two continuously-varying profiles** from a dense
parameter set to the whole space, using **joint** closedness of the `≽`-graph.

**The honest topological input.**  The engine needs the *joint* comparison set
`{(y, z) : Profile X × Profile X | y ≽ z}` to be **closed** in the product topology
— strictly stronger than the per-reference closedness `PreferenceContinuous` gives
(that fixes one side).  We take it as a named input `JointWeakPrefClosed` and prove
a **soundness gate**: under a representation with continuous coordinate utilities it
genuinely holds (the graph is the preimage of `{(p,q) | q ≤ p}` under the continuous
`(y,z) ↦ (∑V y, ∑V z)`).  This mirrors how `PreferenceContinuous` is a named
topological input with an `additiveRep` soundness gate.

**The engine.**  Given two continuous parametrised profile maps `F, G : Y → Profile X`,
if `F y ≽ G y` on a **dense** set of `y` and the joint `≽`-graph is closed, then
`F y ≽ G y` for **all** `y`.  This is the comparison-map closure: it extends the
grid-restricted residue's comparison along a dense mesh to the continuum, which is
exactly what the cover needs (the two profiles are the two sides of the residue
comparison, varying with the slice value). -/

/-- **Joint closedness of the `≽`-graph (the named topological input).**

The set `{(y, z) | y ≽ z}` is closed in `Profile X × Profile X`.  Strictly stronger
than `PreferenceContinuous` (which fixes one argument); it is what a *moving-target*
comparison closure needs.  Soundness-gated below. -/
def JointWeakPrefClosed [∀ i, TopologicalSpace (X i)] (P : ProductPref X) : Prop :=
  IsClosed {yz : Profile X × Profile X | P.weakPref yz.1 yz.2}

/-- **Soundness gate: the joint `≽`-graph is closed under a rep with continuous
utilities (PROVED).**

`y ≽ z ↔ ∑V z ≤ ∑V y` (`R.represents`), so the graph is the preimage of the closed
set `{(p, q) | q ≤ p} ⊆ ℝ × ℝ` under the continuous map
`(y, z) ↦ (∑V y, ∑V z)`.  Confirms `JointWeakPrefClosed` hides nothing false.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem jointWeakPrefClosed_of_additiveRep [∀ i, TopologicalSpace (X i)]
    (R : AdditiveRep P) (hCont : ∀ i : ι, Continuous (R.V i)) :
    JointWeakPrefClosed P := by
  unfold JointWeakPrefClosed
  set f : Profile X → ℝ := fun x => ∑ i, R.V i (x i) with hf
  have hfc : Continuous f :=
    WakkerRoadmap.CertificateChecklist.additiveRep_sum_continuous R hCont
  -- The graph equals the preimage of {(p,q) | q ≤ p} under (y,z) ↦ (f y, f z).
  have hset : {yz : Profile X × Profile X | P.weakPref yz.1 yz.2}
      = (fun yz : Profile X × Profile X => (f yz.1, f yz.2)) ⁻¹'
          {pq : ℝ × ℝ | pq.2 ≤ pq.1} := by
    ext yz
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact R.represents yz.1 yz.2
  rw [hset]
  -- {(p,q) | q ≤ p} is closed; pull back along the continuous map.
  have hcont_pair : Continuous (fun yz : Profile X × Profile X => (f yz.1, f yz.2)) :=
    Continuous.prodMk (hfc.comp continuous_fst) (hfc.comp continuous_snd)
  have hclosed_le : IsClosed {pq : ℝ × ℝ | pq.2 ≤ pq.1} :=
    isClosed_le continuous_snd continuous_fst
  exact hclosed_le.preimage hcont_pair

/-- **The comparison-map closure engine (PROVED).**

Two continuous parametrised profile maps `F, G : Y → Profile X`.  If `F y ≽ G y`
holds on a **dense** set of parameters and the joint `≽`-graph is closed
(`JointWeakPrefClosed`), then `F y ≽ G y` for **all** `y`.

This is the engine §N.2 identified as the right shape for the cover: it extends a
*moving-target* comparison (both sides vary with `y`) along a dense set — unlike the
§M engine, which extends a fixed indifference class.  The proof: `{y | F y ≽ G y}`
is the preimage of the closed joint graph under the continuous `y ↦ (F y, G y)`,
hence closed; a closed set containing a dense set is everything.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem weakPref_extends_of_dense [∀ i, TopologicalSpace (X i)]
    {Y : Type*} [TopologicalSpace Y]
    (F G : Y → Profile X) (hF : Continuous F) (hG : Continuous G)
    (hjoint : JointWeakPrefClosed P)
    {D : Set Y} (hdense : Dense D)
    (hagree : ∀ y ∈ D, P.weakPref (F y) (G y))
    (y : Y) :
    P.weakPref (F y) (G y) := by
  -- S = {y | F y ≽ G y} is closed (preimage of the joint graph under (F, G)).
  set S : Set Y := {y | P.weakPref (F y) (G y)} with hS
  have hScl : IsClosed S := by
    have hSeq : S = (fun y => (F y, G y)) ⁻¹'
        {yz : Profile X × Profile X | P.weakPref yz.1 yz.2} := by
      ext y; simp [hS]
    rw [hSeq]
    exact hjoint.preimage (Continuous.prodMk hF hG)
  -- D ⊆ S, D dense, S closed ⟹ S = univ.
  have hDS : D ⊆ S := hagree
  have huniv : S = Set.univ :=
    Set.eq_univ_of_univ_subset
      (hdense.closure_eq ▸ (hScl.closure_eq ▸ closure_mono hDS))
  have : y ∈ S := huniv ▸ Set.mem_univ y
  exact this

/-- **Indifference closure as two comparison closures (PROVED).**

`F y ∼ G y` everywhere from dense agreement, by applying `weakPref_extends_of_dense`
in both directions.  This recovers the indifference-extension shape (cf. §M) but in
the *moving-target* form the cover needs (both `F` and `G` vary with `y`), which §M
could not express.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem indiff_extends_of_dense [∀ i, TopologicalSpace (X i)]
    {Y : Type*} [TopologicalSpace Y]
    (F G : Y → Profile X) (hF : Continuous F) (hG : Continuous G)
    (hjoint : JointWeakPrefClosed P)
    {D : Set Y} (hdense : Dense D)
    (hagree : ∀ y ∈ D, P.indiff (F y) (G y))
    (y : Y) :
    P.indiff (F y) (G y) :=
  ⟨weakPref_extends_of_dense F G hF hG hjoint hdense (fun y hy => (hagree y hy).1) y,
   weakPref_extends_of_dense G F hG hF hjoint hdense (fun y hy => (hagree y hy).2) y⟩

/-! ## §P.  The mesh, from axioms: density is FREE for ℝ-coordinates

For the project's actual Debreu–Koopmans setting — `X i = ℝ` for every `i`
(`ProductPref (fun _ : ι => ℝ)`) — the `{j,k}`-mesh's **density** is not a residual
at all: the rationals are dense in ℝ (`Rat.denseRange_cast`), so the rational-image
families give a dense `{j,k}`-mesh with **no axiom beyond the ambient topology**.

This settles the *mesh* half of "build the mesh and the matching": for ℝ-valued
coordinates the dense mesh exists unconditionally (a strictly positive finding —
earlier sections only showed density was *reachable* from per-coordinate density;
here it is outright free).  What is **not** free, and is the genuine §IV.5 frontier,
is the *matching* — the residue/cover holding **on** that mesh (`indiff_extends`'s
`hagree` hypothesis).  That is the Thomsen cross-pair cancellation content
(`OffCalCompensationMatch`, characterized as KLST `t`-block separability,
§D.3-level), which the strip/Kz probes prove is not A1-derivable and which requires
the full standard-sequence double-cancellation construction. -/

/-- **The `{j,k}`-mesh is free for ℝ-coordinates (PROVED).**

For real coordinates, the rational casts `(↑) : ℚ → ℝ` are dense
(`Rat.denseRange_cast`), so their product is a dense `{j,k}`-mesh — no axiom beyond
the ambient real topology.  So the *density* half of the §IV.2.6 mesh is
unconditionally available for the DK setting; only the *matching* (the residue on
the mesh) remains.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem realDenseJKMesh {ι : Type u} [Fintype ι] [DecidableEq ι]
    {P : ProductPref (fun _ : ι => ℝ)} (j k : ι) :
    DenseJKMesh (X := fun _ : ι => ℝ) j k
      (fun p : ℚ × ℚ => ((p.1 : ℝ) : (fun _ : ι => ℝ) j))
      (fun p : ℚ × ℚ => ((p.2 : ℝ) : (fun _ : ι => ℝ) k)) :=
  denseJKMesh_of_coordinateDenseRanges (X := fun _ : ι => ℝ)
    (fun q : ℚ => ((q : ℝ) : (fun _ : ι => ℝ) j))
    (fun q : ℚ => ((q : ℝ) : (fun _ : ι => ℝ) k))
    Rat.denseRange_cast Rat.denseRange_cast

/-! ## §Q.  Attacking the matching: its irreducible core is cross-pair trade-off
    transitivity (the genuine §IV.5 axiom), NOT solvability

The matching residual `OffCalCompensationMatch` is the off-cal diagonal step, which
the project reduces (`OptionB_C1aThirdCoordinate`) to `KzTransfer` + `StripTransfer`
at a third coordinate.  Attacking it from bare axioms forces the honest question:
**what does `KzTransfer` actually need?**

`KzTransfer`: from `P1 : [x|q|c] ∼ [y|p|c]` (the j-step `x→y` trades for the k-step
`q→p` at level `c`) and `J2 : [x|r|w] ∼ [y|r|c]` (the same j-step `x→y` trades for
the t-step `w→c`), conclude `Kz : [z|q|c] ∼ [z|p|w]` (the k-step `q→p` trades for
the t-step `w→c`).  Structurally: P1 says `(j: x→y) ≡ (k: q→p)`, J2 says
`(j: x→y) ≡ (t: w→c)`, and the conclusion is `(k: q→p) ≡ (t: w→c)` — the
**transitivity of trade-off equality across coordinate pairs**.

This is Wakker IV.2.5 **trade-off consistency** (the hexagon).  It is **not** a
consequence of restricted solvability: solvability supplies the *existence* of
compensating values (`compensating_reference_value_of_…`), but **not** the
*equality-transfer* across pairs.  And the §5 gate proved the project's formalized
`TradeoffConsistency` is only *single-coordinate* indifference base-independence —
it carries no cross-pair content.  So the genuine irreducible input is a named
**cross-pair trade-off transitivity** `CrossPairTradeoffTransitivity`, which we
define, show **suffices** for `KzTransfer` (pure weak order), and prove
**necessary** under a representation.  This pins the matching's true axiom: not
solvability, not A1, but cross-pair trade-off consistency — exactly Wakker's
hexagon input. -/

/-- **Cross-pair trade-off transitivity (the genuine §IV.5 / Wakker IV.2.5 hexagon
input).**

If a j-step `x→y` trades for a k-step `q→p` (at level `c`), and the same j-step
trades for a t-step `w→c` (at k-value `r`), then the k-step trades for the t-step at
any j-value `z`.  This is the transitivity of trade-off equality across the three
coordinate pairs `{j,k}`, `{j,t}`, `{k,t}` — the content the additive
representation's common scale `δ` encodes, and which solvability (existence of
compensations) does **not** supply. -/
def CrossPairTradeoffTransitivity (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (x y z : X j) (p q r : X k) (w : X t),
    P.indiff (tri a j k t x q (a t)) (tri a j k t y p (a t)) →   -- (j:x→y) ≡ (k:q→p)
    P.indiff (tri a j k t x r w) (tri a j k t y r (a t)) →       -- (j:x→y) ≡ (t:w→c)
    P.indiff (tri a j k t z q (a t)) (tri a j k t z p w)         -- (k:q→p) ≡ (t:w→c)

/-- **`KzTransfer` is exactly `CrossPairTradeoffTransitivity` (PROVED, definitional).**

The two are the *same* statement (both say: P1 ∧ J2 ⟹ Kz).  This makes precise that
`KzTransfer` — half of the matching — **is** the cross-pair trade-off transitivity
axiom, nothing weaker.  Audit `[propext]`. -/
theorem kzTransfer_iff_crossPairTradeoffTransitivity {j k t : ι} :
    KzTransfer P j k t ↔ CrossPairTradeoffTransitivity P j k t :=
  Iff.rfl

/-- **`KzTransfer` from cross-pair trade-off transitivity (PROVED).**

The forward direction of the characterization, as a usable lemma: the matching's
`KzTransfer` half follows from the named hexagon input.  Audit `[propext]`. -/
theorem kzTransfer_of_crossPairTradeoffTransitivity {j k t : ι}
    (h : CrossPairTradeoffTransitivity P j k t) :
    KzTransfer P j k t := h

/-- **Soundness gate: cross-pair trade-off transitivity is necessary under a rep
(PROVED).**

Under any additive representation, P1 forces `V_k q - V_k p = V_j y - V_j x` and J2
forces `V_t (a t) - V_t w = V_j y - V_j x` (the common trade-off scalar `δ`); so the
conclusion `V_k q - V_k p = V_t (a t) - V_t w` holds — i.e. the cross-pair
transitivity holds.  This confirms the hexagon input hides nothing false and is
exactly the right strength (the additive scale composes trade-offs across pairs).
The point of §Q: this is what the matching needs — **not** solvability (existence of
compensations) but this **equality-transfer** across pairs.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem crossPairTradeoffTransitivity_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    CrossPairTradeoffTransitivity P j k t := by
  intro a' x y z p q r w hP1 hJ2
  -- Score split of a `tri` profile at the background a' (local copy of the engine).
  have score_tri' : ∀ (u : X j) (vv : X k) (cc : X t),
      (∑ i, R.V i (tri a' j k t u vv cc i))
        = R.V j u + R.V k vv + R.V t cc
          + ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a' i) := by
    intro u vv cc
    have hkj : k ≠ j := Ne.symm hjk
    have htj : t ≠ j := Ne.symm hjt
    have htk : t ≠ k := Ne.symm hkt
    unfold tri
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (show k ∈ Finset.univ.erase j from
          Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩),
        ← Finset.add_sum_erase _ _ (show t ∈ (Finset.univ.erase j).erase k from
          Finset.mem_erase.mpr ⟨htk, Finset.mem_erase.mpr ⟨htj, Finset.mem_univ t⟩⟩)]
    have hj : (Function.update (Function.update (Function.update a' j u) k vv) t cc) j = u := by
      rw [Function.update_of_ne hjt, Function.update_of_ne hjk, Function.update_self]
    have hk : (Function.update (Function.update (Function.update a' j u) k vv) t cc) k = vv := by
      rw [Function.update_of_ne hkt, Function.update_self]
    have ht : (Function.update (Function.update (Function.update a' j u) k vv) t cc) t = cc := by
      rw [Function.update_self]
    rw [hj, hk, ht]
    have hrest : (∑ i ∈ ((Finset.univ.erase j).erase k).erase t,
          R.V i (Function.update (Function.update (Function.update a' j u) k vv) t cc i))
        = ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a' i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hit : i ≠ t := Finset.ne_of_mem_erase hi
      have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      have hij : i ≠ j :=
        Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij]
    rw [hrest]; ring
  have e1 := (indiff_iff_score R).mp hP1
  have e2 := (indiff_iff_score R).mp hJ2
  rw [score_tri', score_tri'] at e1 e2
  rw [indiff_iff_score R, score_tri', score_tri']
  linarith

end ProductPref
end WakkerInfra

/-! ## Audit — the R1.2 transport is `sorry`-free.

The transport from the grid-restricted residue to the full `TBlockDiagonalResidue`
is reduced — by pure weak order — to the single named level-stable grid-coverage
residual `StableGridIndifferentCover` (proved necessary under a rep modulo
grid-utility reach, the §IV.2.6 density content).  Composed with the grid-Thomsen
frontier capstone, this yields the full residue from {calibrated grid + forward
frontier + stable cover}.  All declarations audit at
`[propext, Classical.choice, Quot.sound]` (the transport core is `[propext,
Quot.sound]`); none carries `sorry`. -/

#print axioms WakkerInfra.ProductPref.stableGridIndifferentCover_of_additiveRep
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_gridRestricted_and_stableCover
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_frontier_and_stableCover

/-! §E — full residue over all backgrounds + the grid-route hexagon capstone. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_gridRouteData
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_gridRoute

/-! §F — J2 folded into the §IV.2.6 escape grid. -/

#print axioms WakkerInfra.ProductPref.j2Supplier_of_escapeData
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_gridRoute_escapeJ2

/-! §G — unified single-bundle interface (organizational; the three Thomsen facts
do NOT collapse — see the docstring). -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_unifiedGridRoute

/-! §H — `OffCalJBracket` discharged from the §IV.2.6 escape grid (pure order
theory; a named input removed from bare axioms). -/

#print axioms WakkerInfra.ProductPref.offCalJBracket_of_escapeGrid
#print axioms WakkerInfra.ProductPref.gridThomsenForwardFrontier_of_escapeGrid

/-! §I — end-to-end route data with the reach bracket escape-discharged. -/

#print axioms WakkerInfra.ProductPref.tBlockGridRouteData_of_esc
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_gridRouteDataEsc
#print axioms WakkerInfra.ProductPref.doubleCancellation_of_unifiedGridRouteEsc

/-! §J — scoping the exact-match cover: solvability reaches only a strictly weaker
dense-interpolant cover; the exact-match cover encodes cross-pair transport. -/

#print axioms WakkerInfra.ProductPref.denseSliceInterpolantCover_of_solvability_and_bracket
#print axioms WakkerInfra.ProductPref.stableCover_gives_levelTransport

/-! §K — the continuity+density closure engine (the genuine §IV.2.6 path):
slice-map continuity + dense grid image ⟹ indifference extends to the continuum. -/

#print axioms WakkerInfra.ProductPref.continuous_jkSliceMap
#print axioms WakkerInfra.ProductPref.indiff_extends_of_denseGridImage

/-! §L — scoping verdict: the dense-range infrastructure does NOT discharge
`GridImageDense` (it forces single-axis density, which the standard-sequence
arithmetic-progression no-go refutes; the genuine input is a refinement mesh). -/

#print axioms WakkerInfra.ProductPref.gridImageDense_imp_axisDenseRange

/-! §M — the generalized closure engine over an abstract dense `{j,k}`-mesh (the
fix for §L: works for a §IV.2.6 refinement mesh, not just the single grid). -/

#print axioms WakkerInfra.ProductPref.indiff_extends_of_denseJKMesh
#print axioms WakkerInfra.ProductPref.indiff_extends_of_denseGridImage_via_mesh

/-! §N — scoping the utility-side density infrastructure for the mesh: density is
reachable (N.1), but the §M fixed-`b` engine is mis-targeted for the cover (N.2). -/

#print axioms WakkerInfra.ProductPref.denseJKMesh_of_coordinateDenseRanges
#print axioms WakkerInfra.ProductPref.fixedB_meshHypothesis_forces_constant_score

/-! §O — the comparison-map closure engine (the moving-target closure N.2 calls
for): joint `≽`-graph closedness (soundness-gated) + dense agreement ⟹ everywhere. -/

#print axioms WakkerInfra.ProductPref.jointWeakPrefClosed_of_additiveRep
#print axioms WakkerInfra.ProductPref.weakPref_extends_of_dense
#print axioms WakkerInfra.ProductPref.indiff_extends_of_dense

/-! §P — the mesh is FREE for ℝ-coordinates (rationals dense); only the matching
(the residue on the mesh) remains as the genuine §IV.5 frontier. -/

#print axioms WakkerInfra.ProductPref.realDenseJKMesh

/-! §Q — attacking the matching: its irreducible core is cross-pair trade-off
transitivity (Wakker IV.2.5 hexagon), proved to be exactly `KzTransfer` and
necessary under a rep — NOT solvability, NOT A1. -/

#print axioms WakkerInfra.ProductPref.kzTransfer_iff_crossPairTradeoffTransitivity
#print axioms WakkerInfra.ProductPref.kzTransfer_of_crossPairTradeoffTransitivity
#print axioms WakkerInfra.ProductPref.crossPairTradeoffTransitivity_of_additiveRep
