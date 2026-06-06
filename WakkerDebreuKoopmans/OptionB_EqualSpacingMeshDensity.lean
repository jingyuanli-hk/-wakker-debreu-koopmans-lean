/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — G3: the §IV.2.6 mesh density, and the honest redundancy finding

> **STATUS: `sorry`-free.  Leads with a redundancy finding, then the genuine
> density-closure brick for the *solvability* route.**
> Not in the umbrella import.

This file executes **G3** of `OptionB_SectionIV5GridConstructionRoadmap.md` — but the
first thing it does is correct the route.

## The finding that reshapes G3 (and retroactively G2)

`TBlockDiagonalResidue P j k t` (`OptionB_C1aDiagonalResidue`) is **definitionally
`TBlockWeakIndependent P j k t` with two extra disequality guards** (`x ≠ z`,
`r ≠ p`): identical binders, identical hypothesis, identical conclusion.  So the
residue follows from the block condition by **dropping the guards** —
`tBlockDiagonalResidue_of_tBlockWeakIndependent`, a one-liner (§A).

Consequence (§B): in the **block route** (G1.a/b/c → G2, which feed the three KLST
block conditions into the grid machinery), producing `TBlockDiagonalResidue` needs
**no grid, no calibrated cover, no A1-`j`, no `K`/`J`-block** — it is immediate from
`TBlockWeakIndependent` alone.  G2's
`tBlockDiagonalResidue_of_blockIndependence_and_coverData` is therefore a *sound but
redundant* over-strong route to a trivial consequence, and the naive G3 (discharge
`StableGridIndifferentCover` to feed that transport) adds nothing in the block route.

This is the §D.2b-style "circular/redundant for R1.1" pattern at the residue level:
the grid construction only does genuine work when its **input is bare restricted
solvability**, not when it is the block conditions (which already contain the target
modulo guards).  The honest conclusion: **the grid route's entire value is G1 —
deriving the block conditions from solvability (the `n ≥ 3` crux).**  The transport
(G2) and density (G3) are non-redundant *only* in the bare-solvability route.

## What this file delivers (all machine-checked, no `sorry`)

* **§A** `tBlockDiagonalResidue_of_tBlockWeakIndependent` — the guard-drop (the
  residue is free from the block condition).
* **§B** `tBlockDiagonalResidue_blockRoute_is_redundant` — the residue from
  `TBlockWeakIndependent` alone, with the explicit note that this subsumes G2.
* **§C** `weakPrefComparison_extends_of_denseJKMesh` /
  `indiffComparison_extends_of_denseJKMesh` — the genuine §IV.2.6 density closure
  *for the solvability route*: a fixed-level `≽`/`∼` comparison extends from a dense
  `{j,k}`-mesh to **all** `{j,k}`-values, via the §O moving-target engine
  (`weakPref_extends_of_dense`) + `JointWeakPrefClosed` (continuity).  Plus the ℝ
  corollary `weakPrefComparison_extends_real` (the mesh is free for ℝ, `realDenseJKMesh`).
* **§D** `jointWeakPrefClosed_necessary` — soundness gate (continuity input necessary
  under a rep with continuous utilities).

## Honest scope

§A/§B are the finding: the block route does not need G2/G3.  §C is the genuine,
non-redundant density brick — but it only **extends a supplied mesh-comparison**;
the mesh-comparison itself (the "matching") is, by `OptionB_C1aGridTransport` §Q,
exactly `KzTransfer` = cross-pair trade-off transitivity = the same `n ≥ 3` crux the
block conditions are.  So even in the solvability route, the density closure does not
escape the crux — it reduces the cover to the matching-on-mesh, which is the crux.
Net: **the single genuine open obligation across G1/G2/G3 is the cross-pair /
block-separability content from bare solvability.**

Imports `OptionB_C1aGridTransport` (the §O engine, `DenseJKMesh`, `realDenseJKMesh`),
`OptionB_C1aDiagonalResidue` (`TBlockDiagonalResidue`), `OptionB_C1aBlockIndependence`
(`TBlockWeakIndependent`).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aGridTransport
import WakkerDebreuKoopmans.OptionB_C1aDiagonalResidue
import WakkerDebreuKoopmans.OptionB_C1aBlockIndependence

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

/-! ## §A.  The guard-drop: the residue is free from the block condition

`TBlockDiagonalResidue P j k t` is `TBlockWeakIndependent P j k t` with the two extra
hypotheses `x ≠ z`, `r ≠ p`.  Dropping them is the whole proof. -/

/-- **The `t`-block diagonal residue from `TBlockWeakIndependent` (PROVED, trivial).**

`TBlockDiagonalResidue` is definitionally `TBlockWeakIndependent` with the disequality
guards `x ≠ z`, `r ≠ p`; supplying the block condition and ignoring the guards proves
it.  So the residue the downstream one-Thomsen hexagon capstone consumes is **free**
from the standard KLST `t`-block separability — no grid, no cover, no density.  Audit
`[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_of_tBlockWeakIndependent
    {j k t : ι} (hTB : TBlockWeakIndependent P j k t) :
    TBlockDiagonalResidue P j k t :=
  fun a x z p r w c _hxz _hrp hw => hTB a x z p r w c hw

/-! ## §B.  Consequence: the block-route transport (G2) and cover (G3) are redundant -/

/-- **The G2 output from `TBlockWeakIndependent` alone (PROVED) — G2/G3 redundant in
the block route.**

This re-derives G2's headline `TBlockDiagonalResidue P j k t` from **one** of G2's
inputs (`TBlockWeakIndependent`) by §A, using **none** of the grid, the level-stable
cover, A1-`j`, `KBlockWeakIndependent`, or `JBlockWeakIndependent`.  So
`OptionB_EqualSpacingGridTransport.tBlockDiagonalResidue_of_blockIndependence_and_coverData`
is a sound but **redundant** over-strong route, and the naive G3 (discharging
`StableGridIndifferentCover` to feed that transport) adds nothing in the block route.
The grid construction does genuine work only when its input is bare restricted
solvability, not the block conditions.  Audit `[propext, Quot.sound]`. -/
theorem tBlockDiagonalResidue_blockRoute_is_redundant
    {j k t : ι} (hTB : TBlockWeakIndependent P j k t) :
    TBlockDiagonalResidue P j k t :=
  tBlockDiagonalResidue_of_tBlockWeakIndependent hTB

/-! ## §C.  The genuine §IV.2.6 density closure (for the *solvability* route)

In the bare-solvability route the `t`-block comparison is **not** free — it must be
extended from where solvability reaches it (a dense `{j,k}`-mesh) to all `{j,k}`-
values.  The §O moving-target engine `weakPref_extends_of_dense` + `JointWeakPrefClosed`
do exactly this.  Here we instantiate it to the concrete fixed-level `{j,k}`-comparison
over a dense mesh — the honest §IV.2.6 density-closure brick. -/

/-- **Fixed-level `≽`-comparison extends from a dense `{j,k}`-mesh to all values
(PROVED).**

Fix a level `c` and a background `a`.  If the comparison `[mⱼ|mₖ|c] ≽ [m'ⱼ|m'ₖ|c]`
holds for **all** mesh-index pairs (the left pair from `(meshJ, meshK)`, the right
from `(meshJ', meshK')`), and the joint `≽`-graph is closed (`JointWeakPrefClosed`,
the §O continuity input), then `[x|r|c] ≽ [z|p|c]` for **all** `x, z : X j`,
`r, p : X k`.

This is the §IV.2.6 density closure in the moving-target form the cover needs: both
compared profiles vary with the slice value.  It is the `weakPref_extends_of_dense`
engine at parameter space `(X j × X k) × (X j × X k)`, dense set the product mesh.
Audit `[propext, Classical.choice, Quot.sound]`.

**Honest scope:** this *extends* a supplied mesh-comparison; the mesh-comparison
itself (`hmesh`) is the genuine open "matching" content, which `OptionB_C1aGridTransport`
§Q identifies as `KzTransfer` = the cross-pair crux. -/
theorem weakPrefComparison_extends_of_denseJKMesh
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (c : X t)
    (hjoint : JointWeakPrefClosed P)
    {I I' : Type*} (meshJ : I → X j) (meshK : I → X k)
    (meshJ' : I' → X j) (meshK' : I' → X k)
    (hdense : DenseJKMesh j k meshJ meshK)
    (hdense' : DenseJKMesh j k meshJ' meshK')
    (hmesh : ∀ (i : I) (i' : I'),
      P.weakPref (tri a j k t (meshJ i) (meshK i) c)
                 (tri a j k t (meshJ' i') (meshK' i') c))
    (x z : X j) (r p : X k) :
    P.weakPref (tri a j k t x r c) (tri a j k t z p c) := by
  -- Parameter space: the two slice values, left and right.
  set F : (X j × X k) × (X j × X k) → Profile X :=
    fun y => jkSliceMap a j k t c y.1 with hF
  set G : (X j × X k) × (X j × X k) → Profile X :=
    fun y => jkSliceMap a j k t c y.2 with hG
  have hFc : Continuous F :=
    (continuous_jkSliceMap a j k t hjk hjt hkt c).comp continuous_fst
  have hGc : Continuous G :=
    (continuous_jkSliceMap a j k t hjk hjt hkt c).comp continuous_snd
  -- The product mesh is dense in `(X j × X k) × (X j × X k)`.
  have hprod : DenseRange
      (fun ii' : I × I' =>
        ((meshJ ii'.1, meshK ii'.1), (meshJ' ii'.2, meshK' ii'.2))) :=
    hdense.prodMap hdense'
  -- Agreement on the dense range (from `hmesh`).
  have hagree : ∀ y ∈ Set.range
      (fun ii' : I × I' =>
        ((meshJ ii'.1, meshK ii'.1), (meshJ' ii'.2, meshK' ii'.2))),
      P.weakPref (F y) (G y) := by
    rintro _ ⟨ii', rfl⟩
    exact hmesh ii'.1 ii'.2
  -- Extend to the whole parameter space; evaluate at `((x,r),(z,p))`.
  exact weakPref_extends_of_dense F G hFc hGc hjoint hprod hagree ((x, r), (z, p))

/-- **Fixed-level `∼`-comparison extends from a dense `{j,k}`-mesh (PROVED).**

The indifference version: dense mesh agreement `[mesh|c] ∼ [mesh'|c]` + continuity
extends to `[x|r|c] ∼ [z|p|c]` everywhere.  Two applications of
`weakPrefComparison_extends_of_denseJKMesh` (both `≽`-directions).  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem indiffComparison_extends_of_denseJKMesh
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (c : X t)
    (hjoint : JointWeakPrefClosed P)
    {I I' : Type*} (meshJ : I → X j) (meshK : I → X k)
    (meshJ' : I' → X j) (meshK' : I' → X k)
    (hdense : DenseJKMesh j k meshJ meshK)
    (hdense' : DenseJKMesh j k meshJ' meshK')
    (hmesh : ∀ (i : I) (i' : I'),
      P.indiff (tri a j k t (meshJ i) (meshK i) c)
               (tri a j k t (meshJ' i') (meshK' i') c))
    (x z : X j) (r p : X k) :
    P.indiff (tri a j k t x r c) (tri a j k t z p c) :=
  ⟨weakPrefComparison_extends_of_denseJKMesh hjk hjt hkt a c hjoint
      meshJ meshK meshJ' meshK' hdense hdense'
      (fun i i' => (hmesh i i').1) x z r p,
   weakPrefComparison_extends_of_denseJKMesh hjk hjt hkt a c hjoint
      meshJ' meshK' meshJ meshK hdense' hdense
      (fun i' i => (hmesh i i').2) z x p r⟩

/-- **The density closure is FREE for ℝ-coordinates (PROVED corollary).**

For `X i = ℝ`, the rational mesh `realDenseJKMesh` is dense, so the §C closure needs
**no density axiom** beyond the ambient topology: a fixed-level `≽`-comparison holding
on the rational `{j,k}`-mesh extends to all reals, given `JointWeakPrefClosed`.  This
pins the only remaining content to the mesh-comparison itself (the matching = the
crux).  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem weakPrefComparison_extends_real
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {P : ProductPref (fun _ : ι => ℝ)} [ProductPref.IsWeakOrder P]
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile (fun _ : ι => ℝ)) (c : (fun _ : ι => ℝ) t)
    (hjoint : JointWeakPrefClosed P)
    (hmesh : ∀ (q q' : ℚ × ℚ),
      P.weakPref (tri a j k t ((q.1 : ℝ) : (fun _ : ι => ℝ) j)
                              ((q.2 : ℝ) : (fun _ : ι => ℝ) k) c)
                 (tri a j k t ((q'.1 : ℝ) : (fun _ : ι => ℝ) j)
                              ((q'.2 : ℝ) : (fun _ : ι => ℝ) k) c))
    (x z : (fun _ : ι => ℝ) j) (r p : (fun _ : ι => ℝ) k) :
    P.weakPref (tri a j k t x r c) (tri a j k t z p c) :=
  weakPrefComparison_extends_of_denseJKMesh (X := fun _ : ι => ℝ) hjk hjt hkt a c hjoint
    (fun q : ℚ × ℚ => ((q.1 : ℝ) : (fun _ : ι => ℝ) j))
    (fun q : ℚ × ℚ => ((q.2 : ℝ) : (fun _ : ι => ℝ) k))
    (fun q : ℚ × ℚ => ((q.1 : ℝ) : (fun _ : ι => ℝ) j))
    (fun q : ℚ × ℚ => ((q.2 : ℝ) : (fun _ : ι => ℝ) k))
    (realDenseJKMesh (P := P) j k) (realDenseJKMesh (P := P) j k) hmesh x z r p

/-! ## §D.  Soundness gate -/

/-- **Soundness gate (PROVED): the continuity input is necessary under a rep.**

Re-export of `jointWeakPrefClosed_of_additiveRep` (`OptionB_C1aGridTransport` §O):
under a representation with continuous coordinate utilities, the joint `≽`-graph is
closed.  So the §C density closure's topological input hides nothing false.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem jointWeakPrefClosed_necessary
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    (R : AdditiveRep P) (hCont : ∀ i : ι, Continuous (R.V i)) :
    JointWeakPrefClosed P :=
  jointWeakPrefClosed_of_additiveRep R hCont

end ProductPref
end WakkerInfra

/-! ## G3 audit

* §A: `tBlockDiagonalResidue_of_tBlockWeakIndependent` — the guard-drop (residue free
  from the block condition).
* §B: `tBlockDiagonalResidue_blockRoute_is_redundant` — the residue from
  `TBlockWeakIndependent` alone; documents that G2's transport and the naive G3 cover
  are redundant in the block route.
* §C: `weakPrefComparison_extends_of_denseJKMesh`,
  `indiffComparison_extends_of_denseJKMesh`, `weakPrefComparison_extends_real` — the
  genuine §IV.2.6 density closure for the solvability route (fixed-level comparison
  extends from a dense `{j,k}`-mesh; free for ℝ).
* §D: `jointWeakPrefClosed_necessary` — soundness gate.

**Honest scope.**  The block route does not need G2/G3 (§A/§B): the residue is free
from the block conditions.  The density closure (§C) is non-redundant only in the
solvability route, where it *extends* a supplied mesh-comparison — and the
mesh-comparison itself is, by `OptionB_C1aGridTransport` §Q, exactly `KzTransfer` =
the cross-pair crux.  So the single genuine open obligation across G1/G2/G3 is the
cross-pair / block-separability content from bare restricted solvability. -/

#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_tBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_blockRoute_is_redundant
#print axioms WakkerInfra.ProductPref.weakPrefComparison_extends_of_denseJKMesh
#print axioms WakkerInfra.ProductPref.indiffComparison_extends_of_denseJKMesh
#print axioms WakkerInfra.ProductPref.weakPrefComparison_extends_real
#print axioms WakkerInfra.ProductPref.jointWeakPrefClosed_necessary
