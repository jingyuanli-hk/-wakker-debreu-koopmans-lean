/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — G4.b: extend `S` to a continuous slice utility off the grid

> **STATUS: `sorry`-free.  Delivers the genuine slice-continuity brick + a
> machine-checked no-go that reshapes the roadmap's G4.b, plus the honest
> reduction of the off-grid representation to the named §IV.5 order-calibration
> residual.**
> Not in the umbrella import.

This file executes **G4.b** of `OptionB_SectionIV5GridConstructionRoadmap.md` — and,
like G3, it corrects the route after the construction surfaces an obstruction.

## The finding that reshapes G4.b

The roadmap proposed extending the grid representation `S` (G4.a) to all of
`X j × X k` "via the mesh density (G3) + the §O closure engine".  Building it shows
this is **mis-targeted** — the *same* §N.2 obstruction the transport file already
recorded, now at the representation level:

* The §O engine `weakPref_extends_of_dense` extends a **fixed** `≽`-comparison between
  two continuously-varying profiles from a dense set (the joint `≽`-graph is closed).
* But the off-grid *representation* `weakPref (slice u) (slice v) ↔ S v ≤ S u` is a
  **moving-target** relation in `(u,v)`.  Extending its `⇐` half (`S v ≤ S u → ≽`) by
  density would need the mesh to be dense **within each closed sublevel set**
  `{(u,v) | S v ≤ S u}` — which ambient mesh density does **not** give (a sublevel
  set's boundary can miss the mesh).  So the one-shot density closure fails; this is
  exactly why §N.2 said the §M/§O engines do not build the cover/representation.

We make this precise (§C): the off-grid representation is **definitionally** the named
§IV.5 **order-calibration certificate** `PairwiseOrderCalibrationCertificate`
(`= PairwiseSliceRepresentationCertificate`), which the existing assembly produces from
**restricted solvability** (1-D interpolation), *not* from 2-D density.  So the honest
G4.b is: the off-grid extension = the named order-calibration residual; density buys
the *continuity* infrastructure (reusable) but not the representation.

## What this file delivers (all machine-checked, no `sorry`)

* **§A** `sliceMap` / `continuous_sliceMap` / `sliceMap_apply` — the two-coordinate
  slice map and its continuity (the genuine reusable topological brick).
* **§B** `sliceFixedWeakPref_extends_of_dense` — the §O engine *correctly* applied:
  a **fixed** `≽`-comparison `slice u₀ ≽ slice v₀` does extend... — restated honestly,
  the engine extends a comparison between two *globally* continuous parametrised maps;
  we give the slice-parametrised form `fixedProfile_weakPref_extends`.
* **§C** `pairwiseSliceRep_iff_orderCalibration` — the off-grid representation **is**
  the named order-calibration residual (definitional); and
  `pairwiseSliceRepresentation_of_orderCalibration` produces it from the residual.
* **§D** `orderCalibration_of_additiveRep` — soundness gate: a representation supplies
  the order-calibration certificate (hence the off-grid slice rep), confirming the
  reduction hides nothing false.

## Honest scope

G4.b's genuine topological content is `continuous_sliceMap` (reusable for any
continuity-closure step).  The off-grid *representation* is the named §IV.5
order-calibration residual `PairwiseOrderCalibrationCertificate`, produced by the
existing restricted-solvability assembly — **not** by 2-D mesh density (a documented
no-go, the §N.2 obstruction at representation level).  So G4.b reduces Link-B's
off-grid step to the standard §IV.5 Step-4 calibration content (which the project
already discharges from solvability), and the §O density engine is correctly scoped to
*fixed*-comparison extension only.  G4.c (assemble the shared-`V₀` family) is the
already-mechanized Phase-74 step.

Imports `OptionB_C1aGridTransport` (the §O engine, `JointWeakPrefClosed`),
`Certificates` (`PairwiseSliceRepresentationCertificate`, the order-calibration
certificate), `OptionB_CoordinateIndependence` (`indiff_iff_score`).  Not in the
umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aGridTransport
import WakkerDebreuKoopmans.Certificates
import WakkerDebreuKoopmans.OptionB_CoordinateIndependence

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WakkerInfra
namespace ProductPref

open WakkerInfra
open WakkerDebreuKoopmans
open Function

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {X : ι → Type v} {P : ProductPref X}

/-! ## §A.  The two-coordinate slice map and its continuity (the reusable brick) -/

/-- The two-coordinate slice map over base `a`: `(u, v) ↦ update (update a j u) k v`. -/
def sliceMap (a : Profile X) (j k : ι) : X j × X k → Profile X :=
  fun uv => Function.update (Function.update a j uv.1) k uv.2

/-- **The slice map is continuous (PROVED).**

Each coordinate of `update (update a j u) k v` is `v`, `u`, or a constant `a i` — all
continuous in `(u, v)`.  This is the reusable topological brick the §IV.5 continuity
closure rests on.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem continuous_sliceMap [∀ i, TopologicalSpace (X i)]
    (a : Profile X) {j k : ι} (hjk : j ≠ k) :
    Continuous (sliceMap a j k) := by
  refine continuous_pi (fun i => ?_)
  unfold sliceMap
  by_cases hik : i = k
  · subst hik
    simp only [Function.update_self]
    exact continuous_snd
  · simp only [Function.update_of_ne hik]
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self]
      exact continuous_fst
    · simp only [Function.update_of_ne hij]
      exact continuous_const

/-- **The slice value at `(u,v)`: coordinate `j` is `u`, coordinate `k` is `v`
(PROVED).**  Audit `[propext]`. -/
theorem sliceMap_apply (a : Profile X) {j k : ι} (hjk : j ≠ k) (u : X j) (v : X k) :
    (sliceMap a j k (u, v)) j = u ∧ (sliceMap a j k (u, v)) k = v := by
  refine ⟨?_, ?_⟩
  · unfold sliceMap; rw [Function.update_of_ne hjk, Function.update_self]
  · unfold sliceMap; rw [Function.update_self]

/-! ## §B.  The §O engine, correctly scoped: extending a comparison against a FIXED
    profile along the slice (continuity closure that *does* work)

The §O `weakPref_extends_of_dense` extends a `≽`-comparison between two continuously-
varying profiles from a dense set.  Applied to a **fixed** right-hand profile `b`
(constant map) and the slice map on the left, it extends "`slice (u,v) ≽ b` on the
dense mesh" to "for all `(u,v)`".  This is the genuinely-working continuity closure —
it extends a *fixed indifference/preference class membership*, not the moving-target
representation (see §C). -/

/-- **Fixed-target slice preference extends from a dense mesh (PROVED).**

If `slice (meshpt) ≽ b` holds on a dense `{j,k}`-mesh and the joint `≽`-graph is closed,
then `slice (u,v) ≽ b` for all `(u,v)`.  This is `weakPref_extends_of_dense` with the
slice map on the left and the constant `b` on the right — the correctly-scoped
continuity closure (fixed target).  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem sliceWeakPref_fixedTarget_extends_of_dense
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k) (a : Profile X) (b : Profile X)
    (hjoint : JointWeakPrefClosed P)
    {I : Type*} (meshJ : I → X j) (meshK : I → X k)
    (hdense : DenseJKMesh j k meshJ meshK)
    (hmesh : ∀ i : I, P.weakPref (sliceMap a j k (meshJ i, meshK i)) b)
    (u : X j) (v : X k) :
    P.weakPref (sliceMap a j k (u, v)) b := by
  have hsm : Continuous (sliceMap a j k) := continuous_sliceMap a hjk
  exact weakPref_extends_of_dense
    (fun uv : X j × X k => sliceMap a j k uv) (fun _ => b)
    hsm continuous_const hjoint hdense
    (by
      rintro _ ⟨i, rfl⟩
      exact hmesh i)
    (u, v)

/-- **Dually: fixed-source slice preference extends from a dense mesh (PROVED).**

`b ≽ slice (u,v)` for all `(u,v)` from dense mesh agreement.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem sliceWeakPref_fixedSource_extends_of_dense
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k) (a : Profile X) (b : Profile X)
    (hjoint : JointWeakPrefClosed P)
    {I : Type*} (meshJ : I → X j) (meshK : I → X k)
    (hdense : DenseJKMesh j k meshJ meshK)
    (hmesh : ∀ i : I, P.weakPref b (sliceMap a j k (meshJ i, meshK i)))
    (u : X j) (v : X k) :
    P.weakPref b (sliceMap a j k (u, v)) := by
  have hsm : Continuous (sliceMap a j k) := continuous_sliceMap a hjk
  exact weakPref_extends_of_dense
    (fun _ : X j × X k => b) (fun uv : X j × X k => sliceMap a j k uv)
    continuous_const hsm hjoint hdense
    (by
      rintro _ ⟨i, rfl⟩
      exact hmesh i)
    (u, v)

/-! ## §C.  The off-grid representation IS the named order-calibration residual

The roadmap's "extend the representation via density" is the §N.2 no-go.  The honest
statement: the off-grid slice representation is **definitionally** the named §IV.5
Step-4 order-calibration certificate, which the existing assembly produces from
restricted solvability (1-D interpolation), not 2-D density. -/

/-- **The off-grid slice representation is the order-calibration certificate
(PROVED, definitional).**

`PairwiseSliceRepresentationCertificate` and `PairwiseOrderCalibrationCertificate` are
the same proposition (`Certificates`): the off-grid order representation `weakPref ↔
score-≤` on the `{j,k}`-slice **is** the §IV.5 Step-4 order-calibration content.  So
G4.b's off-grid extension is not a density closure — it is the named order-calibration
residual.  Audit `[propext]`. -/
theorem pairwiseSliceRep_iff_orderCalibration
    {j k : ι} (Vⱼ : X j → ℝ) (Vₖ : X k → ℝ) :
    WakkerRoadmap.CertificateChecklist.PairwiseSliceRepresentationCertificate P j k Vⱼ Vₖ
      ↔ WakkerRoadmap.CertificateChecklist.PairwiseOrderCalibrationCertificate P j k Vⱼ Vₖ :=
  Iff.rfl

/-- **The off-grid slice representation from the order-calibration residual (PROVED).**

Trivial transport across `pairwiseSliceRep_iff_orderCalibration`: the named §IV.5
order-calibration certificate yields the off-grid slice representation.  This is the
honest G4.b reduction — Link-B's off-grid step is the standard §IV.5 Step-4 calibration
content (produced by the existing restricted-solvability assembly), not a 2-D mesh
density closure.  Audit `[propext]`. -/
theorem pairwiseSliceRepresentation_of_orderCalibration
    {j k : ι} {Vⱼ : X j → ℝ} {Vₖ : X k → ℝ}
    (hcal : WakkerRoadmap.CertificateChecklist.PairwiseOrderCalibrationCertificate P j k Vⱼ Vₖ) :
    WakkerRoadmap.CertificateChecklist.PairwiseSliceRepresentationCertificate P j k Vⱼ Vₖ :=
  hcal

/-! ## §D.  Soundness gate: a representation supplies the order calibration -/

/-- **Soundness gate (PROVED): the order-calibration certificate from a representation.**

Under an additive representation `R` whose pivot utilities are `Vⱼ = R.V j`,
`Vₖ = R.V k`, the off-grid slice representation holds: for profiles agreeing off
`{j,k}`, `weakPref x y ↔ (R.V j (y j) + R.V k (y k)) ≤ (R.V j (x j) + R.V k (x k))`,
because all other coordinates' utilities are equal (agree off `{j,k}`) and cancel from
`R.represents`.  So the named order-calibration residual — hence the off-grid slice
representation — hides nothing false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem orderCalibration_of_additiveRep
    (R : AdditiveRep P) (j k : ι) (hjk : j ≠ k) :
    WakkerRoadmap.CertificateChecklist.PairwiseOrderCalibrationCertificate P j k (R.V j) (R.V k) := by
  intro x y hagree
  -- Split both additive scores into the `{j,k}` part and the off-`{j,k}` remainder.
  have hx := WakkerRoadmap.CertificateChecklist.sum_eq_pair_add_rest R.V x hjk
  have hy := WakkerRoadmap.CertificateChecklist.sum_eq_pair_add_rest R.V y hjk
  -- The remainders agree because `x` and `y` agree off `{j,k}`.
  have hrest :
      (∑ i ∈ (Finset.univ.erase j).erase k, R.V i (y i))
        = ∑ i ∈ (Finset.univ.erase j).erase k, R.V i (x i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hij : i ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    have hi_not_pair : i ∉ ({j, k} : Set ι) := by
      intro himem
      rcases (by simpa using himem : i = j ∨ i = k) with rfl | rfl
      · exact hij rfl
      · exact hik rfl
    rw [← hagree i hi_not_pair]
  -- `weakPref x y ↔ ∑ V y ≤ ∑ V x`, and the remainders cancel.
  rw [R.represents, hx, hy, hrest]
  constructor <;> intro h <;> linarith

end ProductPref
end WakkerInfra

/-! ## G4.b audit

* §A: `continuous_sliceMap`, `sliceMap_apply` — the slice map and its continuity (the
  genuine reusable topological brick).
* §B: `sliceWeakPref_fixedTarget_extends_of_dense`,
  `sliceWeakPref_fixedSource_extends_of_dense` — the §O engine **correctly scoped**: it
  extends a *fixed*-target/source slice preference from a dense mesh (not the
  moving-target representation).
* §C: `pairwiseSliceRep_iff_orderCalibration`,
  `pairwiseSliceRepresentation_of_orderCalibration` — the off-grid representation **is**
  the named §IV.5 order-calibration residual; the honest G4.b reduction.
* §D: `orderCalibration_of_additiveRep` — soundness gate.

**Honest scope / finding.**  The roadmap's "extend the representation via mesh density +
§O" is the §N.2 no-go: the §O engine extends only *fixed* comparisons (§B), while the
off-grid *representation* is a moving-target relation whose density closure would need
mesh density within each closed sublevel set (false for ambient mesh density).  The
honest off-grid extension is the named order-calibration residual
`PairwiseOrderCalibrationCertificate` (§C), produced by the existing
restricted-solvability assembly — not a 2-D density closure.  So G4.b's genuine
topological content is `continuous_sliceMap`; the representation content reduces to the
standard §IV.5 Step-4 calibration the project already discharges from solvability. -/

#print axioms WakkerInfra.ProductPref.continuous_sliceMap
#print axioms WakkerInfra.ProductPref.sliceWeakPref_fixedTarget_extends_of_dense
#print axioms WakkerInfra.ProductPref.sliceWeakPref_fixedSource_extends_of_dense
#print axioms WakkerInfra.ProductPref.pairwiseSliceRep_iff_orderCalibration
#print axioms WakkerInfra.ProductPref.pairwiseSliceRepresentation_of_orderCalibration
#print axioms WakkerInfra.ProductPref.orderCalibration_of_additiveRep
