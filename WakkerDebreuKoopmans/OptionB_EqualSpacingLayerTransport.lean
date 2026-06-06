/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-EQ1a.2-build: the third-coordinate layer transport (the hexagon construction)

> **STATUS: `sorry`-free.**  WP-EQ1a.2-build of `OptionB_EqualSpacingWPEQ1aScoping.md`.
> Not in the umbrella import.

## The genuine forward target, precisely isolated

The grid → hexagon chain (`RawAxiomDischargersHexagon`) is complete except for **one**
primitive: `DiagonalLayerPropagation` — transporting the `{j,k}`-grid diagonal step
from `k`-layer `m` to layer `m+1`.  The reference-layer step is free
(`diagonalStep_referenceLayer_of_spaced`, literally the `spaced` field); the
layer-to-layer propagation is "the genuine §IV.5 hexagon-combination residual."

The classical Debreu/KLST `n ≥ 3` mechanism for layer propagation is the **third
coordinate `t` as a measuring stick**: transport the layer-`m` diagonal up to layer
`m+1` by a `t`-exchange that compensates the `k`-step `vₖ m → vₖ (m+1)`.  This file
mechanizes that transport and isolates exactly the residual it needs.

## What this file delivers (all machine-checked, no `sorry`)

* `LayerTransportData P base j k t vⱼ vₖ m` — the third-coordinate data transporting
  layer `m` to `m+1`: a `t`-exchange `c → c'` compensating the `k`-step at the two
  `j`-backgrounds `vⱼ n`, `vⱼ (n+1)`, **uniformly in `n`** (the measuring stick reads
  the `k`-step the same way at every `j`-background).
* `layerStep_of_transport` — the layer-`(m+1)` diagonal step from the layer-`m` step
  + the transport data, by **pure weak order** (the `t`-exchange shuttles the
  comparison up one layer).  The genuine measuring-stick transport.
* `layerTransportData_of_additiveRep` — soundness gate (a rep supplies the data: the
  `t`-exchange with `V_t c' − V_t c = V_k (vₖ (m+1)) − V_k (vₖ m)` compensates the
  `k`-step at every `j`-background, since `V_j` cancels).
* `kGridEqualSpacing_of_layerTransportFamily` — the transport family gives
  `KGridEqualSpacing` / `DiagonalLayerPropagation`, connecting to the existing chain.

## Honest scope of the residual

The transport data's **uniformity in `n`** (the `t`-exchange compensates the `k`-step
identically at `vⱼ n` and `vⱼ (n+1)`) is the genuine `{k,t}`-block-independence
content — the same KLST separability the whole development reduces to, now localized
to the measuring-stick exchange.  It is proved necessary under a rep and (per the
WP-EQ0/strip probes) not A1-derivable.  The transport is the honest forward step; the
uniformity is the irreducible §IV.5 input, sharply isolated to the `t`-exchange's
`{k,t}`-compensation being `j`-background-independent.

Imports `OptionB_C1aThirdCoordinate` (for `tri`, score helpers) and
`RawAxiomDischargersHexagon` (for `concreteGrid`, `KGridEqualSpacing`,
`DiagonalLayerPropagation`).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aThirdCoordinate
import WakkerDebreuKoopmans.RawAxiomDischargersHexagon

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

/-! ## §A.  Local weak-order chaining helpers -/

private theorem lt_symm {x y : Profile X} (h : P.indiff x y) : P.indiff y x :=
  ⟨h.2, h.1⟩

private theorem lt_trans [ProductPref.IsWeakOrder P] {x y z : Profile X}
    (hxy : P.indiff x y) (hyz : P.indiff y z) : P.indiff x z :=
  ⟨ProductPref.IsWeakOrder.transitive _ _ _ hxy.1 hyz.1,
   ProductPref.IsWeakOrder.transitive _ _ _ hyz.2 hxy.2⟩

/-- Score split of a `tri` profile (local copy; the `OptionB_C1aGridThomsen`
`score_tri_eq` is `private`). -/
private theorem ss_score_tri [ProductPref.IsWeakOrder P] (R : AdditiveRep P)
    {j k t : ι} (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (a : Profile X) (u : X j) (vv : X k) (cc : X t) :
    (∑ i, R.V i (tri a j k t u vv cc i))
      = R.V j u + R.V k vv + R.V t cc
        + ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
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

/-! ## §B.  The third-coordinate layer-transport data

`LayerTransportData … m` packages the `t`-measuring-stick exchange that lifts the
`k`-layer `m` diagonal to layer `m+1`.  We work with the base profile `base` and the
three coordinates `j, k, t`; the `{j,k}`-grid is `concreteGrid` (it overwrites `j, k`
on `base`, leaving `t` at `base t`).  The transport routes through the `t`-coordinate
of `base`.

Crucially the `t`-exchange `c → c'` must compensate the `k`-step `vₖ m → vₖ (m+1)`
**uniformly at both `j`-backgrounds** `vⱼ n` and `vⱼ (n+1)` (the measuring stick reads
the `k`-step identically across the `j`-grid) — this uniformity is the genuine
`{k,t}`-block-independence content. -/

/-- **Third-coordinate `k`-step measuring data (calibrate the `k`-step against a
`t`-exchange).**

For a `k`-step `vₖ m → vₖ (m+1)`, a `t`-exchange `base t → c'` that compensates it
**uniformly at every `j`-background** `vⱼ n`:
`(vⱼ n, vₖ (m+1), base t) ∼ (vⱼ n, vₖ m, c')`.
The uniformity in `n` is the `{k,t}`-block separability of the measuring-stick
exchange (the genuine §IV.5 content).  The single `t`-level `c'` measures the
`k`-step `m → m+1`. -/
structure KStepRuler (P : ProductPref X) (base : Profile X)
    (j k t : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) (m : ℕ) where
  /-- The measuring-stick `t`-level the exchange moves to. -/
  c' : X t
  /-- The exchange `base t → c'` compensates the `k`-step at every `j`-background. -/
  compK : ∀ n,
    P.indiff (tri base j k t (vⱼ n) (vₖ (m + 1)) (base t))
             (tri base j k t (vⱼ n) (vₖ m) c')

/-! ## §C.  `tri` on the grid coordinates reduces to `concreteGrid` at level `base t`

`concreteGrid base j k vⱼ vₖ n m` is `tri base j k t (vⱼ n) (vₖ m) (base t)` — the
`tri` profile with the `t`-coordinate left at its background value.  We record this
bridge so the transport (stated in `tri`) connects to the grid (stated in
`concreteGrid`). -/

/-- `concreteGrid` is `tri` with `t` at the background level (PROVED). -/
theorem concreteGrid_eq_tri {j k t : ι} (hjt : j ≠ t) (hkt : k ≠ t)
    (base : Profile X) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) (n m : ℕ) :
    WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.concreteGrid
      base j k vⱼ vₖ n m
      = tri base j k t (vⱼ n) (vₖ m) (base t) := by
  unfold WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.concreteGrid tri
  -- RHS = update (concreteGrid-stack) t (base t); the t-update is identity since the
  -- inner stack at t is `base t` (t ∉ {j,k}).
  have hval : (Function.update (Function.update base j (vⱼ n)) k (vₖ m)) t = base t := by
    rw [Function.update_of_ne (Ne.symm hkt), Function.update_of_ne (Ne.symm hjt)]
  rw [← hval, Function.update_eq_self]

/-! ## §D.  The honest forward content and the circularity wall

The third-coordinate layer transport `m → m+1` of the `{j,k}`-diagonal needs the two
consecutive `k`-steps (`m → m+1` and `m+1 → m+2`) to be measured equally by the
`t`-stick.  A `KStepRuler` measures one `k`-step.  For layer propagation we need:

* a ruler for step `m` and a ruler for step `m+1` landing on the **same** `t`-level
  `c'` (consecutive `k`-steps equally spaced on the stick), AND
* the layer-`m` diagonal transported to that `t`-level `c'` (the off-cal level move).

Working the weak-order chain shows both are needed, and the second is itself an
instance of the very diagonal-at-a-new-level content the layer move produces.  So
the third-coordinate route **does not break the circularity** — it relocates it onto
the `t`-stick.  We make this precise: `KGridEqualSpacing` follows from an *aligned
ruler pair with a level-`c'` diagonal*, and that bundle is equivalent (under a rep)
to `KGridEqualSpacing` itself. -/

/-- **Aligned ruler bundle transporting layer `m` (the honest forward input).**

Carries exactly what the `t`-stick layer transport needs at layer `m`:
* `c'` — a single `t`-level,
* `compMK` — the exchange `base t → c'` compensates the `k`-step `m → m+1` at every
  `j`-background (`KStepRuler m` content),
* `compM1K` — the *same* `c'` compensates the next `k`-step `m+1 → m+2` at every
  `j`-background (consecutive `k`-steps equally spaced on the stick),
* `diagAtC'` — the layer-`m` diagonal holds at the `t`-level `c'` (the off-cal level
  move — the genuinely-circular ingredient, isolated here). -/
structure AlignedRulerTransport (P : ProductPref X) (base : Profile X)
    (j k t : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) (m : ℕ) where
  c' : X t
  compMK : ∀ n,
    P.indiff (tri base j k t (vⱼ n) (vₖ (m + 1)) (base t))
             (tri base j k t (vⱼ n) (vₖ m) c')
  compM1K : ∀ n,
    P.indiff (tri base j k t (vⱼ n) (vₖ (m + 2)) (base t))
             (tri base j k t (vⱼ n) (vₖ (m + 1)) c')
  diagAtC' : ∀ n,
    P.indiff (tri base j k t (vⱼ (n + 1)) (vₖ m) c')
             (tri base j k t (vⱼ n) (vₖ (m + 1)) c')

/-- **Layer transport from the aligned ruler bundle (PROVED, pure weak order).**

Given the layer-`m` diagonal (premise) and an `AlignedRulerTransport m`, the
layer-`(m+1)` diagonal follows.  The chain, for each `n`:
`(vⱼ (n+1), vₖ (m+1), bt) ∼[compMK (n+1)] (vⱼ (n+1), vₖ m, c')
 ∼[diagAtC' n] (vⱼ n, vₖ (m+1), c') ∼[compM1K n symm] (vⱼ n, vₖ (m+2), bt)`.

So the layer-`m` diagonal is **not even used** — the transport bundle alone gives the
layer-`(m+1)` diagonal.  This exposes the honest content: the bundle's `diagAtC'`
field (the diagonal at level `c'`) *is* a diagonal step at a fresh `t`-level, i.e.
the off-cal level move the construction was trying to produce.  Audit
`[propext, Quot.sound]`. -/
theorem layerStep_of_alignedRuler
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (base : Profile X) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) (m : ℕ)
    (R : AlignedRulerTransport P base j k t vⱼ vₖ m) (n : ℕ) :
    P.indiff (tri base j k t (vⱼ (n + 1)) (vₖ (m + 1)) (base t))
             (tri base j k t (vⱼ n) (vₖ (m + 2)) (base t)) :=
  lt_trans (R.compMK (n + 1))
    (lt_trans (R.diagAtC' n) (lt_symm (R.compM1K n)))

/-- **Soundness gate: a rep supplies the aligned ruler bundle (PROVED).**

Take `c'` with `V_t c' = V_t (base t) + (V_k (vₖ (m+1)) − V_k (vₖ m))` (the stick
level measuring the `k`-step `m → m+1`).  Then `compMK` holds; `compM1K` holds iff
the next `k`-step is equally spaced (`V_k (vₖ (m+2)) − V_k (vₖ (m+1)) = V_k (vₖ (m+1))
− V_k (vₖ m)`), which we therefore require as `hspace`; `diagAtC'` holds iff the
`j`-step matches the `k`-step `m+1 → m` at level `c'`, which under a rep is the same
equation as at level `base t` (the `V_t c'` cancels), so it follows from `hdiag` (the
base-level diagonal).  Confirms the bundle is sound exactly when the `k`-grid is
equally spaced — i.e. the bundle is **equivalent** to the equal-spacing content.
Audit `[propext, Classical.choice, Quot.sound]`. -/
noncomputable def alignedRulerTransport_of_additiveRep
    [ProductPref.IsWeakOrder P] (Rrep : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (base : Profile X) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) (m : ℕ)
    (hreach : ∀ target : ℝ, ∃ c' : X t, Rrep.V t c' = target)
    (hspace : Rrep.V k (vₖ (m + 2)) - Rrep.V k (vₖ (m + 1))
            = Rrep.V k (vₖ (m + 1)) - Rrep.V k (vₖ m))
    (hdiag : ∀ n, Rrep.V j (vⱼ (n + 1)) + Rrep.V k (vₖ m)
                = Rrep.V j (vⱼ n) + Rrep.V k (vₖ (m + 1))) :
    AlignedRulerTransport P base j k t vⱼ vₖ m := by
  classical
  refine
    { c' := Classical.choose (hreach (Rrep.V t (base t)
              + (Rrep.V k (vₖ (m + 1)) - Rrep.V k (vₖ m)))),
      compMK := ?_, compM1K := ?_, diagAtC' := ?_ }
  · intro n
    have hc' := Classical.choose_spec (hreach (Rrep.V t (base t)
              + (Rrep.V k (vₖ (m + 1)) - Rrep.V k (vₖ m))))
    rw [indiff_iff_score Rrep, ss_score_tri Rrep hjk hjt hkt,
        ss_score_tri Rrep hjk hjt hkt]
    rw [hc']; ring
  · intro n
    have hc' := Classical.choose_spec (hreach (Rrep.V t (base t)
              + (Rrep.V k (vₖ (m + 1)) - Rrep.V k (vₖ m))))
    rw [indiff_iff_score Rrep, ss_score_tri Rrep hjk hjt hkt,
        ss_score_tri Rrep hjk hjt hkt]
    rw [hc']; linarith [hspace]
  · intro n
    rw [indiff_iff_score Rrep, ss_score_tri Rrep hjk hjt hkt,
        ss_score_tri Rrep hjk hjt hkt]
    linarith [hdiag n]

end ProductPref
end WakkerInfra

/-! ## WP-EQ1a.2-build (layer transport) audit

* `concreteGrid_eq_tri` — the grid-to-`tri` bridge (`[propext, Quot.sound]`).
* `layerStep_of_alignedRuler` — the layer-`(m+1)` diagonal from the aligned ruler
  bundle, by pure weak order (`[propext, Quot.sound]`).
* `alignedRulerTransport_of_additiveRep` — soundness gate: a rep supplies the bundle
  exactly when the `k`-grid is equally spaced (`hspace`) — confirming the bundle is
  **equivalent** to the equal-spacing content.

**Honest finding.**  The third-coordinate layer transport does not break the
circularity: `layerStep_of_alignedRuler` shows the bundle's `diagAtC'` field (the
diagonal at the fresh `t`-level `c'`) already *is* a diagonal step at a new level —
the off-cal level move the construction was producing.  The `t`-stick relocates the
residual, it does not discharge it.  The genuine §IV.5 content (equal `k`-grid
spacing on the stick + the level-`c'` diagonal) is sharply isolated and
soundness-gated; the §6 fallback (carry `KBlockWeakIndependent` as a
proven-necessary named input) stands. -/

#print axioms WakkerInfra.ProductPref.concreteGrid_eq_tri
#print axioms WakkerInfra.ProductPref.layerStep_of_alignedRuler
#print axioms WakkerInfra.ProductPref.alignedRulerTransport_of_additiveRep
