/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — reducing the cross-pair frontier's two continuum quantifiers to dense sets

> **STATUS: `sorry`-free forward bricks on the R1.1 cross-pair frontier.**  Not in
> the umbrella import; audited by `OptionB_AxiomCheck.lean`.

## What this file does (and, honestly, does not)

The genuine open content of the hexagon is the cross-pair trade-off transitivity
`CrossPairTradeoffTransitivity P j k t` (= `KzTransfer`, `OptionB_C1aGridTransport`
§Q): from `P1 : (j:x→y) ≡ (k:q→p)` and `J2 : (j:x→y) ≡ (t:w→c)`, conclude
`Kz : (k:q→p) ≡ (t:w→c)` **at every anchor `j`-value `z`**, i.e.
`[z|q|c] ∼ [z|p|w]` for all `z`.  The cross-pair frontier carries **two** continuum
universal quantifiers — the anchor `z` and the `t`-level `c` — and this file
discharges **both** from dense subsets by preference continuity.

### §C–E. The anchor quantifier

The two premises `P1`, `J2` **do not mention the anchor `z`** — they pin the
trade-off `(k:q→p) ≡ (t:w→c)` once and for all.  So the conclusion is a single
`z`-parametrised indifference between the two continuous slice maps

* `F z := [z|q|c] = tri a j k t z q (a t)` and
* `G z := [z|p|w] = tri a j k t z p w`.

Therefore, **by preference continuity** (the joint `≽`-graph is closed,
`JointWeakPrefClosed`, §O of `OptionB_C1aGridTransport`), the conclusion holds for
*all* anchors `z` as soon as it holds for a *dense set* `D` of anchors —
`indiff_extends_of_dense` is exactly this closure
(`crossPairTradeoffTransitivity_of_denseAnchors`).

### §F. The `t`-level quantifier (the equal-spacing level move)

The grid-Thomsen *diagonal step* at level `c` is `[u₁|v₁|c] ∼ [u₂|v₂|c]`, and the
two sides are continuous **in `c`** (only the outermost `t`-update varies).  So the
`{j,k}`-comparison also extends from a dense set of `t`-levels to all levels
(`indiff_allLevels_of_denseLevels`).  This is a *forward-construction* tool: it
lets a measuring-stick construction establish the diagonal step on a dense
(rational) set of levels and conclude it everywhere — it is **not** a reduction of
the level-independent `StripTransfer` residual (whose premise gives only a *single*
level, not a dense set).

**These are genuine, non-circular forward steps.**  The new input is *continuity*
(`JointWeakPrefClosed`, soundness-gated by `jointWeakPrefClosed_of_additiveRep`),
**not** the cross-pair content: the §D.2b circularity (deriving the cross-pair
residue from the permutation-equivalent diagonal residues) is avoided entirely —
we discharge only the *anchor* and *level* universal quantifiers.

**What this does NOT do.**  It does not close the hexagon.  The genuine cross-pair
*magnitude-matching* content (that the `{k,t}` trade-off equals the `{j,k}` one, the
content the additive scale `δ` composes) is untouched — it survives as the residue
restricted to a dense `{j,k}`-grid at dense `t`-levels.  For ℝ-coordinates that is
a **countable, rational** obligation (`*_of_rationalAnchors`, `*_of_rationalLevels`);
the equal-spacing magnitude content on that rational grid remains the multi-week
Wakker §IV.5 frontier.

Imports `OptionB_C1aGridTransport` (for `tri`, `CrossPairTradeoffTransitivity`,
`JointWeakPrefClosed`, `indiff_extends_of_dense`, `weakPref_extends_of_dense`,
`continuous_jkSliceMap`, and the soundness gates) and is **not** in the umbrella
import.
-/

import WakkerDebreuKoopmans.OptionB_C1aGridTransport

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

/-! ## §A.  The anchor-restricted cross-pair hexagon -/

/-- **Cross-pair trade-off transitivity restricted to a set of anchors `D ⊆ X j`.**

Identical to `CrossPairTradeoffTransitivity` except the conclusion `[z|q|c] ∼ [z|p|w]`
is asserted only for anchor `j`-values `z ∈ D` (the premises `P1`, `J2` never
mention `z`).  Taking `D = Set.univ` recovers the full residual
(`crossPairTradeoffTransitivity_iff_onAnchors_univ`). -/
def CrossPairTradeoffTransitivityOnAnchors (P : ProductPref X) (j k t : ι)
    (D : Set (X j)) : Prop :=
  ∀ (a : Profile X) (x y : X j) (p q r : X k) (w : X t),
    P.indiff (tri a j k t x q (a t)) (tri a j k t y p (a t)) →   -- P1 : (j:x→y) ≡ (k:q→p)
    P.indiff (tri a j k t x r w) (tri a j k t y r (a t)) →       -- J2 : (j:x→y) ≡ (t:w→c)
    ∀ z ∈ D, P.indiff (tri a j k t z q (a t)) (tri a j k t z p w) -- Kz at anchor z

/-- **The full residual is the `Set.univ` anchor restriction (PROVED, definitional).**

Confirms `CrossPairTradeoffTransitivityOnAnchors` is the honest generalisation:
at `D = univ` it is exactly `CrossPairTradeoffTransitivity`.  Audit `[propext]`. -/
theorem crossPairTradeoffTransitivity_iff_onAnchors_univ {j k t : ι} :
    CrossPairTradeoffTransitivity P j k t ↔
      CrossPairTradeoffTransitivityOnAnchors P j k t Set.univ := by
  constructor
  · intro h a x y p q r w hP1 hJ2 z _hz
    exact h a x y z p q r w hP1 hJ2
  · intro h a x y z p q r w hP1 hJ2
    exact h a x y p q r w hP1 hJ2 z (Set.mem_univ z)

/-! ## §B.  Continuity of the single-anchor slice maps -/

/-- **The single-anchor slice map `z ↦ [z|v|c]` is continuous.**

`fun z => tri a j k t z v c` is `jkSliceMap a j k t c ∘ (fun z => (z, v))`, a
composition of the (proved-continuous) two-coordinate slice map with the continuous
`z ↦ (z, v)`.  Audit `[propext]`. -/
theorem continuous_anchorSliceMap [∀ i, TopologicalSpace (X i)]
    (a : Profile X) (j k t : ι) (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (v : X k) (c : X t) :
    Continuous (fun z : X j => tri a j k t z v c) :=
  (continuous_jkSliceMap a j k t hjk hjt hkt c).comp
    (continuous_id.prodMk continuous_const)

/-! ## §C.  The anchor-continuum reduction (the forward step) -/

/-- **Cross-pair hexagon over all anchors from a dense set of anchors (PROVED).**

The forward step: `CrossPairTradeoffTransitivity P j k t` (the conclusion at *every*
anchor `z`) follows from its restriction to a **dense** set `D` of anchors, given
the joint `≽`-graph is closed (preference continuity, `JointWeakPrefClosed`).

For each fixed trade-off (premises `P1`, `J2`), the conclusion `[z|q|c] ∼ [z|p|w]`
is an indifference between the continuous slice maps `z ↦ [z|q|c]` and
`z ↦ [z|p|w]`; it holds on the dense `D` by `hAnchors`, so the comparison-map
closure `indiff_extends_of_dense` extends it to all `z`.

**Non-circular:** the only structural input beyond the dense-anchor residue is
preference continuity — *not* the cross-pair magnitude content (§D.2b circularity
avoided).  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem crossPairTradeoffTransitivity_of_denseAnchors
    [∀ i, TopologicalSpace (X i)] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hjoint : JointWeakPrefClosed P)
    {D : Set (X j)} (hdense : Dense D)
    (hAnchors : CrossPairTradeoffTransitivityOnAnchors P j k t D) :
    CrossPairTradeoffTransitivity P j k t := by
  intro a x y z p q r w hP1 hJ2
  exact indiff_extends_of_dense
    (fun z => tri a j k t z q (a t)) (fun z => tri a j k t z p w)
    (continuous_anchorSliceMap a j k t hjk hjt hkt q (a t))
    (continuous_anchorSliceMap a j k t hjk hjt hkt p w)
    hjoint hdense
    (fun z hz => hAnchors a x y p q r w hP1 hJ2 z hz)
    z

/-- **`KzTransfer` over all anchors from a dense set of anchors (PROVED).**

The same reduction stated in the `KzTransfer` vocabulary (recall
`kzTransfer_iff_crossPairTradeoffTransitivity`): the matching residual `KzTransfer`
follows from its dense-anchor restriction + preference continuity.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem kzTransfer_of_denseAnchors
    [∀ i, TopologicalSpace (X i)] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hjoint : JointWeakPrefClosed P)
    {D : Set (X j)} (hdense : Dense D)
    (hAnchors : CrossPairTradeoffTransitivityOnAnchors P j k t D) :
    KzTransfer P j k t :=
  (kzTransfer_iff_crossPairTradeoffTransitivity).mpr
    (crossPairTradeoffTransitivity_of_denseAnchors hjk hjt hkt hjoint hdense hAnchors)

/-! ## §D.  Soundness gates -/

/-- **Soundness gate: the dense-anchor residue is necessary under a rep (PROVED).**

Every additive representation supplies the full cross-pair transitivity
(`crossPairTradeoffTransitivity_of_additiveRep`), hence its anchor restriction to
any `D`.  Confirms the dense-anchor target hides nothing false.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem crossPairTradeoffTransitivityOnAnchors_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) (D : Set (X j)) :
    CrossPairTradeoffTransitivityOnAnchors P j k t D := by
  intro a x y p q r w hP1 hJ2 z _hz
  exact crossPairTradeoffTransitivity_of_additiveRep R hjk hjt hkt a x y z p q r w hP1 hJ2

/-! ## §E.  The ℝ-coordinate corollary: rational anchors suffice

For the project's Debreu–Koopmans setting (`X i = ℝ` for all `i`) the rational
casts are dense (`Rat.denseRange_cast`), so the cross-pair hexagon over all real
anchors reduces to the hexagon over **rational** anchors — the §IV.2.6 density that
is *free* for ℝ-coordinates (cf. `OptionB_C1aGridTransport` §P), with continuity
the only genuine input. -/

/-- **ℝ-coordinates: rational anchors suffice for the cross-pair hexagon (PROVED).**

With real coordinates and the joint graph closed, `CrossPairTradeoffTransitivity`
follows from its restriction to the dense set of rational anchors `Set.range ((↑) :
ℚ → ℝ)`.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem crossPairTradeoffTransitivity_of_rationalAnchors
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {P : ProductPref (fun _ : ι => ℝ)} {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hjoint : JointWeakPrefClosed P)
    (hAnchors : CrossPairTradeoffTransitivityOnAnchors P j k t
      (Set.range ((↑) : ℚ → ℝ))) :
    CrossPairTradeoffTransitivity P j k t :=
  crossPairTradeoffTransitivity_of_denseAnchors hjk hjt hkt hjoint
    Rat.denseRange_cast hAnchors

/-! ## §F.  The t-level continuum reduction (the equal-spacing level move)

The cross-pair frontier has a second continuum quantifier: the **t-level move**.
The grid-Thomsen *diagonal step* at level `c` is
`[u₁|v₁|c] ∼ [u₂|v₂|c]` (`GridDiagonalStepOffCal`), and the `StripTransfer`
residual is the same `{j,k}`-comparison's independence of the common `t`-level `c`.
For fixed `{j,k}`-data the two sides `c ↦ [u₁|v₁|c]` and `c ↦ [u₂|v₂|c]` are
**continuous in `c`** (only the outermost `t`-update varies), so — exactly as for
anchors — the comparison extends from a **dense set of levels** to all levels by
preference continuity.

This is the level-move analogue of §C–E: it discharges the *level* universal
quantifier of the diagonal step / strip, non-circularly (continuity, not the
diagonal residues).  For ℝ-coordinates the equal-spacing level move thus reduces to
its restriction to **rational** levels — a countable obligation. -/

/-- **The single-`{j,k}` `t`-level slice map `c ↦ [u|v|c]` is continuous.**

`fun c => tri a j k t u v c` updates only coordinate `t` by `c`; every other
coordinate is constant in `c`.  Audit `[propext]`. -/
theorem continuous_tSliceMap [∀ i, TopologicalSpace (X i)]
    (a : Profile X) (j k t : ι) (u : X j) (v : X k) :
    Continuous (fun c : X t => tri a j k t u v c) := by
  refine continuous_pi (fun i => ?_)
  unfold tri
  by_cases hit : i = t
  · subst hit
    simp only [Function.update_self]
    exact continuous_id
  · simp only [Function.update_of_ne hit]
    exact continuous_const

/-- **The `{j,k}`-comparison at all `t`-levels from a dense set of levels (PROVED).**

For fixed `{j,k}`-data `(u₁,v₁)`, `(u₂,v₂)`, if `[u₁|v₁|c] ∼ [u₂|v₂|c]` holds on a
**dense** set `D` of `t`-levels and the joint `≽`-graph is closed
(`JointWeakPrefClosed`), then it holds at **every** level `c`.

This is the `t`-level analogue of `crossPairTradeoffTransitivity_of_denseAnchors`:
the two sides are continuous in `c` (`continuous_tSliceMap`), so the §O
comparison-map closure `indiff_extends_of_dense` extends the agreement.  It
discharges the level universal quantifier of the equal-spacing diagonal step /
`StripTransfer`, non-circularly (continuity only).  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem indiff_allLevels_of_denseLevels
    [∀ i, TopologicalSpace (X i)] {j k t : ι}
    (a : Profile X) (u₁ : X j) (v₁ : X k) (u₂ : X j) (v₂ : X k)
    (hjoint : JointWeakPrefClosed P)
    {D : Set (X t)} (hdense : Dense D)
    (hagree : ∀ c ∈ D, P.indiff (tri a j k t u₁ v₁ c) (tri a j k t u₂ v₂ c))
    (c : X t) :
    P.indiff (tri a j k t u₁ v₁ c) (tri a j k t u₂ v₂ c) :=
  indiff_extends_of_dense
    (fun c => tri a j k t u₁ v₁ c) (fun c => tri a j k t u₂ v₂ c)
    (continuous_tSliceMap a j k t u₁ v₁) (continuous_tSliceMap a j k t u₂ v₂)
    hjoint hdense hagree c

/-- **The `{j,k}`-comparison at all `t`-levels from a dense set of levels, one
direction (PROVED).**

The `weakPref` form, for transferring `≽`-comparisons (e.g. the diagonal step in
its preference form) across the level continuum from a dense set.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem weakPref_allLevels_of_denseLevels
    [∀ i, TopologicalSpace (X i)] {j k t : ι}
    (a : Profile X) (u₁ : X j) (v₁ : X k) (u₂ : X j) (v₂ : X k)
    (hjoint : JointWeakPrefClosed P)
    {D : Set (X t)} (hdense : Dense D)
    (hagree : ∀ c ∈ D, P.weakPref (tri a j k t u₁ v₁ c) (tri a j k t u₂ v₂ c))
    (c : X t) :
    P.weakPref (tri a j k t u₁ v₁ c) (tri a j k t u₂ v₂ c) :=
  weakPref_extends_of_dense
    (fun c => tri a j k t u₁ v₁ c) (fun c => tri a j k t u₂ v₂ c)
    (continuous_tSliceMap a j k t u₁ v₁) (continuous_tSliceMap a j k t u₂ v₂)
    hjoint hdense hagree c

/-- **ℝ-coordinates: rational `t`-levels suffice for the `{j,k}`-comparison (PROVED).**

With real coordinates and the joint graph closed, the `{j,k}`-comparison at all
levels follows from its restriction to the dense set of rational levels.  So the
equal-spacing level move reduces to a countable (rational) obligation.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem indiff_allLevels_of_rationalLevels
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {P : ProductPref (fun _ : ι => ℝ)} {j k t : ι}
    (a : Profile (fun _ : ι => ℝ)) (u₁ v₁ u₂ v₂ : ℝ)
    (hjoint : JointWeakPrefClosed P)
    (hagree : ∀ c ∈ Set.range ((↑) : ℚ → ℝ),
      P.indiff (tri a j k t u₁ v₁ c) (tri a j k t u₂ v₂ c))
    (c : ℝ) :
    P.indiff (tri a j k t u₁ v₁ c) (tri a j k t u₂ v₂ c) :=
  indiff_allLevels_of_denseLevels a u₁ v₁ u₂ v₂ hjoint Rat.denseRange_cast hagree c

end ProductPref
end WakkerInfra

/-! ## Audit — the anchor- and level-continuum reductions are `sorry`-free.

The cross-pair frontier's two continuum quantifiers are discharged from dense sets
by preference continuity (`JointWeakPrefClosed`), non-circularly (no appeal to the
permutation-equivalent diagonal residues):

* **anchor** quantifier (§C–E): `crossPairTradeoffTransitivity_of_denseAnchors`;
* **`t`-level** quantifier (§F, the equal-spacing level move):
  `indiff_allLevels_of_denseLevels`.

For ℝ-coordinates both reduce to rational restrictions
(`*_of_rationalAnchors`, `*_of_rationalLevels`).  The cross-pair
*magnitude-matching* content (the residue on the dense rational grid) remains the
genuine §IV.5 frontier. -/

#print axioms WakkerInfra.ProductPref.crossPairTradeoffTransitivity_iff_onAnchors_univ
#print axioms WakkerInfra.ProductPref.continuous_anchorSliceMap
#print axioms WakkerInfra.ProductPref.crossPairTradeoffTransitivity_of_denseAnchors
#print axioms WakkerInfra.ProductPref.kzTransfer_of_denseAnchors
#print axioms WakkerInfra.ProductPref.crossPairTradeoffTransitivityOnAnchors_of_additiveRep
#print axioms WakkerInfra.ProductPref.crossPairTradeoffTransitivity_of_rationalAnchors
#print axioms WakkerInfra.ProductPref.continuous_tSliceMap
#print axioms WakkerInfra.ProductPref.indiff_allLevels_of_denseLevels
#print axioms WakkerInfra.ProductPref.weakPref_allLevels_of_denseLevels
#print axioms WakkerInfra.ProductPref.indiff_allLevels_of_rationalLevels
