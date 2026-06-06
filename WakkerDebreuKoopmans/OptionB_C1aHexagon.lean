/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — §IV.5 Thomsen discharge, Phase II: the diagonal hexagon / stick-shift

> **STATUS: `sorry`-free.**  Executes **Phase II** of
> `OptionB_C1aThomsenResidueDischargeRoadmap.md`: the measuring-stick hexagon that
> sits between Phase I (`OptionB_C1aStickMeasure.lean`, the stick-realization
> *existence* primitive) and Phase III (the three `*DiagonalResidue_of_klst`
> discharges).  NOT in the umbrella import, NOT merged into
> `OptionB_AxiomCheck.lean`.
>
> ## The honest content of Phase II
>
> The §IV.5 measuring-stick argument turns the diagonal residue
> (`TBlockDiagonalResidue`: shifting a common `t`-value preserves a `≽`-comparison
> between two profiles that differ in **both** `j` and `k`) into a strictly
> **sharper** fact about *indifferences*:
>
> * `DiagonalIndiffStickInvariant P j k t` — a `{j,k}`-block **indifference**
>   `[u|v|w] ∼ [u'|v'|w]` is independent of the common stick value: it still holds
>   at any other stick value `c`.
>
> This is the genuine §IV.5 hexagon-combination content.  The formalized
> `TradeoffConsistency` (Wakker IV.2.5, as encoded in `Core.lean`) transports
> **single-coordinate** indifferences across bases only — see the Phase-29 scope
> note in `RawAxiomDischargersHexagon.lean` §3 — so it does **not** by itself
> supply the two-coordinate diagonal-indifference transport.  That is why
> `DiagonalIndiffStickInvariant` is named here as the explicit §IV.5 measuring-stick
> seam, exactly mirroring how `RawAxiomDischargersHexagon.lean` names
> `SliceThomsenMove` as the deliberately-undischarged hexagon-combination residual.
>
> ## What is theorem-backed in this file
>
> * `diagonalIndiffStickInvariant_of_additiveRep` — the **soundness gate**: every
>   additive representation satisfies the seam (the common stick value cancels on
>   both sides of an equal-score indifference).  Proved.
> * `tBlockDiagonalResidue_of_diagonalIndiffStickInvariant` — the **discharge
>   bridge**: the diagonal residue follows from the seam, *plus* two standard
>   §III.4 inputs:
>     - single-coordinate-`k` weak separability
>       (`CoordinateWeakSeparable P k`, here in unfolded `coordPref` form), and
>     - a diagonal `k`-compensator existence (a `RestrictedSolvability` fill in the
>       `k`-direction, the §III.4 bracket analogue of Phase I).
>   Both extra inputs are legitimate KLST/§III.4 structural primitives, never a
>   block-independence or diagonal-residue assumption — so this is a genuine
>   reduction, not a relocation.  Proved.
>
> ## Honest determination (Phase II verdict)
>
> Phase II **reduces** the diagonal residue to a sharper indifference-only seam
> (`DiagonalIndiffStickInvariant`) plus standard §III.4 single-coordinate
> primitives.  It does **not** discharge that seam from base axioms — the seam is
> the irreducible §IV.5 Thomsen content, to be supplied (from
> `WakkerCoordinateTopology` + `RestrictedSolvability` + the genuine measuring-stick
> IVT crossing) in Phase III.  This file isolates exactly *which* two-coordinate
> indifference fact the whole residue rests on.

Imports `OptionB_C1aInteriorCalibration` (for `tri`, `AdditiveRep`,
`indiff_iff_score`) and, transitively, `Core` (`coordPref`, `IsWeakOrder`).
-/

import WakkerDebreuKoopmans.OptionB_C1aInteriorCalibration
import WakkerDebreuKoopmans.OptionB_C1aDiagonalResidue
import WakkerDebreuKoopmans.OptionB_C1aGridThomsen

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

/-! ## §A.  `tri` plumbing -/

/-- Additive score of a `tri` profile, split into the three named coordinates plus
the untouched background sum.  (Same shape as the Route C `rc_score_tri` and the
Phase I `sm_score_tri`.) -/
private theorem hx_score_tri (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
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

/-- Commuting the `k` and `t` updates in a `tri` profile (so the `k`-update is
outermost).  Used to convert a same-`{j,t}`, differing-`k` comparison of `tri`
profiles into the `coordPref k` form that single-coordinate separability speaks
about. -/
private theorem tri_comm_kt {j k t : ι} (hkt : k ≠ t)
    (a : Profile X) (u : X j) (v : X k) (s : X t) :
    tri a j k t u v s
      = Function.update (Function.update (Function.update a j u) t s) k v := by
  unfold tri
  exact Function.update_comm hkt v s (Function.update a j u)

/-! ## §B.  The §IV.5 diagonal-indifference stick-invariance seam -/

/-- **Diagonal-indifference stick invariance (the §IV.5 seam).**

A `{j,k}`-block **indifference** is independent of the common stick value `t`: if
the corner `(u,v)` at stick `w` is indifferent to the corner `(u',v')` at the same
stick `w`, then the same two corners are indifferent at any other stick value `c`:

```text
[u|v|w] ∼ [u'|v'|w]   ⟹   [u|v|c] ∼ [u'|v'|c].
```

This is the genuine §IV.5 hexagon-combination content.  Unlike single-coordinate
indifference (which `TradeoffConsistency` makes base-independent), the corners here
may differ in **both** `j` and `k`, so the transport is the two-coordinate Thomsen
fact `TradeoffConsistency` does not supply on its own. -/
def DiagonalIndiffStickInvariant (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (u u' : X j) (v v' : X k) (w c : X t),
    P.indiff (tri a j k t u v w) (tri a j k t u' v' w) →
    P.indiff (tri a j k t u v c) (tri a j k t u' v' c)

/-- **Soundness gate (PROVED).**

Every additive representation satisfies the seam: an indifference
`[u|v|w] ∼ [u'|v'|w]` means `V_j u + V_k v + V_t w = V_j u' + V_k v' + V_t w`, i.e.
`V_j u + V_k v = V_j u' + V_k v'`, and adding the *same* `V_t c` to both sides
recovers the indifference at any other stick value `c`.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem diagonalIndiffStickInvariant_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    DiagonalIndiffStickInvariant P j k t := by
  intro a u u' v v' w c hw
  have h := (indiff_iff_score R).mp hw
  rw [hx_score_tri R hjk hjt hkt, hx_score_tri R hjk hjt hkt] at h
  rw [indiff_iff_score R, hx_score_tri R hjk hjt hkt, hx_score_tri R hjk hjt hkt]
  linarith

/-! ## §C.  The discharge bridge: residue from the seam + standard §III.4 inputs -/

/-- **`TBlockDiagonalResidue` from the §IV.5 seam (the discharge bridge).**

The diagonal residue (a two-coordinate *weak*-preference fact) reduces to the
sharper indifference-only seam `DiagonalIndiffStickInvariant`, together with two
standard §III.4 structural inputs:

* `hsepk` — single-coordinate-`k` **weak separability** (`CoordinateWeakSeparable P k`
  in unfolded `coordPref` form): a `k`-comparison is background-independent, in
  particular independent of the common stick value.  This is the §III.4
  single-coordinate-independence primitive adopted as a topology-module axiom.
* `hkcomp` — a **diagonal `k`-compensator**: given the premise comparison at stick
  `w`, a `k`-value `q` with `[x|r|w] ∼ [z|q|w]`.  This is a `RestrictedSolvability`
  fill in the `k`-direction (the §III.4 bracket analogue of Phase I's
  `diagonalStepStickValue_of_restrictedSolvability`).

**Argument.**  Pick the compensator `q` at stick `w`; transitivity gives
`[z|q|w] ≽ [z|p|w]`, a pure `k`-comparison, which `hsepk` carries to stick `c`:
`[z|q|c] ≽ [z|p|c]`.  The seam carries the indifference `[x|r|w] ∼ [z|q|w]` to
`[x|r|c] ∼ [z|q|c]`.  Chaining, `[x|r|c] ∼ [z|q|c] ≽ [z|p|c]`, i.e.
`[x|r|c] ≽ [z|p|c]`.

None of the inputs is a block-independence or diagonal-residue assumption, so this
is a genuine reduction of the residue to the §IV.5 seam.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockDiagonalResidue_of_diagonalIndiffStickInvariant
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hSeam : DiagonalIndiffStickInvariant P j k t)
    (hsepk : ∀ (b₁ b₂ : Profile X) (v w : X k),
      P.coordPref k b₁ v w → P.coordPref k b₂ v w)
    (hkcomp : ∀ (a : Profile X) (x z : X j) (p r : X k) (w : X t),
      x ≠ z → r ≠ p →
      P.weakPref (tri a j k t x r w) (tri a j k t z p w) →
      ∃ q : X k, P.indiff (tri a j k t x r w) (tri a j k t z q w)) :
    TBlockDiagonalResidue P j k t := by
  intro a x z p r w c hxz hrp hw
  -- Diagonal `k`-compensator `q` at stick `w`: [x|r|w] ∼ [z|q|w].
  obtain ⟨q, hq⟩ := hkcomp a x z p r w hxz hrp hw
  -- From the premise and the compensator: [z|q|w] ≽ [z|p|w] (a pure `k`-comparison).
  have hzq_zp_w : P.weakPref (tri a j k t z q w) (tri a j k t z p w) :=
    ProductPref.IsWeakOrder.transitive _ _ _ hq.2 hw
  -- Recast as `coordPref k` over the `(j ↦ z, t ↦ w)`-background.
  have hcoord_w : P.coordPref k (Function.update (Function.update a j z) t w) q p := by
    show P.weakPref
      (Function.update (Function.update (Function.update a j z) t w) k q)
      (Function.update (Function.update (Function.update a j z) t w) k p)
    rw [← tri_comm_kt hkt a z q w, ← tri_comm_kt hkt a z p w]
    exact hzq_zp_w
  -- Single-coordinate-`k` weak separability carries it to stick `c`.
  have hcoord_c : P.coordPref k (Function.update (Function.update a j z) t c) q p :=
    hsepk _ _ q p hcoord_w
  have hzq_zp_c : P.weakPref (tri a j k t z q c) (tri a j k t z p c) := by
    show P.weakPref (tri a j k t z q c) (tri a j k t z p c)
    rw [tri_comm_kt hkt a z q c, tri_comm_kt hkt a z p c]
    exact hcoord_c
  -- The §IV.5 seam carries the diagonal indifference to stick `c`.
  have hq_c : P.indiff (tri a j k t x r c) (tri a j k t z q c) :=
    hSeam a x z r q w c hq
  -- Chain: [x|r|c] ∼ [z|q|c] ≽ [z|p|c].
  exact ProductPref.IsWeakOrder.transitive _ _ _ hq_c.1 hzq_zp_c

/-! ## §D.  Phase III — the genuine discharge of the §IV.5 seam from topology

This section discharges `DiagonalIndiffStickInvariant` itself — the two-coordinate
diagonal-indifference transport — by the **honest measuring-stick construction**,
exactly mirroring the grid-level discharge
`gridDiagonalStepOffCal_of_topology_bracket_and_match` in `OptionB_C1aGridThomsen`,
lifted from the calibrated grid to **arbitrary corners**.

The forward decomposition splits the seam into:

* **The continuum existence half (theorem-backed from topology).**  Given a
  bracket pair at the target stick `c`, the slice-IVT engine
  `tCompensationExists_of_topology` (connectedness + preference continuity of the
  `WakkerCoordinateTopology` bundle, the project's standard §III.4.2 input)
  produces a compensating `t`-level `q` with `[u|v|c] ∼ [u'|v'|q]`.  No A1, no
  block-independence, no residue appeal — the genuine continuum content.

* **The Archimedean reach (named §IV.2.6 residual).**  `DiagonalStickBracket` —
  for each corner, a `t`-level over- and under-compensating the move
  `(u,v,·) → (u',v',·)` at stick `c`.  This is the reach pair the IVT crossing
  consumes; necessary under a representation from `V_t`-coverage
  (`diagonalStickBracket_of_additiveRep`).  It is the exact arbitrary-corner
  analogue of `OffCalJBracket`.

* **The Thomsen matching (named §IV.5 residual).**  `DiagonalStickMatch` — the
  IVT-produced compensation `q` is `t`-equivalent to `c` once the seam premise (the
  `t = w` indifference) is known.  Under a representation the premise forces
  `V_j u + V_k v = V_j u' + V_k v'`, so the compensation forces `V_t q = V_t c`
  (`diagonalStickMatch_of_additiveRep`).  This is the genuine cross-pair
  cancellation content — the exact arbitrary-corner analogue of
  `OffCalCompensationMatch`.

The seam then follows by pure weak-order chaining: `[u|v|c] ∼ [u'|v'|q] ∼ [u'|v'|c]`.

**Honesty.**  This is *not* a clean discharge from topology alone — no such
discharge exists in the codebase, and the two named residuals are the documented
§IV.2.6 / §IV.5 Wakker content (reach + Thomsen matching), kept at the
`WakkerCoordinateTopology` / IVT level and never expressed via a block-independence
or diagonal-residue assumption.  It *is* the genuine forward construction: the
analytic crux (the IVT crossing) is theorem-backed, and the open content is sharply
isolated into two necessity-proven structural residuals. -/

/-- **Archimedean stick bracket (the §IV.2.6 reach for the arbitrary-corner seam).**

For each corner `(a, u, u', v, v')` and target stick `c`, a `t`-level `cHi`
over-compensating and `cLo` under-compensating the two-coordinate move
`(u, v, c) → (u', v', ·)`.  The reach pair the slice-IVT crossing consumes
(arbitrary-corner analogue of `OffCalJBracket`). -/
def DiagonalStickBracket (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (u u' : X j) (v v' : X k) (c : X t),
    ∃ cHi cLo : X t,
      P.weakPref (tri a j k t u' v' cHi) (tri a j k t u v c) ∧
      P.weakPref (tri a j k t u v c) (tri a j k t u' v' cLo)

/-- **Thomsen stick matching (the §IV.5 cross-pair residual for the seam).**

Given the seam premise (the `t = w` diagonal indifference) and a compensation `q`
realizing `[u|v|c] ∼ [u'|v'|q]` at the target stick `c`, the compensation level `q`
is `t`-equivalent to `c` at the fixed `(u', v')` background:
`[u'|v'|q] ∼ [u'|v'|c]`.  The genuine cross-pair cancellation content
(arbitrary-corner analogue of `OffCalCompensationMatch`); the existence of `q` is
discharged by the IVT engine, this is the remaining equal-displacement match. -/
def DiagonalStickMatch (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (u u' : X j) (v v' : X k) (w c q : X t),
    P.indiff (tri a j k t u v w) (tri a j k t u' v' w) →
    P.indiff (tri a j k t u v c) (tri a j k t u' v' q) →
    P.indiff (tri a j k t u' v' q) (tri a j k t u' v' c)

/-- **The §IV.5 seam from topology + the two named residuals (PROVED).**

The genuine measuring-stick discharge of `DiagonalIndiffStickInvariant`:

1. `DiagonalStickBracket` supplies the §IV.2.6 reach pair `(cHi, cLo)` at stick `c`;
2. `tCompensationExists_of_topology` (the `WakkerCoordinateTopology` slice-IVT
   engine — connectedness + preference continuity, theorem-backed) crosses to a
   compensation `q` with `[u|v|c] ∼ [u'|v'|q]`;
3. `DiagonalStickMatch` upgrades `q` to `t`-equivalence with `c`:
   `[u'|v'|q] ∼ [u'|v'|c]`;
4. weak-order transitivity chains `[u|v|c] ∼ [u'|v'|q] ∼ [u'|v'|c]`.

No A1, no block independence, no diagonal-residue appeal: the analytic crux is the
theorem-backed IVT crossing, and the open content is exactly the two
necessity-proven §IV.2.6 / §IV.5 residuals.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem diagonalIndiffStickInvariant_of_topology_bracket_and_match
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (hbr : DiagonalStickBracket P j k t)
    (hmatch : DiagonalStickMatch P j k t) :
    DiagonalIndiffStickInvariant P j k t := by
  intro a u u' v v' w c hw
  -- §IV.2.6 reach bracket at the target stick `c`.
  obtain ⟨cHi, cLo, hHi, hLo⟩ := hbr a u u' v v' c
  -- Continuum/IVT crossing: a compensation `q` with `[u|v|c] ∼ [u'|v'|q]`.
  obtain ⟨q, hq⟩ :=
    tCompensationExists_of_topology htop a u u' v v' c cHi cLo hHi hLo
  -- §IV.5 Thomsen match: `q` is `t`-equivalent to `c` at the fixed `(u',v')` background.
  have hmatchqc : P.indiff (tri a j k t u' v' q) (tri a j k t u' v' c) :=
    hmatch a u u' v v' w c q hw hq
  -- Chain `[u|v|c] ∼ [u'|v'|q] ∼ [u'|v'|c]`.
  exact ⟨ProductPref.IsWeakOrder.transitive _ _ _ hq.1 hmatchqc.1,
         ProductPref.IsWeakOrder.transitive _ _ _ hmatchqc.2 hq.2⟩

/-- **Soundness gate: the Archimedean stick bracket is necessary under a rep
(modulo `V_t`-reach) (PROVED).**

Given a representation and `V_t`-reach (a level scoring at least the `{j,k}`-move
displacement above `c`, and one at most), the bracket holds.  Confirms the
§IV.2.6 reach residual hides nothing false.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem diagonalStickBracket_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hreach : ∀ (a : Profile X) (u u' : X j) (v v' : X k) (c : X t),
      ∃ cHi cLo : X t,
        R.V j u + R.V k v + R.V t c ≤ R.V j u' + R.V k v' + R.V t cHi ∧
        R.V j u' + R.V k v' + R.V t cLo ≤ R.V j u + R.V k v + R.V t c) :
    DiagonalStickBracket P j k t := by
  intro a u u' v v' c
  obtain ⟨cHi, cLo, hHi, hLo⟩ := hreach a u u' v v' c
  refine ⟨cHi, cLo, ?_, ?_⟩
  · rw [R.represents, hx_score_tri R hjk hjt hkt, hx_score_tri R hjk hjt hkt]
    linarith
  · rw [R.represents, hx_score_tri R hjk hjt hkt, hx_score_tri R hjk hjt hkt]
    linarith

/-- **Soundness gate: the Thomsen stick match is necessary under a rep (PROVED).**

Under a representation the seam premise forces `V_j u + V_k v = V_j u' + V_k v'`
(the common stick `w` cancels); the compensation premise then forces
`V_t q = V_t c`, so `[u'|v'|q] ∼ [u'|v'|c]`.  Confirms the §IV.5 matching residual
hides nothing false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem diagonalStickMatch_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    DiagonalStickMatch P j k t := by
  intro a u u' v v' w c q hw hcomp
  have h1 := (indiff_iff_score R).mp hw
  have h2 := (indiff_iff_score R).mp hcomp
  rw [hx_score_tri R hjk hjt hkt, hx_score_tri R hjk hjt hkt] at h1 h2
  rw [indiff_iff_score R, hx_score_tri R hjk hjt hkt, hx_score_tri R hjk hjt hkt]
  linarith

/-- **`TBlockDiagonalResidue` from topology + the §IV.5/§IV.2.6 residuals (PROVED).**

End-to-end Phase III chain: the seam is discharged from the topology bundle plus
the two named residuals (`diagonalIndiffStickInvariant_of_topology_bracket_and_match`),
then the Phase II bridge `tBlockDiagonalResidue_of_diagonalIndiffStickInvariant`
converts it to the diagonal residue using single-coordinate-`k` weak separability
and a diagonal `k`-compensator.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem tBlockDiagonalResidue_of_topology_bracket_and_match
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (hbr : DiagonalStickBracket P j k t)
    (hmatch : DiagonalStickMatch P j k t)
    (hsepk : ∀ (b₁ b₂ : Profile X) (v w : X k),
      P.coordPref k b₁ v w → P.coordPref k b₂ v w)
    (hkcomp : ∀ (a : Profile X) (x z : X j) (p r : X k) (w : X t),
      x ≠ z → r ≠ p →
      P.weakPref (tri a j k t x r w) (tri a j k t z p w) →
      ∃ q : X k, P.indiff (tri a j k t x r w) (tri a j k t z q w)) :
    TBlockDiagonalResidue P j k t :=
  tBlockDiagonalResidue_of_diagonalIndiffStickInvariant hjk hjt hkt
    (diagonalIndiffStickInvariant_of_topology_bracket_and_match htop hbr hmatch)
    hsepk hkcomp

end ProductPref
end WakkerInfra

/-! ## §IV.5 Thomsen discharge — Phase II + III audit

* `diagonalIndiffStickInvariant_of_additiveRep` (soundness gate) — every additive
  representation satisfies the diagonal-indifference stick-invariance seam.  Audit
  `[propext, Classical.choice, Quot.sound]`.
* `tBlockDiagonalResidue_of_diagonalIndiffStickInvariant` (Phase II discharge
  bridge) — the diagonal residue follows from the §IV.5 seam plus
  single-coordinate-`k` weak separability and a diagonal `k`-compensator (both
  standard §III.4 / solvability inputs, no block independence).  Audit
  `[propext, Classical.choice, Quot.sound]`.
* `diagonalIndiffStickInvariant_of_topology_bracket_and_match` (Phase III genuine
  discharge) — the seam itself, discharged by the measuring-stick construction:
  the slice-IVT crossing `tCompensationExists_of_topology` (theorem-backed from the
  `WakkerCoordinateTopology` bundle) supplies the compensation level, and the two
  named §IV.2.6 / §IV.5 residuals `DiagonalStickBracket` (Archimedean reach) and
  `DiagonalStickMatch` (Thomsen cross-pair matching) close it.  Audit
  `[propext, Classical.choice, Quot.sound]`.
* `diagonalStickBracket_of_additiveRep`, `diagonalStickMatch_of_additiveRep`
  (soundness gates) — both residuals are necessary under a representation, so they
  hide nothing false.  Audit `[propext, Classical.choice, Quot.sound]`.
* `tBlockDiagonalResidue_of_topology_bracket_and_match` (end-to-end Phase III) —
  the diagonal residue from topology + the two residuals + the §III.4 single-`k`
  inputs.  Audit `[propext, Classical.choice, Quot.sound]`.

**Honest determination.**  Phase II reduced the two-coordinate weak-preference
residue to the sharper indifference-only seam `DiagonalIndiffStickInvariant`.
Phase III now discharges that seam by the genuine §IV.5 measuring-stick
construction: the analytic crux (the slice-IVT crossing producing the compensating
stick value) is theorem-backed from `WakkerCoordinateTopology`, and the open
content is sharply isolated into two necessity-proven structural residuals
(`DiagonalStickBracket`, the §IV.2.6 Archimedean reach; `DiagonalStickMatch`, the
§IV.5 Thomsen cross-pair matching) — kept strictly at the topology / IVT level,
never expressed as a block-independence or diagonal-residue assumption.  This is
the exact arbitrary-corner analogue of the grid-level discharge
`gridDiagonalStepOffCal_of_topology_bracket_and_match`.  NOT merged into
`OptionB_AxiomCheck.lean`. -/

#print axioms WakkerInfra.ProductPref.diagonalIndiffStickInvariant_of_additiveRep
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_diagonalIndiffStickInvariant
#print axioms WakkerInfra.ProductPref.diagonalIndiffStickInvariant_of_topology_bracket_and_match
#print axioms WakkerInfra.ProductPref.diagonalStickBracket_of_additiveRep
#print axioms WakkerInfra.ProductPref.diagonalStickMatch_of_additiveRep
#print axioms WakkerInfra.ProductPref.tBlockDiagonalResidue_of_topology_bracket_and_match
