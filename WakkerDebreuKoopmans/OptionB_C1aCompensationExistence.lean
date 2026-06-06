/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — C1.a-1: compensating-level existence at one off-cal cell

> **STATUS: `sorry`-free forward brick on the C1.a measuring-stick construction.**
> Not in the umbrella import.

This file executes **C1.a-1** of `OptionB_C1aConstructionPlan.md`: the
compensating-`t`-level **existence** at one off-calibration cell, from the structural
axioms via {connectedness + preference continuity (the IVT crossing) + the Archimedean
escape grid (the bracket)}.

This is the first genuinely-new sound brick of the C1.a crux attack, and — crucially —
it is **not** the wall (§0.4 of the plan): it is *existence*, produced by restricted
solvability / the continuum, exactly the content the probe countermodel `Pcm` lacks
(finite, non-solvable coordinates).  The cross-pair *matching* of two such
compensations (C1.a-3) is the genuine open crux; this brick only supplies one
compensation's existence.

## What this file delivers (all machine-checked, no `sorry`)

* `CompensatingLevelExists P j k t G` — the named target: at every off-cal cell
  `(m, n, c)` with `c ∉ {rt, st}`, a `t`-level `p` with
  `[αⱼ m | αₖ n | p] ∼ [αⱼ (m+1) | αₖ n | c]` (the `j`-step compensated at level `c`).
* `compensatingLevelExists_of_additiveRep` — **the soundness gate (proved FIRST)**:
  under a representation with `V_t`-reach, the compensating level exists (it is the
  level scoring `V_t c + (V_t rt − V_t st)`).  Confirms the target hides nothing false.
* `compensatingLevelExists_of_topology_and_escapeGrid` — **the C1.a-1 forward brick**:
  the compensating level from {`WakkerCoordinateTopology` bundle + `OffCalJEscapeGrid`},
  composing `offCalJBracket_of_escapeGrid` (bracket from Archimedean escape, pure order
  theory) with `offCalJHalf_of_topology_and_bracket` (IVT crossing).

## Honest scope

C1.a-1 is the *existence* half of the off-cal cell.  It is theorem-backed end-to-end
from the structural axioms (the IVT crossing is theorem-backed; the bracket is the
§IV.2.6 Archimedean escape grid, the canonical reach residual shared with WP-density /
the J2 supplier).  It does **not** touch the crux: the genuine open content is C1.a-3
(the two compensations coincide = `OffCalCompensationMatch` = the source-level pivot),
which this brick feeds but does not discharge.  Per the plan, C1.a-1's gate is proved
first; the forward brick reuses the two existing theorem-backed half-existences.

Imports `OptionB_C1aGridThomsen` (`CalibratedJKGrid`, `OffCalJBracket`,
`offCalJHalf_of_topology_and_bracket`) and `OptionB_C1aGridTransport`
(`OffCalJEscapeGrid`, `offCalJBracket_of_escapeGrid`).  Not in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_C1aGridThomsen
import WakkerDebreuKoopmans.OptionB_C1aGridTransport

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

/-! ## §A.  The named target -/

/-- **Compensating-level existence at the off-cal cells.**

At every off-cal cell `(m, n, c)` with `c ∉ {rt, st}`, a `t`-level `p` compensates the
`j`-step `αⱼ m → αⱼ (m+1)` at level `c`:
`[αⱼ m | αₖ n | p] ∼ [αⱼ (m+1) | αₖ n | c]`.  This is the `j`-half of the off-cal
diagonal cell — *existence only* (the matching with the `k`-half is C1.a-3). -/
def CompensatingLevelExists (P : ProductPref X) (j k t : ι)
    (G : CalibratedJKGrid P j k t) : Prop :=
  ∀ (m n : ℕ) (c : X t), c ≠ G.rt → c ≠ G.st →
    ∃ p : X t, P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                        (tri G.a j k t (G.αj (m + 1)) (G.αk n) c)

/-! ## §B.  Soundness gate (proved FIRST, per the protocol)

Local score split of a `tri` profile (the `score_tri_eq` of `OptionB_C1aGridThomsen`
is `private`). -/

private theorem ce_score_tri (R : AdditiveRep P) {j k t : ι}
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

/-- **Soundness gate (PROVED): the compensating level exists under a rep.**

Under an additive representation, `[αⱼ m | αₖ n | p] ∼ [αⱼ (m+1) | αₖ n | c]` iff the
scores match, i.e. iff `V_t p = V_t c + (V_j (αⱼ (m+1)) − V_j (αⱼ m))`.  By the grid's
`spaced_j` calibration, `V_j (αⱼ (m+1)) − V_j (αⱼ m) = V_t rt − V_t st`, so the required
level is the one scoring `V_t c + (V_t rt − V_t st)` — supplied by `V_t`-reach.  So the
compensating level exists for any preference with a representation (given the reach the
continuum provides).  Confirms `CompensatingLevelExists` hides nothing false.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem compensatingLevelExists_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (G : CalibratedJKGrid P j k t)
    (hreach : ∀ (m n : ℕ) (c : X t), ∃ p : X t,
      R.V t p = R.V t c + (R.V t G.rt - R.V t G.st)) :
    CompensatingLevelExists P j k t G := by
  -- The `j`-grid step's utility increment equals the calibrating `t`-exchange size.
  have stepJ : ∀ m, R.V j (G.αj (m + 1))
      = R.V j (G.αj m) + (R.V t G.rt - R.V t G.st) := by
    intro m
    have h := (indiff_iff_score R).mp (G.spaced_j m)
    rw [ce_score_tri R hjk hjt hkt, ce_score_tri R hjk hjt hkt] at h
    linarith
  intro m n c hrt hst
  obtain ⟨p, hp⟩ := hreach m n c
  refine ⟨p, ?_⟩
  rw [indiff_iff_score R, ce_score_tri R hjk hjt hkt, ce_score_tri R hjk hjt hkt]
  have := stepJ m
  linarith

/-! ## §C.  The forward brick: existence from topology + the Archimedean escape grid -/

/-- **C1.a-1 forward brick (PROVED): compensating-level existence from the topology
bundle + the Archimedean escape grid.**

Composes two theorem-backed pieces:
* `offCalJBracket_of_escapeGrid` — the §IV.2.6 reach bracket from the strict
  Archimedean `t`-standard-sequence escape grid (pure order theory, no topology/IVT);
* `offCalJHalf_of_topology_and_bracket` — the IVT crossing from connectedness +
  preference continuity (the `WakkerCoordinateTopology` bundle) + the bracket.

So at every off-cal cell, a compensating `t`-level exists — derived end-to-end from the
structural axioms (connectedness + continuity + the Archimedean escape grid), with no
named matching input.  This is C1.a-1: the *existence* half of the off-cal cell, feeding
C1.a-3/C1.a-4.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem compensatingLevelExists_of_topology_and_escapeGrid
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (G : CalibratedJKGrid P j k t)
    (esc : OffCalJEscapeGrid P j k t G) :
    CompensatingLevelExists P j k t G :=
  offCalJHalf_of_topology_and_bracket htop G (offCalJBracket_of_escapeGrid G esc)

/-! ## §D.  Soundness gate for the forward brick's escape-grid input

The escape grid `OffCalJEscapeGrid` is the §IV.2.6 Archimedean content; it is necessary
under a rep (a strict `t`-standard-sequence with positive utility steps escapes any
reference both ways).  This is already established as `j2`/reach-necessity content; we
record the existence target's soundness via the gate `compensatingLevelExists_of_additiveRep`
above (the level exists under a rep + reach), which is the honest soundness statement for
this brick — the escape grid's own necessity is the shared §IV.2.6 residual, proved in
`OptionB_EscapeGridNecessity`. -/

end ProductPref
end WakkerInfra

/-! ## C1.a-1 audit

* §A: `CompensatingLevelExists` — the named target (compensating-level existence at
  off-cal cells).
* §B (gate, proved FIRST): `compensatingLevelExists_of_additiveRep` — the level exists
  under a rep given `V_t`-reach.
* §C (forward): `compensatingLevelExists_of_topology_and_escapeGrid` — existence from
  {topology bundle + Archimedean escape grid}, composing `offCalJBracket_of_escapeGrid`
  + `offCalJHalf_of_topology_and_bracket`.

**Honest scope.**  C1.a-1 is the *existence* half of the off-cal cell — theorem-backed
from the structural axioms (IVT crossing + Archimedean escape).  It is NOT the crux: the
cross-pair *matching* of two compensations (C1.a-3 = `OffCalCompensationMatch` = the
source-level pivot) is the genuine open content this brick feeds.  Gate proved first per
the construction protocol.  Audit `[propext, Classical.choice, Quot.sound]`. -/

#print axioms WakkerInfra.ProductPref.compensatingLevelExists_of_additiveRep
#print axioms WakkerInfra.ProductPref.compensatingLevelExists_of_topology_and_escapeGrid
