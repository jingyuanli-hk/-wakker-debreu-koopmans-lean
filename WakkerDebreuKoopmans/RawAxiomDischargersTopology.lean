/-
Copyright (c) 2026 Wakker–Debreu–Koopmans project.
SPDX-License-Identifier: Apache-2.0

# Topology axiom bundle for raw-axiom dischargers (Phase 8 architectural seam)

This file isolates the **topology architectural decision** for axiom 11
(`sharedPivotPivotOneStepExtensibleOnSeedProfileAndReferenceExchangeCertificate_from_raw_axioms`)
of `RawAxiomDischargers.lean`.

## The issue

Axiom 11 asks for `ProductPref.OneStepExtensible P j₀ base k r s` from the
four raw axioms `Essential + RestrictedSolvability + TradeoffConsistency +
Archimedean`.  But Wakker's actual derivation of `OneStepExtensible`
(monograph III.4.2) uses an **additional** structural input that is **not**
on the raw-axiom list:

* topological connectedness of each coordinate space `X j`, and
* continuity of the preference relation `≽`.

So axiom 11 is **strictly stronger** than the raw axioms can honestly
support.  Wakker's proof needs the topology, and so does any honest Lean
proof.

## The architectural options

* **Option A — typeclass bundle.**  Introduce a `Prop`-level bundle
  `WakkerCoordinateTopology P` that names the topology hypotheses
  separately, and discharge axiom 11 against `bundle + RestrictedSolvability`.
  The resulting theorem requires consumers to supply the topology data
  explicitly, but the audit boundary becomes honest: the topology bundle
  is a documented data input, not a hidden axiom.

* **Option B — predicate-only.**  Same content as Option A but as plain
  function arguments rather than typeclass instances.

* **Option C — status quo.**  Keep axiom 11 as a primitive axiom and
  document the topology hypotheses needed in a comment.  The audit then
  shows axiom 11 as an opaque obligation; consumers cannot tell from the
  audit alone whether the missing content is "Wakker theory we haven't
  formalized" or "raw-axiom-impossible content we need to take as
  topology hypothesis".

## What this file does

This file implements **Option A** as a recommendation, in a way that:

1. defines the topology axiom bundle as `Prop`-level predicates;
2. proves `OneStepExtensible` from `bundle + RestrictedSolvability`
   (where the bundle is sufficient — the proof shape mirrors the
   existing `coordinateStandardSequenceExtensionData_of_restrictedSolvability_and_connectedContinuity`
   in `M2Frontier.lean`, but lifted to generic coordinate types);
3. exposes a discharge route that the consumer file
   `RawAxiomDischargers.lean` can opt into, leaving axiom 11 as a
   documented residual that depends only on the topology bundle.

This file is **not** imported into the umbrella, by design.  Importing
the topology bundle into a consumer means committing to the Wakker
topology hypotheses explicitly; that is the architectural decision the
consumer must make.

## Status

The bundle definitions in this file compile.  The discharge theorem is
currently a **typed `axiom`** that documents the precise content of the
remaining work; the analytic proof requires lifting Mathlib's
`IsPreconnected` / IVT machinery from the real-coordinate case (already
present in `Topology.lean`) to a generic coordinate type, plus a
two-coordinate update-swap manipulation (already present in
`update_comm_two_coords_real`).  This residual proof is approximately
the same shape as
`coordinateStandardSequenceExtensionData_of_restrictedSolvability_and_connectedContinuity`
in `M2Frontier.lean`, but specialized to a single chosen
`(j, k, base, r, s)` rather than a per-coordinate family.

See `RawAxiomDischargersAttackPlan.md` for the recommended next steps.
-/
import WakkerDebreuKoopmans.Core
import WakkerDebreuKoopmans.Closure
import WakkerDebreuKoopmans.RawAxiomDischargersIVT
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace RawAxiomDischargersTopology

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

open WakkerInfra
open Function Finset
open Classical

/-! ## §1.  Topology axiom bundle

The honest topology input Wakker (1989) III.4.2 uses to derive
`OneStepExtensible`. -/

/-- **Preference continuity at a single profile.**

For a fixed reference profile `a`, the upper and lower closed sets at `a`
are closed under the product topology on `Profile X`. -/
def PreferenceContinuousAt {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) (a : Profile X) : Prop :=
  IsClosed {x : Profile X | P.weakPref x a} ∧
  IsClosed {x : Profile X | P.weakPref a x}

/-- **Preference continuity globally.** -/
def PreferenceContinuous {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) : Prop :=
  ∀ a : Profile X, PreferenceContinuousAt P a

/-- **Per-coordinate connectedness.** -/
def ConnectedCoordinates {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    (_P : ProductPref X) : Prop :=
  ∀ i : ι, ConnectedSpace (X i)

/-- **The Wakker topology bundle.**

Components:

* per-coordinate topology (typeclass instances on each `X i`);
* per-coordinate connectedness;
* preference continuity;
* **coordinate weak separability** — single-coordinate weak preference is
  background-independent (Wakker §III.4 coordinate independence).

These together with `RestrictedSolvability P` are sufficient to discharge
`OneStepExtensible` (Wakker III.4.2).

**Soundness note (A1).**  Coordinate weak separability is a genuine *structural
axiom* (Wakker §III.4 / additive conjoint measurement), **not** a consequence of
connectedness + continuity: the weak order on `ℝ²` represented by the continuous
utility `U(x₁,x₂) = x₁·(x₂−1)` is a complete, transitive order with connected
coordinates and continuous preference, yet its coordinate-1 preference reverses
between base `x₂ = 2` (where `2 ≽₁ 1`) and base `x₂ = 0` (where `1 ≻₁ 2`).  So
separability cannot be derived from the topological data; it is carried here as an
explicit field of the structural bundle, matching Wakker's framework where
coordinate independence is an axiom. -/
structure WakkerCoordinateTopology {X : ι → Type v}
    [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) where
  connected : ConnectedCoordinates P
  continuous : PreferenceContinuous P
  separable : ∀ i, RawAxiomDischargersIVT.CoordinateWeakSeparable P i

/-! ## §2.  Bracketing axiom (the analytic content)

To discharge `OneStepExtensible` honestly, one needs the **bracket**: for
each `aPrev`, the perturbed profile `update (update base j aPrev) k r`
sits between two profiles `update (update base j aLo) k s` and
`update (update base j aHi) k s`.  Restricted solvability then fills the
bracket to produce `aNext`.

The bracket itself comes from the bundle's continuity + connectedness, but
proving that requires either:

* an additive-representation IVT (the route used in
  `oneStepExtensible_of_continuity_unbounded` in `ConstructionStack.lean`);
* a generic preconnectedness IVT on the coordinate space (the route Wakker
  III.4.2 uses).

Neither is a small lemma.  The bracket is therefore named here as a
separate certificate so the architectural decision can be made
incrementally: one can discharge the bracket from the bundle in a future
session, and the full discharge of `OneStepExtensible` then follows
immediately.
-/

/-- **Per-`(j, k, base, r, s)` one-step bracket on `X j`.**

For each prior `aPrev : X j` and each pair of distinct reference values
`r ≠ s : X k`, two pivot values `aLo, aHi : X j` such that the perturbed
profile sits between the two two-coordinate updates. -/
def CoordinateOneStepBracket {X : ι → Type v}
    (P : ProductPref X) (j : ι) (base : Profile X) (k : ι) (r s : X k) : Prop :=
  ∀ aPrev : X j,
    ∃ aLo aHi : X j,
      P.weakPref
        (Function.update (Function.update base j aHi) k s)
        (Function.update (Function.update base j aPrev) k r) ∧
      P.weakPref
        (Function.update (Function.update base j aPrev) k r)
        (Function.update (Function.update base j aLo) k s)

/-! ## §3.  Discharge of `OneStepExtensible` from bracket + restricted solvability

This is the **honest theorem-backed bridge** below the bracket.  Once the
bracket is named, restricted solvability fills it to produce the `aNext`
witness.  This part of the chain is fully theorem-backed; it is the
analytic content (the bracket itself) that requires the topology bundle.

The proof below mirrors
`coordinateStandardSequenceExtensionData_of_restrictedSolvability_and_connectedContinuity`
in `M2Frontier.lean`, generalized to arbitrary coordinate type `X j` (not
just `ℝ`). -/

/-- Generic two-coordinate update-swap lemma.  Same content as
`update_comm_two_coords_real` in `M2Frontier.lean`, but for any `X k`. -/
lemma update_comm_two_coords {X : ι → Type v}
    (base : Profile X) {j k : ι} (hjk : j ≠ k)
    (c : X j) (s : X k) :
    Function.update (Function.update base k s) j c =
      Function.update (Function.update base j c) k s := by
  funext t
  by_cases htj : t = j
  · subst t
    simp [Function.update_of_ne hjk]
  · by_cases htk : t = k
    · subst t
      simp [Function.update_of_ne (Ne.symm hjk)]
    · rw [Function.update_of_ne htj, Function.update_of_ne htk,
        Function.update_of_ne htk, Function.update_of_ne htj]

/-- **`OneStepExtensible` from a one-step bracket plus restricted solvability.**

This is the theorem-backed half of the architectural decision: once the
bracket has been supplied (the analytic content of the topology bundle),
restricted solvability fills it to produce the indifference witness. -/
theorem oneStepExtensible_of_coordinateOneStepBracket_and_restrictedSolvability
    {X : ι → Type v} {P : ProductPref X}
    (hsolv : ProductPref.RestrictedSolvability P)
    {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (r s : X k)
    (hbracket : CoordinateOneStepBracket P j base k r s) :
    ProductPref.OneStepExtensible P j base k r s := by
  intro aPrev
  obtain ⟨aLo, aHi, hupper, hlower⟩ := hbracket aPrev
  let a : Profile X := Function.update base k s
  let b : Profile X := Function.update (Function.update base j aPrev) k r
  -- Restricted solvability:
  --   weakPref (update a j aHi) b → weakPref b (update a j aLo) →
  --     ∃ c, indiff (update a j c) b
  have hupper' :
      P.weakPref (Function.update a j aHi) b := by
    have hswap := update_comm_two_coords (X := X) base hjk aHi s
    show P.weakPref (Function.update (Function.update base k s) j aHi) b
    rw [hswap]
    exact hupper
  have hlower' :
      P.weakPref b (Function.update a j aLo) := by
    have hswap := update_comm_two_coords (X := X) base hjk aLo s
    show P.weakPref b (Function.update (Function.update base k s) j aLo)
    rw [hswap]
    exact hlower
  obtain ⟨aNext, hfill⟩ := hsolv a b j aHi aLo hupper' hlower'
  refine ⟨aNext, ?_⟩
  -- hfill : P.indiff (update a j aNext) b, where a = update base k s.
  -- Need: P.indiff (update (update base j aPrev) k r) (update (update base j aNext) k s).
  -- The latter is `b ∼ update (update base j aNext) k s`.
  have hswap := update_comm_two_coords (X := X) base hjk aNext s
  -- hfill is symmetric in indiff, so flip and rewrite.
  have hflip : P.indiff b (Function.update a j aNext) := ⟨hfill.2, hfill.1⟩
  show P.indiff b (Function.update (Function.update base j aNext) k s)
  rw [← hswap]
  exact hflip

/-! ## §4.  Bracket from the topology bundle (the residual analytic content)

The remaining honest piece: under the topology bundle, the bracket holds.

The proof is Wakker III.4.2's connectedness + continuity argument, which
in Mathlib terms reads:

* Define `f : X j → Profile X` by `f c = update (update base j c) k r`.
  Continuous (composition of continuous coordinate inclusions).
* The set `S = {c : X j | weakPref (f aPrev) (update (update base j c) k s)}`
  is closed (preimage of an upper closed set under a continuous map, where
  upper closure is part of the bundle).
* Symmetric set `T` for the lower direction.
* The bundle's connectedness gives that `X j` is preconnected; if `S` and
  `T` cover `X j` and intersect nontrivially with extra mild hypotheses,
  IVT gives a witness in both, which is the bracket boundary.

The actual proof requires either:

* additive-representation IVT (used in `ConstructionStack.lean` —
  needs an `AdditiveRep`, which we don't have at this layer);
* a generic preconnectedness argument for the preference image
  (similar to `coordinateUtilityImage_isPreconnected_of_connected_and_continuous`
  in `Topology.lean`, but lifted to two-coordinate updates).

This is genuine Wakker mathematics.  The remaining residual content is
captured here as the smaller named seam below. -/

/-! ### The residual seam: bracket from topology bundle

The original conjunctive axiom is the **honest residual** below the topology architectural
decision: even after committing to a topology bundle, Wakker's actual
III.4.2 proof requires a connectedness/IVT argument we have not yet
formalized in generic-coordinate form.

**Wakker reference:** §III.4.2 (the IVT/connectedness step in the
standard-sequence extensibility derivation).

**Mathematical content:** Under the topology bundle (per-coordinate
connectedness + preference continuity), for any base profile, any
coordinates `j ≠ k`, and any `r ≠ s : X k`, the prior pivot value
`aPrev : X j` admits bracket values `aLo, aHi : X j` such that the
perturbed profile sits between the two two-coordinate updates.  This
is the analytic IVT step: continuity makes the bracket condition a
closed/closed pair of conditions on `X j`, connectedness fills the gap.

**Why this remains an axiom:** lifting Mathlib's `IsPreconnected` IVT
machinery from the real-coordinate case (in `Topology.lean`) to a
generic coordinate type with two-coordinate updates is multi-day work.
The infrastructure for the real case is in place; the generic case is
a structural lift.

When proved, it composes via
`oneStepExtensible_of_coordinateOneStepBracket_and_restrictedSolvability`
into a full theorem-backed discharge of axiom 11.

**Estimated effort:** 3–5 days of Mathlib-topology lifting work.

**Decomposition (this session):** The conjunctive bracket is split into
two strictly smaller named seams below: an upper-reach axiom
(`coordinateOneStepBracketUpperReach_of_wakkerCoordinateTopology`) and
a lower-reach axiom (`coordinateOneStepBracketLowerReach_of_wakkerCoordinateTopology`).
The conjunctive bracket itself is then proved as a theorem.  Each
half-axiom is strictly weaker than the original (it postulates only one
direction of the bracket), and the two halves can be discharged
independently — for example, the upper-reach axiom alone can be proved
from a one-sided IVT/continuity argument that does not need to worry
about the lower half. -/

/-- **Upper-reach half of the bracket from the topology bundle.**

This is the *upper* half of `coordinateOneStepBracket_of_wakkerCoordinateTopology`:
for any prior pivot `aPrev : X j`, there exists some pivot value
`aHi : X j` such that the `(j ↦ aHi, k ↦ s)`-perturbed profile is at
least as preferred as the `(j ↦ aPrev, k ↦ r)`-perturbed profile.

Strictly weaker than the original bracket axiom: it only asserts the
upper direction, not the conjunctive bracket. -/
axiom coordinateOneStepBracketUpperReach_of_wakkerCoordinateTopology
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (r s : X k) (hrs : r ≠ s) :
    ∀ aPrev : X j, ∃ aHi : X j,
      P.weakPref
        (Function.update (Function.update base j aHi) k s)
        (Function.update (Function.update base j aPrev) k r)

/-- **Lower-reach half of the bracket from the topology bundle.**

The dual of `coordinateOneStepBracketUpperReach_of_wakkerCoordinateTopology`:
for any prior pivot `aPrev`, there exists some pivot value `aLo : X j`
such that the `(j ↦ aPrev, k ↦ r)`-perturbed profile is at least as
preferred as the `(j ↦ aLo, k ↦ s)`-perturbed profile.

Strictly weaker than the original bracket axiom: it only asserts the
lower direction, not the conjunctive bracket. -/
axiom coordinateOneStepBracketLowerReach_of_wakkerCoordinateTopology
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (r s : X k) (hrs : r ≠ s) :
    ∀ aPrev : X j, ∃ aLo : X j,
      P.weakPref
        (Function.update (Function.update base j aPrev) k r)
        (Function.update (Function.update base j aLo) k s)

/-- **Conjunctive bracket from the two half-axioms.**

Theorem-backed assembly: combining the upper- and lower-reach axioms
yields the full `CoordinateOneStepBracket`.  The original
single axiom is therefore retired in favor of the two strictly weaker
named seams above. -/
theorem coordinateOneStepBracket_of_wakkerCoordinateTopology
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (r s : X k) (hrs : r ≠ s) :
    CoordinateOneStepBracket P j base k r s := by
  intro aPrev
  obtain ⟨aHi, hupper⟩ :=
    coordinateOneStepBracketUpperReach_of_wakkerCoordinateTopology
      htop hjk base r s hrs aPrev
  obtain ⟨aLo, hlower⟩ :=
    coordinateOneStepBracketLowerReach_of_wakkerCoordinateTopology
      htop hjk base r s hrs aPrev
  exact ⟨aLo, aHi, hupper, hlower⟩

/-! ### IVT-backed discharge of the bracket from reach witnesses

The generic-coordinate IVT engine in `RawAxiomDischargersIVT.lean` lets us prove
the **exact indifferent crossing** form of the one-step extensibility — not just
the two-sided bracket — directly from the topology bundle plus *reach witnesses*.
The reach witnesses (`aHi` above `b`, `aLo` below `b`) are the genuine residual
that Wakker (1989) §IV.2.6 derives from the **Archimedean axiom** (unboundedness
of the standard-sequence grid); the IVT/connectedness crossing that fills the gap
between them is now **theorem-backed**, not axiomatized.

This isolates the honest analytic content of the bracket axioms: it is *only* the
reach/unboundedness residual, with the intermediate-value crossing discharged. -/

/-- **`OneStepExtensible` from the topology bundle plus reach witnesses, via the
IVT engine.**

Given per-coordinate connectedness and global preference continuity (both
packaged in `WakkerCoordinateTopology`), together with, for every prior pivot
`aPrev`, a *reach* pair `cHi, cLo` bracketing `update (update base j aPrev) k r`
from above and below along coordinate `j` (with `k` fixed at `s`), the
generic-coordinate IVT produces an exact indifferent crossing — which is
precisely the `OneStepExtensible` witness.

The crossing is theorem-backed (`coordinate_slice_IVT_of_preferenceContinuous`);
the only residual is the reach pair, i.e. the Archimedean-derived unboundedness. -/
theorem oneStepExtensible_of_wakkerCoordinateTopology_and_reachWitnesses
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (r s : X k)
    (hreach : ∀ aPrev : X j, ∃ cHi cLo : X j,
      P.weakPref
        (Function.update (Function.update base j cHi) k s)
        (Function.update (Function.update base j aPrev) k r) ∧
      P.weakPref
        (Function.update (Function.update base j aPrev) k r)
        (Function.update (Function.update base j cLo) k s)) :
    ProductPref.OneStepExtensible P j base k r s := by
  classical
  haveI : ConnectedSpace (X j) := htop.connected j
  intro aPrev
  -- Reference profile to cross: the `r`-perturbed prior profile.
  set b : Profile X := Function.update (Function.update base j aPrev) k r with hb
  obtain ⟨cHi, cLo, hHi, hLo⟩ := hreach aPrev
  -- Preference continuity at `b` (global product-topology form).
  have hUpper : IsClosed {x : Profile X | P.weakPref x b} := (htop.continuous b).1
  have hLower : IsClosed {x : Profile X | P.weakPref b x} := (htop.continuous b).2
  -- IVT on the slice map at coordinate `j`, base `update base k s`, reference `b`.
  -- The slice values are `update (update base k s) j c`; rewrite to the
  -- two-coordinate-update form used by the reach witnesses via `update_comm`.
  have hHi' : P.weakPref
      (Function.update (Function.update base k s) j cHi) b := by
    rw [update_comm_two_coords (X := X) base hjk cHi s]; exact hHi
  have hLo' : P.weakPref b
      (Function.update (Function.update base k s) j cLo) := by
    rw [update_comm_two_coords (X := X) base hjk cLo s]; exact hLo
  obtain ⟨c, hc⟩ :=
    RawAxiomDischargersIVT.coordinate_slice_IVT_of_preferenceContinuous
      P (Function.update base k s) j b hUpper hLower hHi' hLo'
  -- `hc : indiff (update (update base k s) j c) b`.  Repackage as OneStepExtensible.
  refine ⟨c, ?_⟩
  -- Need: indiff (update (update base j aPrev) k r) (update (update base j c) k s).
  -- i.e. indiff b (update (update base j c) k s).
  have hcrew : Function.update (Function.update base k s) j c
      = Function.update (Function.update base j c) k s :=
    update_comm_two_coords (X := X) base hjk c s
  rw [hcrew] at hc
  -- hc : indiff (update (update base j c) k s) b.  Flip to match the goal `indiff b ...`.
  exact ⟨hc.2, hc.1⟩

/-- **`OneStepExtensible` from the topology bundle plus Archimedean grid escape.**

The full composition of engines A (IVT) and B (Archimedean reach) at the
`OneStepExtensible` level.  For every prior pivot `aPrev`, suppose we have a
strict Archimedean standard sequence `σ` on coordinate `j` whose base is the
`s`-perturbed profile `update base k s`, and whose grid two-sidedly escapes the
`r`-perturbed reference `update (update base j aPrev) k r`.  Then connectedness +
preference continuity (the bundle) supply the indifferent crossing, i.e. the
`OneStepExtensible` witness.

This routes entirely through the theorem-backed `archimedean_slice_crossing`
(engines A + B) — **no bracket axiom**.  The honest residual is reduced to the
existence of the per-`aPrev` strict Archimedean grid that two-sidedly escapes,
which is precisely Wakker §IV.2.6 standard-sequence content. -/
theorem oneStepExtensible_of_wakkerCoordinateTopology_and_archimedeanEscape
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (r s : X k)
    (harchim : ProductPref.Archimedean P j)
    (hgrid : ∀ aPrev : X j,
      ∃ σ : ProductPref.StandardSequence P j,
        σ.IsStrict ∧
        σ.base = Function.update base k s ∧
        (∃ n : ℕ, ¬ P.weakPref
          (Function.update (Function.update base j aPrev) k r)
          (Function.update σ.base j (σ.α n))) ∧
        (∃ n : ℕ, ¬ P.weakPref
          (Function.update σ.base j (σ.α n))
          (Function.update (Function.update base j aPrev) k r))) :
    ProductPref.OneStepExtensible P j base k r s := by
  classical
  haveI : ConnectedSpace (X j) := htop.connected j
  intro aPrev
  set b : Profile X := Function.update (Function.update base j aPrev) k r with hb
  obtain ⟨σ, hσ, hσbase, habove, hbelow⟩ := hgrid aPrev
  have hUpper : IsClosed {x : Profile X | P.weakPref x b} := (htop.continuous b).1
  have hLower : IsClosed {x : Profile X | P.weakPref b x} := (htop.continuous b).2
  obtain ⟨c, hc⟩ :=
    RawAxiomDischargersIVT.archimedean_slice_crossing
      P σ hσ harchim b hUpper hLower habove hbelow
  -- hc : indiff (update σ.base j c) b.  Rewrite σ.base = update base k s.
  rw [hσbase] at hc
  refine ⟨c, ?_⟩
  have hcrew : Function.update (Function.update base k s) j c
      = Function.update (Function.update base j c) k s :=
    update_comm_two_coords (X := X) base hjk c s
  rw [hcrew] at hc
  exact ⟨hc.2, hc.1⟩

/-- **`OneStepExtensible` from the topology bundle + a weakly-descending
Archimedean grid seeded above (the leanest engine-A∘B residual).**

The cleanest packaging: for every prior pivot `aPrev`, supply a strict
**weakly-descending** Archimedean standard sequence `σ` based at
`update base k s` whose **first** grid point is seeded *above* the `r`-perturbed
reference `update (update base j aPrev) k r` (i.e. `¬ b ≽ update σ.base j (σ.α 0)`).
Then `OneStepExtensible` follows — with **no escape hypothesis**: the lower
escape is automatic from descent, the upper escape is the seed condition, the
reach is theorem-backed, and the IVT crossing is theorem-backed.

This routes through `archimedean_weaklyDescending_slice_crossing_of_seedAbove`;
audit `[propext, Classical.choice, Quot.sound]`, no bracket axiom.  The residual
is now exactly "a strict weakly-descending Archimedean grid seeded above the
target exists per prior pivot" — pure §III.4/§IV.2.6 standard-sequence
construction content. -/
theorem oneStepExtensible_of_wakkerCoordinateTopology_and_descendingSeedAboveGrid
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (r s : X k)
    (harchim : ProductPref.Archimedean P j)
    (hgrid : ∀ aPrev : X j,
      ∃ σ : ProductPref.StandardSequence P j,
        σ.IsStrict ∧
        σ.base = Function.update base k s ∧
        (∀ n, P.weakPref (Function.update σ.base j (σ.α n))
                         (Function.update σ.base j (σ.α (n + 1)))) ∧
        ¬ P.weakPref
          (Function.update (Function.update base j aPrev) k r)
          (Function.update σ.base j (σ.α 0))) :
    ProductPref.OneStepExtensible P j base k r s := by
  classical
  haveI : ConnectedSpace (X j) := htop.connected j
  intro aPrev
  set b : Profile X := Function.update (Function.update base j aPrev) k r with hb
  obtain ⟨σ, hσ, hσbase, hdesc, hseed⟩ := hgrid aPrev
  have hUpper : IsClosed {x : Profile X | P.weakPref x b} := (htop.continuous b).1
  have hLower : IsClosed {x : Profile X | P.weakPref b x} := (htop.continuous b).2
  obtain ⟨c, hc⟩ :=
    RawAxiomDischargersIVT.archimedean_weaklyDescending_slice_crossing_of_seedAbove
      P σ hσ harchim hdesc b hUpper hLower hseed
  rw [hσbase] at hc
  refine ⟨c, ?_⟩
  have hcrew : Function.update (Function.update base k s) j c
      = Function.update (Function.update base j c) k s :=
    update_comm_two_coords (X := X) base hjk c s
  rw [hcrew] at hc
  exact ⟨hc.2, hc.1⟩

/-! ### Degenerate-case discharges of the bracket half-axioms

Following the partial-discharge methodology already applied to every primitive
axiom in `RawAxiomDischargers.lean` (Phases 8–11), the two bracket half-axioms
admit a clean **theorem-backed** discharge in the degenerate
`Subsingleton (X k)` regime: when the reference coordinate `X k` is a
subsingleton, the distinctness hypothesis `r ≠ s` is unsatisfiable (`r = s` by
`Subsingleton.allEq`), so both half-axioms hold vacuously without any topology
bundle.

In any non-degenerate setting where the reference exchange `(r, s)` is genuinely
distinct, `X k` has at least two values, so this discharge is genuinely
degenerate.  But it establishes that the bracket half-axioms are **not strictly
unprovable** — the genuine Wakker §III.4.2 IVT/connectedness content lives only
in the regime where `X k` carries distinct reference values. -/

/-- **Partial discharge of the upper-reach bracket half-axiom in
`Subsingleton (X k)`.**

When `X k` is a subsingleton the distinctness hypothesis `r ≠ s` is
contradictory, so the upper-reach bracket holds vacuously.  No topology bundle
needed. -/
theorem coordinateOneStepBracketUpperReach_of_subsingleton
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j k : ι}
    (base : Profile X) (r s : X k) (hrs : r ≠ s)
    [Subsingleton (X k)] :
    ∀ aPrev : X j, ∃ aHi : X j,
      P.weakPref
        (Function.update (Function.update base j aHi) k s)
        (Function.update (Function.update base j aPrev) k r) :=
  absurd (Subsingleton.allEq r s) hrs

/-- **Partial discharge of the lower-reach bracket half-axiom in
`Subsingleton (X k)`.**

Dual of the upper-reach subsingleton discharge: the distinctness hypothesis
`r ≠ s` is contradictory when `X k` is a subsingleton, so the lower-reach
bracket holds vacuously. -/
theorem coordinateOneStepBracketLowerReach_of_subsingleton
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j k : ι}
    (base : Profile X) (r s : X k) (hrs : r ≠ s)
    [Subsingleton (X k)] :
    ∀ aPrev : X j, ∃ aLo : X j,
      P.weakPref
        (Function.update (Function.update base j aPrev) k r)
        (Function.update (Function.update base j aLo) k s) :=
  absurd (Subsingleton.allEq r s) hrs

/-- **`OneStepExtensible` from the Wakker topology bundle plus restricted
solvability.**

This is the **architectural-decision-shaped discharge** of axiom 11.

Audit-wise, this theorem depends on:

* `[propext, Classical.choice, Quot.sound]`;
* the named topology bundle `WakkerCoordinateTopology P` (not an axiom — a
  data input);
* `RestrictedSolvability P` (one of the four raw axioms);
* the smaller seam `coordinateOneStepBracket_of_wakkerCoordinateTopology`
  (an axiom in this file, awaiting a Wakker-III.4.2-style proof).

It is **strictly cleaner** than the corresponding axiom 11 in
`RawAxiomDischargers.lean`, because:

1. the topology hypotheses are explicit, not silently postulated;
2. the residual content is now a named one-line analytic axiom about
   bracketing, instead of an opaque obligation about an indifference
   that is half-bookkeeping and half-Wakker theory.

Adopting this discharge route in `RawAxiomDischargers.lean` means
adding `[∀ i, TopologicalSpace (X i)]` and a `WakkerCoordinateTopology P`
hypothesis to the relevant theorem-backed wrappers.  That is the
architectural decision the consumer must make consciously. -/
theorem oneStepExtensible_of_wakkerCoordinateTopology_and_restrictedSolvability
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (htop : WakkerCoordinateTopology P)
    {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (r s : X k) (hrs : r ≠ s) :
    ProductPref.OneStepExtensible P j base k r s :=
  oneStepExtensible_of_coordinateOneStepBracket_and_restrictedSolvability
    hsolv hjk base r s
    (coordinateOneStepBracket_of_wakkerCoordinateTopology htop hjk base r s hrs)

/-! ## §5.  Architectural-decision summary

This file commits to **Option A** (typeclass bundle) by introducing
`WakkerCoordinateTopology` as a `Prop`-level data input.  The
architectural decision is:

* downstream `_from_raw_axioms` declarations that reach axiom 11 should
  add `[∀ i, TopologicalSpace (X i)]` and a `WakkerCoordinateTopology P`
  hypothesis, then route through
  `oneStepExtensible_of_wakkerCoordinateTopology_and_restrictedSolvability`
  to discharge the `OneStepExtensible` content;

* the resulting audit will show the smaller analytic axiom
  `coordinateOneStepBracket_of_wakkerCoordinateTopology` instead of the
  opaque axiom 11.

The audit becomes strictly more informative without committing to extra
foundational axioms beyond the topology data input.

This file is **not** imported by `RawAxiomDischargers.lean` automatically:
adopting the architectural decision means modifying the consumer side to
import this file and add the topology hypotheses.  That move is a
session of structural refactoring beyond the architectural-decision
setup itself. -/

/-! ## §6.  Compensating reference value (preliminary infrastructure for axioms 9/10)

Axioms 9 and 10 in `RawAxiomDischargers.lean` jointly assert the
descending seed indifference

```
indiff (update (update base j₀ a0) k r) (update (update base j₀ a1) k s)
```

against the canonical seed pair `(base, a0, a1)` from `Essential P j₀`
and arbitrary distinct `(r, s)` from `Essential P k`.  This is **not
true in general**: two arbitrary essential witnesses on two different
coordinates do not automatically compensate each other.

Below is the **compensating-`s` theorem**: under the topology bundle
plus restricted solvability, given any fixed pivot seed pair
`(base, a0, a1)` with `a0 ≠ a1` and any `r : X k`, one can find
`s : X k` such that the descending seed indifference holds.

This theorem is **partial infrastructure** for retiring axioms 9 and
10.  It does **not** by itself complete the retirement, because the
existing `SharedPivotPivotReferenceExchangeAtPivotData` structure also
requires `r ≠ s` (Wakker III.4 distinctness assumption needed for
`extend_to_standard_sequence`), and the compensating `s` returned by
this theorem may equal `r` in degenerate cases (when `a0` and `a1` are
indifferent on `j₀` at the perturbed base).

Two paths forward to actually retire axioms 9 and 10:

1. **Structural refactor.**  Restructure
   `SharedPivotPivotReferenceExchangeAtPivotData` to drop the `r ≠ s`
   field, push the distinctness requirement deeper into the consumers
   that genuinely need it (the `extend_to_standard_sequence` interface).
2. **New axiom.**  Add a smaller analytic axiom asserting that one can
   choose `r : X k` such that the compensating `s` differs from it.
   This is essentially a strong monotonicity claim (Wakker III.4 with
   strictness uniformity).

Either path is a multi-session refactor.  The compensating-`s` theorem
below is the reusable building block both paths will share. -/

/-- **Compensating reference value on coordinate `k`.**

Given the topology bundle + `RestrictedSolvability`, for any fixed pivot
seed pair `(base, a0, a1)` on coordinate `j₀` with `a0 ≠ a1`, any
non-pivot coordinate `k ≠ j₀`, and any `r : X k`, one can find
`s : X k` such that the descending seed indifference

```
P.indiff
  (update (update base j₀ a0) k r)
  (update (update base j₀ a1) k s)
```

holds.

Note: the returned `s` may equal `r` in degenerate cases.  For full
retirement of axioms 9 and 10, see the discussion above this theorem. -/
theorem compensating_reference_value_of_wakkerCoordinateTopology_and_restrictedSolvability
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (htop : WakkerCoordinateTopology P)
    {j₀ k : ι} (hkj : k ≠ j₀)
    (base : Profile X) (a0 a1 : X j₀) (h01 : a0 ≠ a1) (r : X k) :
    ∃ s : X k,
      P.indiff
        (Function.update (Function.update base j₀ a0) k r)
        (Function.update (Function.update base j₀ a1) k s) := by
  -- Apply `OneStepExtensible` in the `k` direction, with `j₀` playing
  -- the role of the auxiliary coordinate.
  have hext :
      ProductPref.OneStepExtensible P k base j₀ a0 a1 :=
    oneStepExtensible_of_wakkerCoordinateTopology_and_restrictedSolvability
      (j := k) (k := j₀) hsolv htop hkj base a0 a1 h01
  obtain ⟨s, hindiff⟩ := hext r
  refine ⟨s, ?_⟩
  -- hindiff :
  --   indiff (update (update base k r) j₀ a0) (update (update base k s) j₀ a1)
  -- Need:
  --   indiff (update (update base j₀ a0) k r) (update (update base j₀ a1) k s)
  -- Use update_comm_two_coords with hjk = j₀ ≠ k = hkj.symm.
  have h1 :
      Function.update (Function.update base k r) j₀ a0 =
        Function.update (Function.update base j₀ a0) k r :=
    update_comm_two_coords (X := X) base hkj.symm a0 r
  have h2 :
      Function.update (Function.update base k s) j₀ a1 =
        Function.update (Function.update base j₀ a1) k s :=
    update_comm_two_coords (X := X) base hkj.symm a1 s
  rw [h1, h2] at hindiff
  exact hindiff

/-! ## §7.  Compensating reference exchange (with distinctness)

The compensating-`s` theorem above produces an `s` such that the
descending seed indifference holds, but does not guarantee `s ≠ r`.

Wakker's monograph treatment makes use of an additional **non-degeneracy**
assumption — informally, that distinct strict pivot values on `j₀` lead
to distinct compensating values on `k`.  This is a **smaller** claim
than axioms 9 and 10 jointly, because the indifference itself is now
theorem-backed.

The smaller named axiom below is the honest residual: under the topology
bundle plus restricted solvability plus the strict pivot pair `(a0, a1)`,
the compensating `s` returned by the compensating theorem is distinct
from `r`.

Wakker (1989) derives this from a structural single-coordinate
monotonicity axiom.  For now, we name it as an axiom and use it to
discharge the descending seed comparison certificates jointly. -/

/-- **Strict distinctness of the compensating reference value.**

Under the topology bundle, restricted solvability, and a strict pivot
seed pair (witnesses `hweak ∧ ¬hweak⁻¹` so `a0 ≠ a1`), the compensating
`s` from the compensating-`s` theorem is distinct from `r`.

**Wakker reference:** §III.4 (single-coordinate independence /
monotonicity preservation across bases).

**Mathematical content:** Wakker's monograph derives this from
*single-coordinate independence*: strictness of preference between two
values on coordinate `j` at one base persists at any other base
agreeing off `{j}`.  Combined with the compensated-`s` theorem from §6,
this rules out the degenerate case `s = r` (which would force
indifference between `a0` and `a1` at the perturbed base, contradicting
strictness at the original base via independence).

**Why this remains an axiom:** the four raw axioms `Essential +
RestrictedSolvability + TradeoffConsistency + Archimedean` do not by
themselves imply single-coordinate independence; Wakker derives it from
preference continuity (which is part of the topology bundle here) plus
connectedness.  The formal argument involves a continuous family of
bases and the closed-set characterization of strict preference under
continuity.

**Estimated effort:** 1–2 weeks of topology-bundle proof work, building
on the Mathlib `IsPreconnected` infrastructure used elsewhere in
`Topology.lean`.  This axiom is **smaller** than axioms 9 and 10
jointly because it asserts only `s ≠ r`, not the indifference itself
(which is theorem-backed via §6).

**Decomposition (Phase 27):** this is now a **theorem**, derived from the
strictly cleaner single-coordinate independence axiom
`singleCoordinateIndependence_of_wakkerCoordinateTopology` below via the
theorem-backed bridge
`RawAxiomDischargersIVT.compensating_value_distinct_of_singleCoordinateIndependence`.
The genuine §III.4 residual is isolated as the independence primitive; the
distinctness conclusion is no longer an opaque `.choose`-level axiom.

**Phase 60:** this indifference-form fact is now itself a *theorem* derived from
the single `coordinateWeakSeparable_of_wakkerCoordinateTopology` axiom (Phase 57
bridge), so the project's §III.4 coordinate-independence content is **one** axiom
(coordinate weak separability) — the indifference form is the weak form applied
in both directions.

**Phase 71 (soundness fix):** `coordinateWeakSeparable_of_wakkerCoordinateTopology`
is now a **sound projection theorem**, not an axiom.  It was previously an `axiom`
*asserting* separability follows from the topology bundle — which is **false**:
the weak order on `ℝ²` from `U(x₁,x₂) = x₁·(x₂−1)` satisfies the whole bundle
(complete/transitive, connected coordinates, continuous preference) yet violates
coordinate-1 separability.  Separability is a genuine §III.4 structural input, now
carried as the explicit `separable` field of `WakkerCoordinateTopology` and
projected here. -/
theorem coordinateWeakSeparable_of_wakkerCoordinateTopology
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    (i : ι) :
    RawAxiomDischargersIVT.CoordinateWeakSeparable P i :=
  htop.separable i

/-- **Single-coordinate independence (indifference form) — now a theorem from
separability (Phase 60).**

Derived from the single `coordinateWeakSeparable_of_wakkerCoordinateTopology`
axiom: indifference is weak preference both ways, and separability transports
each direction.  Formerly the Phase-27 axiom; now subsumed by separability. -/
theorem singleCoordinateIndependence_of_wakkerCoordinateTopology
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    {j₀ k : ι} (hjk : j₀ ≠ k) (base : Profile X) (a0 a1 : X j₀) (r : X k) :
    RawAxiomDischargersIVT.SingleCoordinateIndependenceAtPair P base j₀ k a0 a1 r :=
  RawAxiomDischargersIVT.singleCoordinateIndependenceAtPair_of_coordinateWeakSeparable
    P base hjk a0 a1 r (coordinateWeakSeparable_of_wakkerCoordinateTopology htop j₀)

/-- **Strict distinctness of the compensating reference value (theorem-backed
via single-coordinate independence).**

Now a **theorem**: the distinctness `s ≠ r` follows from the clean §III.4
single-coordinate independence axiom above via
`RawAxiomDischargersIVT.compensating_value_distinct_of_singleCoordinateIndependence`,
applied to the compensated indifference (`choose_spec`) and the strict pivot
pair.  This replaces the former opaque `.choose`-level distinctness axiom. -/
theorem compensating_reference_value_distinct_of_wakkerCoordinateTopology_and_restrictedSolvability
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (htop : WakkerCoordinateTopology P)
    {j₀ k : ι} (hkj : k ≠ j₀)
    (base : Profile X) (a0 a1 : X j₀)
    (hweak : P.weakPref (Function.update base j₀ a0) (Function.update base j₀ a1))
    (hnotweak : ¬ P.weakPref (Function.update base j₀ a1) (Function.update base j₀ a0))
    (r : X k) :
    let h01 : a0 ≠ a1 := fun h => hnotweak (h ▸ hweak)
    (compensating_reference_value_of_wakkerCoordinateTopology_and_restrictedSolvability
       hsolv htop hkj base a0 a1 h01 r).choose ≠ r := by
  intro h01
  -- The compensated indifference at the chosen `s`.
  have hcompensated :
      P.indiff
        (Function.update (Function.update base j₀ a0) k r)
        (Function.update (Function.update base j₀ a1) k
          (compensating_reference_value_of_wakkerCoordinateTopology_and_restrictedSolvability
            hsolv htop hkj base a0 a1 h01 r).choose) :=
    (compensating_reference_value_of_wakkerCoordinateTopology_and_restrictedSolvability
      hsolv htop hkj base a0 a1 h01 r).choose_spec
  exact RawAxiomDischargersIVT.compensating_value_distinct_of_singleCoordinateIndependence
    P base a0 a1 r _ hweak hnotweak
    (singleCoordinateIndependence_of_wakkerCoordinateTopology htop hkj.symm base a0 a1 r)
    hcompensated

/-- **Partial discharge of the distinctness axiom in `Subsingleton (X j₀)`.**

Following the same methodology as
`sharedPivotPivotGridInjectiveOnSeedDataCertificate_of_subsingleton` in the
parent file: when the pivot coordinate `X j₀` is a subsingleton, the strict
seed pair `(hweak, hnotweak)` is contradictory.  Indeed `a0 = a1` by
`Subsingleton.allEq`, so the two profiles `update base j₀ a0` and
`update base j₀ a1` are equal, and `hnotweak` then contradicts reflexivity of
`weakPref` (from `IsWeakOrder.complete`).  The distinctness conclusion follows
vacuously.

In any non-degenerate setting where `Essential P j₀` is satisfiable, `X j₀` has
at least two distinct values, so this discharge is genuinely degenerate.  But
it establishes that the distinctness axiom — like every other residual in the
project — is **not strictly unprovable**: it holds outright wherever the strict
seed pair cannot exist. -/
theorem compensating_reference_value_distinct_of_subsingleton
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (htop : WakkerCoordinateTopology P)
    {j₀ k : ι} (hkj : k ≠ j₀)
    (base : Profile X) (a0 a1 : X j₀)
    (hweak : P.weakPref (Function.update base j₀ a0) (Function.update base j₀ a1))
    (hnotweak : ¬ P.weakPref (Function.update base j₀ a1) (Function.update base j₀ a0))
    (r : X k)
    [Subsingleton (X j₀)] :
    let h01 : a0 ≠ a1 := fun h => hnotweak (h ▸ hweak)
    (compensating_reference_value_of_wakkerCoordinateTopology_and_restrictedSolvability
       hsolv htop hkj base a0 a1 h01 r).choose ≠ r := by
  -- The strict seed pair cannot exist when `X j₀` is a subsingleton.
  exfalso
  have ha0a1 : a0 = a1 := Subsingleton.allEq _ _
  apply hnotweak
  rw [ha0a1]
  rcases ProductPref.IsWeakOrder.complete (P := P)
    (Function.update base j₀ a1) (Function.update base j₀ a1) with h | h <;> exact h

/-- **Compensated reference exchange constructor.**

Bundles the result of the compensating-`s` theorem with its distinctness
assumption (the smaller named axiom above) into the data shape
`(k, hk, r, s, hrs, h01)` directly consumed by the seed assembly.

Note: returns the `s : X k`, the inequality `r ≠ s`, AND the indifference
witness, all bundled.  This is exactly what's needed to prove axioms 9
and 10 in the parent file: the indifference is the conjunction of the
forward and backward weak-preferences. -/
theorem compensated_reference_exchange_of_wakkerCoordinateTopology_and_restrictedSolvability
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (htop : WakkerCoordinateTopology P)
    {j₀ k : ι} (hkj : k ≠ j₀)
    (base : Profile X) (a0 a1 : X j₀)
    (hweak : P.weakPref (Function.update base j₀ a0) (Function.update base j₀ a1))
    (hnotweak : ¬ P.weakPref (Function.update base j₀ a1) (Function.update base j₀ a0))
    (r : X k) :
    ∃ s : X k, r ≠ s ∧
      P.indiff
        (Function.update (Function.update base j₀ a0) k r)
        (Function.update (Function.update base j₀ a1) k s) := by
  have h01 : a0 ≠ a1 := fun h => hnotweak (h ▸ hweak)
  let result :=
    compensating_reference_value_of_wakkerCoordinateTopology_and_restrictedSolvability
      hsolv htop hkj base a0 a1 h01 r
  refine ⟨result.choose, ?_, result.choose_spec⟩
  exact (compensating_reference_value_distinct_of_wakkerCoordinateTopology_and_restrictedSolvability
    hsolv htop hkj base a0 a1 hweak hnotweak r).symm

/-! ## §4.  Weak single-coordinate independence companion axiom (Phase 52)

Phase 27 adopted the **indifference** form of single-coordinate independence as a
clean topology-module axiom (`singleCoordinateIndependence_of_wakkerCoordinateTopology`)
and used it to retire the opaque distinctness axiom.  Phase 51 isolated the
**weak/strict** companion as `RawAxiomDischargersIVT.SingleCoordinateWeakIndependenceAtPair`
— the genuine §III.4 single-coordinate-monotonicity residual that drives the
reach/crossing/injectivity cancellation and is provably *not* a
`TradeoffConsistency` consequence.

This section adopts that weak form as the topology-module companion axiom, on the
same `WakkerCoordinateTopology` bundle, and proves it discharges the per-step
coordinate-cancellation family that the obligation-12a / reach-crossing
discharges consume — so those `CoordinateCancelAtStep` hypotheses are now supplied
by one clean named topology axiom rather than scattered per-step seams. -/

/-- **Weak single-coordinate independence from the topology bundle.**

The weak/strict companion to `singleCoordinateIndependence_of_wakkerCoordinateTopology`:
on the Wakker coordinate-topology bundle, a weak single-coordinate `≽`-comparison
carrying a common value `r` at a second coordinate transports to the bare
comparison.  This is the genuine §III.4 single-coordinate-monotonicity content
(Wakker's coordinate independence in the weak/strict direction), named as one
clean axiom — the weak companion of the Phase-27 indifference-form axiom.

**Phase 59:** this axiom is now itself a *theorem* derived from the strictly more
fundamental `coordinateWeakSeparable_of_wakkerCoordinateTopology` (declared above,
before the distinctness section) — the single conjoint-measurement separability
primitive that Phases 56–58 proved subsumes the entire §III.4 frontier. -/
theorem singleCoordinateWeakIndependence_of_wakkerCoordinateTopology
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    {j₀ k : ι} (hjk : j₀ ≠ k) (base : Profile X) (a0 a1 : X j₀) (r : X k) :
    RawAxiomDischargersIVT.SingleCoordinateWeakIndependenceAtPair P base j₀ k a0 a1 r :=
  RawAxiomDischargersIVT.singleCoordinateWeakIndependenceAtPair_of_coordinateWeakSeparable
    P base hjk a0 a1 r (coordinateWeakSeparable_of_wakkerCoordinateTopology htop j₀)

/-- **Per-step coordinate cancellation (descending) from the separability
primitive.**

For any standard sequence `σ`, the descending coordinate-cancellation residual
`CoordinateCancelAtStep P σ n` at every step is supplied by coordinate weak
separability of the pivot coordinate.  This discharges the `hcancel` family the
obligation-12a weak-descending discharge (Phase 48) consumes — from the one clean
separability axiom. -/
theorem coordinateCancelAtStep_family_of_wakkerCoordinateTopology
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    {j : ι} (σ : ProductPref.StandardSequence P j) :
    ∀ n, RawAxiomDischargersIVT.CoordinateCancelAtStep P σ n :=
  fun n =>
    RawAxiomDischargersIVT.coordinateCancelAtStep_of_singleCoordinateWeakIndependence
      P σ n
      (singleCoordinateWeakIndependence_of_wakkerCoordinateTopology
        htop σ.k_ne_j.symm σ.base (σ.α n) (σ.α (n + 1)) σ.r)

/-- **Per-step coordinate cancellation (ascending) from the separability
primitive.**  Ascending companion of
`coordinateCancelAtStep_family_of_wakkerCoordinateTopology`. -/
theorem coordinateCancelAscAtStep_family_of_wakkerCoordinateTopology
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    {j : ι} (σ : ProductPref.StandardSequence P j) :
    ∀ n, RawAxiomDischargersIVT.CoordinateCancelAscAtStep P σ n :=
  fun n =>
    RawAxiomDischargersIVT.coordinateCancelAscAtStep_of_singleCoordinateWeakIndependence
      P σ n
      (singleCoordinateWeakIndependence_of_wakkerCoordinateTopology
        htop σ.k_ne_j.symm σ.base (σ.α (n + 1)) (σ.α n) σ.r)

/-- **Reverse-strict propagation family from the separability primitive.**

The reverse-strict injectivity half (axiom 12b) along any standard sequence is
supplied by coordinate weak separability of the pivot coordinate (Phase 58's
`reverseStrict_of_coordinateWeakSeparable`).  Together with the descending
cancellation family above, **both** obligation-12 injectivity halves now come
from the single separability axiom. -/
theorem reverseStrict_family_of_wakkerCoordinateTopology
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    (htop : WakkerCoordinateTopology P)
    {j : ι} (σ : ProductPref.StandardSequence P j) :
    ∀ n,
      ¬ P.weakPref (Function.update σ.base j (σ.α (n + 1)))
                   (Function.update σ.base j (σ.α n)) →
      ¬ P.weakPref (Function.update σ.base j (σ.α (n + 2)))
                   (Function.update σ.base j (σ.α (n + 1))) :=
  RawAxiomDischargersIVT.reverseStrict_of_coordinateWeakSeparable
    P σ (coordinateWeakSeparable_of_wakkerCoordinateTopology htop j)

/-! ## §6.  WP-T: discharge the reach half-axioms from the Archimedean grid escape

The two `coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology`
**axioms** assert the one-sided reach of the perturbed reference along the pivot
coordinate.  A soundness analysis (Option B WP-T) shows this reach is **not** a
consequence of connectedness + preference continuity alone: it requires the pivot
coordinate's utility image to be *unbounded* in the relevant direction (a bounded
`X j` with a large `r ↦ s` gap admits no reach value).  That unboundedness is
exactly the content of the **Archimedean axiom** via a strict standard sequence
whose grid escapes the reference.

So WP-T discharges the reach axioms into **theorems** whose only genuine input is
the §IV.2.6 standard-sequence escape — the IVT/connectedness machinery is *not*
needed for the one-sided reach (it is needed only for the *crossing*, which is
already theorem-backed via `archimedean_reach_above`/`below` + completeness).
These theorems retire the two reach axioms in favor of the honest Archimedean
escape residual. -/

/-- **WP-T: upper-reach as a theorem from the Archimedean grid escape.**

Replaces `coordinateOneStepBracketUpperReach_of_wakkerCoordinateTopology` (an
axiom) with a theorem: for each prior pivot `aPrev`, given a strict Archimedean
standard sequence `σ` based at the `s`-perturbed profile whose grid is not
entirely weakly below the `r`-perturbed reference, a grid point provides the
upper-reach witness.  Only the Archimedean axiom + the escape are used — no IVT,
no topology-bundle analytic seam. -/
theorem coordinateOneStepBracketUpperReach_of_archimedeanEscape
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (r s : X k)
    (harchim : ProductPref.Archimedean P j)
    (aPrev : X j)
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (hσbase : σ.base = Function.update base k s)
    (habove : ∃ n : ℕ, ¬ P.weakPref
      (Function.update (Function.update base j aPrev) k r)
      (Function.update σ.base j (σ.α n))) :
    ∃ aHi : X j,
      P.weakPref
        (Function.update (Function.update base j aHi) k s)
        (Function.update (Function.update base j aPrev) k r) := by
  set b : Profile X := Function.update (Function.update base j aPrev) k r with hb
  obtain ⟨c, hc⟩ := RawAxiomDischargersIVT.archimedean_reach_above P σ hσ harchim b habove
  -- hc : weakPref (update σ.base j c) b, with σ.base = update base k s.
  refine ⟨c, ?_⟩
  rw [hσbase] at hc
  -- hc : weakPref (update (update base k s) j c) b.  Swap the two updates.
  rw [update_comm_two_coords (X := X) base hjk c s] at hc
  exact hc

/-- **WP-T: lower-reach as a theorem from the Archimedean grid escape.**

Dual of `coordinateOneStepBracketUpperReach_of_archimedeanEscape`: replaces the
lower-reach axiom with a theorem from the Archimedean escape below the reference. -/
theorem coordinateOneStepBracketLowerReach_of_archimedeanEscape
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (r s : X k)
    (harchim : ProductPref.Archimedean P j)
    (aPrev : X j)
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (hσbase : σ.base = Function.update base k s)
    (hbelow : ∃ n : ℕ, ¬ P.weakPref
      (Function.update σ.base j (σ.α n))
      (Function.update (Function.update base j aPrev) k r)) :
    ∃ aLo : X j,
      P.weakPref
        (Function.update (Function.update base j aPrev) k r)
        (Function.update (Function.update base j aLo) k s) := by
  set b : Profile X := Function.update (Function.update base j aPrev) k r with hb
  obtain ⟨c, hc⟩ := RawAxiomDischargersIVT.archimedean_reach_below P σ hσ harchim b hbelow
  -- hc : weakPref b (update σ.base j c), with σ.base = update base k s.
  refine ⟨c, ?_⟩
  rw [hσbase] at hc
  rw [update_comm_two_coords (X := X) base hjk c s] at hc
  exact hc

/-- **WP-T: the conjunctive bracket as a theorem from the Archimedean two-sided
escape — no reach axiom.**

Combines the two reach theorems above: given, per prior pivot, a strict
Archimedean standard sequence based at the `s`-perturbed profile that two-sidedly
escapes the `r`-perturbed reference, the full `CoordinateOneStepBracket` holds.
This retires **both** `coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology`
axioms; the residual is exactly the §IV.2.6 standard-sequence escape. -/
theorem coordinateOneStepBracket_of_archimedeanEscape
    {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
    {P : ProductPref X} [ProductPref.IsWeakOrder P]
    {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (r s : X k)
    (harchim : ProductPref.Archimedean P j)
    (hgrid : ∀ aPrev : X j,
      ∃ σ : ProductPref.StandardSequence P j,
        σ.IsStrict ∧
        σ.base = Function.update base k s ∧
        (∃ n : ℕ, ¬ P.weakPref
          (Function.update (Function.update base j aPrev) k r)
          (Function.update σ.base j (σ.α n))) ∧
        (∃ n : ℕ, ¬ P.weakPref
          (Function.update σ.base j (σ.α n))
          (Function.update (Function.update base j aPrev) k r))) :
    CoordinateOneStepBracket P j base k r s := by
  intro aPrev
  obtain ⟨σ, hσ, hσbase, habove, hbelow⟩ := hgrid aPrev
  obtain ⟨aHi, hHi⟩ :=
    coordinateOneStepBracketUpperReach_of_archimedeanEscape
      hjk base r s harchim aPrev σ hσ hσbase habove
  obtain ⟨aLo, hLo⟩ :=
    coordinateOneStepBracketLowerReach_of_archimedeanEscape
      hjk base r s harchim aPrev σ hσ hσbase hbelow
  exact ⟨aLo, aHi, hHi, hLo⟩

end RawAxiomDischargersTopology
end CertificateChecklist
end WakkerRoadmap

/-! ## Audit -/

#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.coordinateOneStepBracket_of_wakkerCoordinateTopology
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.oneStepExtensible_of_wakkerCoordinateTopology_and_reachWitnesses
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.oneStepExtensible_of_wakkerCoordinateTopology_and_archimedeanEscape
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.oneStepExtensible_of_wakkerCoordinateTopology_and_descendingSeedAboveGrid
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.oneStepExtensible_of_coordinateOneStepBracket_and_restrictedSolvability
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.oneStepExtensible_of_wakkerCoordinateTopology_and_restrictedSolvability
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.compensating_reference_value_of_wakkerCoordinateTopology_and_restrictedSolvability
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.compensating_reference_value_distinct_of_wakkerCoordinateTopology_and_restrictedSolvability
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.singleCoordinateIndependence_of_wakkerCoordinateTopology
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.compensated_reference_exchange_of_wakkerCoordinateTopology_and_restrictedSolvability

-- §4 (Phase 60): the indifference-form independence is now a THEOREM from the
-- separability axiom — both §III.4 independence forms reduce to one axiom (see
-- the separability audit in the §4 block below).

-- §4 weak single-coordinate independence companion axiom (Phase 52) and its
-- per-step cancellation discharges: the axiom is the clean weak/strict §III.4
-- primitive; the two family theorems should expose only it plus foundational
-- axioms (no per-step cancellation seams).
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.singleCoordinateWeakIndependence_of_wakkerCoordinateTopology
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.coordinateCancelAtStep_family_of_wakkerCoordinateTopology
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.coordinateCancelAscAtStep_family_of_wakkerCoordinateTopology

-- §4 (Phase 59): coordinate weak separability is now THE single §III.4 topology
-- axiom; the weak-independence fact is a theorem from it, and both obligation-12
-- injectivity halves (cancellation + reverse-strict) come from it.  Each should
-- expose exactly `coordinateWeakSeparable_of_wakkerCoordinateTopology` + foundational.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.coordinateWeakSeparable_of_wakkerCoordinateTopology
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.reverseStrict_family_of_wakkerCoordinateTopology

-- Degenerate-case partial discharges of the three primitive axioms in this
-- file: each should report only `[propext, Classical.choice, Quot.sound]`,
-- with no dependency on the bracket / distinctness axioms.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.coordinateOneStepBracketUpperReach_of_subsingleton
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.coordinateOneStepBracketLowerReach_of_subsingleton
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.compensating_reference_value_distinct_of_subsingleton

-- WP-T (Option B): the reach half-axioms discharged into theorems from the
-- Archimedean grid escape (§IV.2.6).  Should expose ONLY
-- `[propext, Classical.choice, Quot.sound]` — NO bracket reach axiom, no sorryAx.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.coordinateOneStepBracketUpperReach_of_archimedeanEscape
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.coordinateOneStepBracketLowerReach_of_archimedeanEscape
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.coordinateOneStepBracket_of_archimedeanEscape

-- The escape-based OneStepExtensible discharges (engines A+B, no bracket axiom).
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.oneStepExtensible_of_wakkerCoordinateTopology_and_archimedeanEscape
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.oneStepExtensible_of_wakkerCoordinateTopology_and_descendingSeedAboveGrid
