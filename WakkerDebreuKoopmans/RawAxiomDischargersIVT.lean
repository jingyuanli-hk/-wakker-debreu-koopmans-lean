/-
Copyright (c) 2026 Wakker–Debreu–Koopmans project.
SPDX-License-Identifier: Apache-2.0

# Generic-coordinate Intermediate Value infrastructure for the raw-axiom dischargers

This file supplies the **mathematical infrastructure** identified as the common
gap underlying the remaining primitive analytic axioms of the raw-axiom
discharger frontier:

* `coordinateOneStepBracketUpperReach_of_wakkerCoordinateTopology` and
  `coordinateOneStepBracketLowerReach_of_wakkerCoordinateTopology`
  (`RawAxiomDischargersTopology.lean`, Wakker §III.4.2 IVT step);
* the seam underneath
  `pairwiseArchimedeanBaseTransportUpperReach/LowerReachCertificate_from_raw_axioms`
  (`RawAxiomDischargers.lean`, Wakker §IV.3 base transport);
* `pivotCoordinateRetargetingBracketUpper/LowerReachAtPivotCertificate_from_raw_axioms`
  (Wakker §IV.5 + §IV.2 reachability).

## The common shape

Every one of those residuals is, at bottom, a **reachability / betweenness**
statement of the same form: *a continuous one-coordinate slice map hits (or
brackets) a target preference level*.  The existing `Topology.lean` proves the
real-coordinate, post-representation version (using `AdditiveRep` and
`X i = ℝ`).  The dischargers, however, operate on **generic coordinate types**,
directly on the preference relation `≽`, **before** any representation exists.

So the missing infrastructure is a **generic-coordinate Intermediate Value
Theorem stated on the preference relation itself**, derived from:

1. per-coordinate topological **connectedness** (`ConnectedSpace (X j)`); and
2. **preference continuity** (closedness of the `≽`-upper/lower sets), in the
   single-coordinate-slice form.

This file builds exactly that bridge.  The headline result
`coordinate_slice_IVT` is the generic-coordinate IVT: a continuous slice map
`c ↦ update base j c` whose preference-image meets both `≽ b` and `≼ b` must, by
connectedness, contain a point indifferent-or-between relative to `b`.

## Status

The IVT bridge is **theorem-backed** from the named topology bundle
(`WakkerCoordinateTopology`, here re-stated minimally) plus Mathlib's
`IsPreconnected` / `intermediate_value` machinery.  It is the reusable engine
that the topology-module bracket axioms can be discharged through, replacing
their opaque analytic content with a single connectedness/continuity argument.

This file is deliberately **not** in the umbrella import; adopting it in the
consumer means committing to the per-coordinate topology bundle explicitly.
-/
import WakkerDebreuKoopmans.Core
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace RawAxiomDischargersIVT

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

open WakkerInfra
open Function

variable {X : ι → Type v}

/-! ## §1.  Single-coordinate slice continuity

The basic object is the **single-coordinate slice map** `sliceMap base j : X j →
Profile X` sending a coordinate value `c` to the profile `update base j c`.
Preference continuity is then expressed as closedness of the preimages of the
`≽`-upper and `≽`-lower sets under this map. -/

/-- The single-coordinate slice map `c ↦ update base j c`. -/
def sliceMap (base : Profile X) (j : ι) : X j → Profile X :=
  fun c => Function.update base j c

@[simp] lemma sliceMap_apply (base : Profile X) (j : ι) (c : X j) :
    sliceMap base j c = Function.update base j c := rfl

/-- **Slice-restricted preference continuity at a reference profile.**

For a fixed coordinate `j`, base profile, and reference profile `b`, the two
sets of slice values whose updated profile is weakly above / below `b` are
closed in `X j`.  This is the single-coordinate restriction of Wakker's
preference-continuity axiom, and is exactly what an IVT argument on `X j`
consumes. -/
def SliceContinuousAt [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) (base : Profile X) (j : ι) (b : Profile X) : Prop :=
  IsClosed {c : X j | P.weakPref (Function.update base j c) b} ∧
    IsClosed {c : X j | P.weakPref b (Function.update base j c)}

/-! ## §2.  The generic-coordinate Intermediate Value Theorem on `≽`

The engine.  Suppose `X j` is connected and slice-continuous at `b`.  If some
slice value `cHi` is weakly **above** `b` and some slice value `cLo` is weakly
**below** `b`, then — because the two closed sets `{c | update c ≽ b}` and
`{c | b ≽ update c}` cover `X j` (completeness of the weak order) and `X j` is
connected — they must intersect, i.e. there is a slice value whose updated
profile is **indifferent** to `b`.

This is the abstract IVT: connectedness forbids a clopen partition, and
completeness makes the two closed sets a cover, so a continuous "sign change"
forces an exact crossing. -/

/-- **Generic-coordinate IVT on the preference relation.**

If coordinate `j` is connected and slice-continuous at `b`, and there exist
slice values bracketing `b` from above and below, then some slice value is
**indifferent** to `b`.

Proof: the upper set `U = {c | update c ≽ b}` and lower set `L = {c | b ≽ update c}`
are closed (slice continuity).  By completeness of the weak order, `U ∪ L =
univ`.  If `U ∩ L = ∅`, then `U` and `L` are disjoint closed sets covering the
connected space `X j`, both nonempty (the bracketing witnesses), contradicting
connectedness (a connected space is not the union of two disjoint nonempty
closed sets).  Hence `U ∩ L ≠ ∅`, and any `c ∈ U ∩ L` gives `update c ∼ b`. -/
theorem coordinate_slice_IVT [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j : ι) (b : Profile X)
    [hconn : ConnectedSpace (X j)]
    (hcont : SliceContinuousAt P base j b)
    {cHi cLo : X j}
    (hHi : P.weakPref (Function.update base j cHi) b)
    (hLo : P.weakPref b (Function.update base j cLo)) :
    ∃ c : X j, P.indiff (Function.update base j c) b := by
  classical
  set U : Set (X j) := {c : X j | P.weakPref (Function.update base j c) b} with hU
  set L : Set (X j) := {c : X j | P.weakPref b (Function.update base j c)} with hL
  -- U and L are closed.
  have hUclosed : IsClosed U := hcont.1
  have hLclosed : IsClosed L := hcont.2
  -- They cover the universe by completeness.
  have hcover : U ∪ L = Set.univ := by
    apply Set.eq_univ_of_forall
    intro c
    rcases ProductPref.IsWeakOrder.complete (P := P)
      (Function.update base j c) b with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- The intersection is nonempty.  Suppose not.
  by_contra hne
  push_neg at hne
  have hempty : U ∩ L = (∅ : Set (X j)) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hcU, hcL⟩
    exact hne c ⟨hcU, hcL⟩
  -- Then U is clopen: U = Lᶜ (since they partition univ), and L is closed.
  have hU_eq_compl : U = Lᶜ := by
    ext c
    constructor
    · intro hcU hcL
      have : c ∈ U ∩ L := ⟨hcU, hcL⟩
      rw [hempty] at this
      exact this
    · intro hcL
      have : c ∈ U ∪ L := by rw [hcover]; exact Set.mem_univ c
      rcases this with h | h
      · exact h
      · exact absurd h hcL
  have hUopen : IsOpen U := by
    rw [hU_eq_compl]
    exact hLclosed.isOpen_compl
  have hUclopen : IsClopen U := ⟨hUclosed, hUopen⟩
  -- U is nonempty (cHi) and not univ (cLo ∉ U unless cLo also in L, impossible).
  have hUne : U.Nonempty := ⟨cHi, hHi⟩
  -- In a connected space, the only clopen sets are ∅ and univ.
  rcases (isClopen_iff.mp hUclopen) with hUe | hUu
  · -- U = ∅ contradicts hUne.
    rw [hUe] at hUne
    exact absurd hUne (by simp)
  · -- U = univ.  Then cLo ∈ U, i.e. update cLo ≽ b.  Combined with b ≽ update cLo
    -- gives indiff, contradicting hne cLo.
    have hcLoU : cLo ∈ U := by rw [hUu]; exact Set.mem_univ cLo
    have hcLoL : cLo ∈ L := hLo
    exact hne cLo ⟨hcLoU, hcLoL⟩

/-- **Bracketing corollary of the IVT.**

The indifferent crossing point in particular *brackets* `b` from both sides: its
updated profile is both weakly above and weakly below `b`.  This is the exact
shape consumed by the topology-module bracket axioms (each direction
separately). -/
theorem coordinate_slice_bracket [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j : ι) (b : Profile X)
    [ConnectedSpace (X j)]
    (hcont : SliceContinuousAt P base j b)
    {cHi cLo : X j}
    (hHi : P.weakPref (Function.update base j cHi) b)
    (hLo : P.weakPref b (Function.update base j cLo)) :
    ∃ c : X j,
      P.weakPref (Function.update base j c) b ∧
      P.weakPref b (Function.update base j c) := by
  obtain ⟨c, hc⟩ := coordinate_slice_IVT P base j b hcont hHi hLo
  exact ⟨c, hc.1, hc.2⟩

/-! ## §3.  Bridge from product preference continuity to slice continuity

The single-coordinate slice map `c ↦ update base j c` is continuous in the
product topology (it agrees with `base` off `j` and is the identity at `j`).
Hence the preimage of any closed `≽`-set under it is closed in `X j`, giving
`SliceContinuousAt` from the global product-topology preference continuity used
in `RawAxiomDischargersTopology.lean`. -/

/-- The single-coordinate slice map is continuous in the product topology. -/
theorem continuous_sliceMap [∀ i, TopologicalSpace (X i)]
    (base : Profile X) (j : ι) :
    Continuous (fun c : X j => Function.update base j c) := by
  -- `update base j c i` is continuous in `c` for each coordinate `i`:
  -- it is either `c` (when `i = j`) or the constant `base i`.
  refine continuous_pi (fun i => ?_)
  by_cases hij : i = j
  · subst hij
    simpa using (continuous_id)
  · simpa [Function.update_of_ne hij] using continuous_const

/-- **Global product-topology preference continuity ⇒ slice continuity.**

If the `≽`-upper and `≽`-lower sets at `b` are closed in the product topology
on `Profile X`, then their preimages under the continuous slice map are closed
in `X j`, i.e. `SliceContinuousAt` holds.  This connects the global
`PreferenceContinuous` predicate (as used in the topology bundle) to the
slice-restricted form the IVT consumes. -/
theorem sliceContinuousAt_of_preferenceContinuous [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) (base : Profile X) (j : ι) (b : Profile X)
    (hUpper : IsClosed {x : Profile X | P.weakPref x b})
    (hLower : IsClosed {x : Profile X | P.weakPref b x}) :
    SliceContinuousAt P base j b := by
  refine ⟨?_, ?_⟩
  · -- {c | update c ≽ b} = (sliceMap)⁻¹ {x | x ≽ b}.
    have : {c : X j | P.weakPref (Function.update base j c) b}
        = (fun c : X j => Function.update base j c) ⁻¹' {x : Profile X | P.weakPref x b} := by
      ext c; simp
    rw [this]
    exact hUpper.preimage (continuous_sliceMap base j)
  · have : {c : X j | P.weakPref b (Function.update base j c)}
        = (fun c : X j => Function.update base j c) ⁻¹' {x : Profile X | P.weakPref b x} := by
      ext c; simp
    rw [this]
    exact hLower.preimage (continuous_sliceMap base j)

/-- **End-to-end generic-coordinate IVT from product preference continuity.**

The headline consumer: from per-coordinate connectedness and *global* product-
topology preference continuity (the two ingredients of the Wakker topology
bundle), a bracketing pair `cHi, cLo` produces an indifferent crossing point.
This is the reusable engine the bracket axioms of
`RawAxiomDischargersTopology.lean` route through. -/
theorem coordinate_slice_IVT_of_preferenceContinuous [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j : ι) (b : Profile X)
    [ConnectedSpace (X j)]
    (hUpper : IsClosed {x : Profile X | P.weakPref x b})
    (hLower : IsClosed {x : Profile X | P.weakPref b x})
    {cHi cLo : X j}
    (hHi : P.weakPref (Function.update base j cHi) b)
    (hLo : P.weakPref b (Function.update base j cLo)) :
    ∃ c : X j, P.indiff (Function.update base j c) b :=
  coordinate_slice_IVT P base j b
    (sliceContinuousAt_of_preferenceContinuous P base j b hUpper hLower) hHi hLo

/-! ## §4.  Engine B: Archimedean ⇒ reach / unboundedness

The IVT engine (§2–§3) consumes *reach witnesses*: a slice value above `b` and
one below `b`.  Those witnesses are the genuine residual content Wakker (1989)
§IV.2.6 derives from the **Archimedean axiom** — a strict standard sequence is
preference-unbounded, so its grid escapes any candidate bound.

This section mechanizes that reach content directly from the raw Archimedean
axiom, as the contrapositive of the no-sandwich statement.  No topology and no
representation are used here; this is pure order theory on `≽`. -/

/-- **Archimedean reach (raw form).**

The Archimedean axiom says a strict standard sequence `σ` admits **no** pair
`(lo, hi)` sandwiching every grid point `Function.update σ.base j (σ.α n)`.
Contrapositively: for *any* candidate bounds `lo, hi`, some grid index `n`
**escapes** the sandwich — either the upper bound fails (`¬ hi ≽ α n`) or the
lower bound fails (`¬ α n ≽ lo`).

This is the order-theoretic core of Wakker §IV.2.6 reach: the grid is unbounded,
so it reaches past any fixed pair of bounds.  Fully theorem-backed from the
`Archimedean` predicate; no topology. -/
theorem archimedean_grid_escapes
    (P : ProductPref X) {j : ι}
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (lo hi : Profile X) :
    ∃ n : ℕ,
      ¬ P.weakPref hi (Function.update σ.base j (σ.α n)) ∨
      ¬ P.weakPref (Function.update σ.base j (σ.α n)) lo := by
  have hno := harchim σ hσ
  by_contra hcontra
  push_neg at hcontra
  -- hcontra : ∀ n, (hi ≽ α n) ∧ (α n ≽ lo) after pushing the De Morgan / double-neg.
  exact hno ⟨lo, hi, fun n => ⟨(hcontra n).1, (hcontra n).2⟩⟩

/-- **Single-sided Archimedean reach below a reference profile.**

If, in addition to strictness + Archimedean, the grid is *weakly descending*
(each step `α n ≽ α (n+1)` at base — the monotone direction supplied by Wakker's
standard-sequence construction), then for any reference profile `b` that the
grid does **not** stay weakly above, some grid point lands weakly below `b`.

This is the lower-reach witness the IVT consumes: it provides the `cLo` with
`b ≽ update base j cLo`.  The descending hypothesis is engine B's genuine
residual (the reference-direction / monotonicity content); the escape itself is
the Archimedean contrapositive above. -/
theorem archimedean_reach_below
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (b : Profile X)
    (hbelow : ∃ n : ℕ, ¬ P.weakPref (Function.update σ.base j (σ.α n)) b) :
    ∃ c : X j, P.weakPref b (Function.update σ.base j c) := by
  obtain ⟨n, hn⟩ := hbelow
  -- `¬ (update (α n) ≽ b)`; by completeness `b ≽ update (α n)`.
  refine ⟨σ.α n, ?_⟩
  rcases ProductPref.IsWeakOrder.complete (P := P)
    b (Function.update σ.base j (σ.α n)) with h | h
  · exact h
  · exact absurd h hn

/-- **Single-sided Archimedean reach above a reference profile.**

Dual of `archimedean_reach_below`: if some grid point is not weakly below `b`,
then some grid point lands weakly above `b`, providing the `cHi` witness with
`update base j cHi ≽ b`. -/
theorem archimedean_reach_above
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (b : Profile X)
    (habove : ∃ n : ℕ, ¬ P.weakPref b (Function.update σ.base j (σ.α n))) :
    ∃ c : X j, P.weakPref (Function.update σ.base j c) b := by
  obtain ⟨n, hn⟩ := habove
  refine ⟨σ.α n, ?_⟩
  rcases ProductPref.IsWeakOrder.complete (P := P)
    (Function.update σ.base j (σ.α n)) b with h | h
  · exact h
  · exact absurd h hn

/-! ## §5.  Engines A + B composed: IVT crossing from Archimedean escape

Combining §2–§3 (engine A, the IVT) with §4 (engine B, Archimedean reach):
given connectedness, preference continuity, and the **two-sided escape** of the
strict Archimedean grid past a reference profile `b`, there is a slice value
*indifferent* to `b`.  This is `OneStepExtensible`-shaped at the level of a
single reference profile, with the reach reduced to the grid-escape residual. -/

/-- **IVT crossing from Archimedean two-sided escape.**

If coordinate `j` is connected and preference-continuous at `b`, the grid is a
strict Archimedean standard sequence, and the grid escapes `b` on **both** sides
(some point not weakly below `b`, some point not weakly above `b`), then some
slice value (over `σ.base`) is indifferent to `b`.

The escape hypotheses are engine B (Archimedean reach); the crossing is engine A
(the IVT).  Fully theorem-backed from those two named inputs — no analytic
axiom. -/
theorem archimedean_slice_crossing [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    [ConnectedSpace (X j)]
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (b : Profile X)
    (hUpper : IsClosed {x : Profile X | P.weakPref x b})
    (hLower : IsClosed {x : Profile X | P.weakPref b x})
    (habove : ∃ n : ℕ, ¬ P.weakPref b (Function.update σ.base j (σ.α n)))
    (hbelow : ∃ n : ℕ, ¬ P.weakPref (Function.update σ.base j (σ.α n)) b) :
    ∃ c : X j, P.indiff (Function.update σ.base j c) b := by
  obtain ⟨cHi, hHi⟩ := archimedean_reach_above P σ hσ harchim b habove
  obtain ⟨cLo, hLo⟩ := archimedean_reach_below P σ hσ harchim b hbelow
  exact coordinate_slice_IVT_of_preferenceContinuous
    P σ.base j b hUpper hLower hHi hLo

/-! ## §6.  Engine B refinement: monotone grids escape automatically

The escape hypotheses fed to `archimedean_slice_crossing` are not arbitrary: in
Wakker's construction the standard-sequence grid is **monotone** (weakly
descending in the relevant direction).  For a weakly-descending grid the *upper*
bound is free — the whole grid sits weakly below the first point `α 0` — so the
Archimedean no-sandwich axiom forces the *lower* escape automatically, with no
escape hypothesis at all.  This further shrinks engine B's residual: only the
monotone-step property is needed, not an a-priori escape witness. -/

/-- A weakly-descending grid is bounded above by its first point: `α 0 ≽ α n`
for every `n`.  Pure induction with weak-order transitivity. -/
theorem weaklyDescending_grid_le_first
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j : ι) (α : ℕ → X j)
    (hdesc : ∀ n, P.weakPref (Function.update base j (α n))
                             (Function.update base j (α (n + 1))))
    (n : ℕ) :
    P.weakPref (Function.update base j (α 0)) (Function.update base j (α n)) := by
  induction n with
  | zero =>
      rcases ProductPref.IsWeakOrder.complete (P := P)
        (Function.update base j (α 0)) (Function.update base j (α 0)) with h | h <;> exact h
  | succ m ih =>
      exact ProductPref.IsWeakOrder.transitive _ _ _ ih (hdesc m)

/-- **Automatic lower escape for a weakly-descending Archimedean grid.**

If the strict standard sequence `σ` is weakly descending at its base, then for
**any** reference profile `b`, the grid escapes below `b` — no escape hypothesis
needed.  Proof: the descending grid is bounded above by `α 0`; if it never fell
weakly below `b`, then `(b, α 0)` would sandwich the whole grid, contradicting
the Archimedean axiom.  Hence some grid point is not weakly above `b`. -/
theorem archimedean_weaklyDescending_escape_below
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (hdesc : ∀ n, P.weakPref (Function.update σ.base j (σ.α n))
                             (Function.update σ.base j (σ.α (n + 1))))
    (b : Profile X) :
    ∃ n : ℕ, ¬ P.weakPref (Function.update σ.base j (σ.α n)) b := by
  by_contra hcontra
  push_neg at hcontra
  -- hcontra : ∀ n, α n ≽ b.  Combined with α 0 ≽ α n, the pair (b, α 0) sandwiches.
  exact harchim σ hσ
    ⟨b, Function.update σ.base j (σ.α 0),
      fun n => ⟨weaklyDescending_grid_le_first P σ.base j σ.α hdesc n, hcontra n⟩⟩

/-- A weakly-ascending grid is bounded below by its first point: `α n ≽ α 0`
for every `n`.  Dual of `weaklyDescending_grid_le_first`; pure induction with
weak-order transitivity. -/
theorem weaklyAscending_grid_ge_first
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j : ι) (α : ℕ → X j)
    (hasc : ∀ n, P.weakPref (Function.update base j (α (n + 1)))
                            (Function.update base j (α n)))
    (n : ℕ) :
    P.weakPref (Function.update base j (α n)) (Function.update base j (α 0)) := by
  induction n with
  | zero =>
      rcases ProductPref.IsWeakOrder.complete (P := P)
        (Function.update base j (α 0)) (Function.update base j (α 0)) with h | h <;> exact h
  | succ m ih =>
      exact ProductPref.IsWeakOrder.transitive _ _ _ (hasc m) ih

/-- **Automatic upper escape for a weakly-ascending Archimedean grid.**

Dual of `archimedean_weaklyDescending_escape_below`: if the strict standard
sequence `σ` is weakly *ascending* at its base, then for **any** reference
profile `b`, the grid escapes above `b` — no escape hypothesis needed.  Proof:
the ascending grid is bounded below by `α 0`; if it never rose above `b`, then
`(α 0, b)` would sandwich the whole grid, contradicting the Archimedean axiom.
Hence some grid point is not weakly below `b`. -/
theorem archimedean_weaklyAscending_escape_above
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (hasc : ∀ n, P.weakPref (Function.update σ.base j (σ.α (n + 1)))
                            (Function.update σ.base j (σ.α n)))
    (b : Profile X) :
    ∃ n : ℕ, ¬ P.weakPref b (Function.update σ.base j (σ.α n)) := by
  by_contra hcontra
  push_neg at hcontra
  -- hcontra : ∀ n, b ≽ α n.  Combined with α n ≽ α 0, the pair (α 0, b) sandwiches.
  exact harchim σ hσ
    ⟨Function.update σ.base j (σ.α 0), b,
      fun n => ⟨hcontra n, weaklyAscending_grid_ge_first P σ.base j σ.α hasc n⟩⟩

/-- **One-sided IVT crossing for a weakly-descending Archimedean grid.**

Combining §6's automatic lower escape with §5's two-sided crossing: for a
weakly-descending strict Archimedean grid on a connected, preference-continuous
coordinate, the lower escape is free, so only the **upper** escape (some grid
point not weakly below `b`) is needed to produce the indifferent crossing.

This is the leanest engine-B residual: a single upper-escape witness (the grid
reaches above `b`), with everything else — the lower escape, the reach
mechanism, and the IVT crossing — theorem-backed. -/
theorem archimedean_weaklyDescending_slice_crossing [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    [ConnectedSpace (X j)]
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (hdesc : ∀ n, P.weakPref (Function.update σ.base j (σ.α n))
                             (Function.update σ.base j (σ.α (n + 1))))
    (b : Profile X)
    (hUpper : IsClosed {x : Profile X | P.weakPref x b})
    (hLower : IsClosed {x : Profile X | P.weakPref b x})
    (habove : ∃ n : ℕ, ¬ P.weakPref b (Function.update σ.base j (σ.α n))) :
    ∃ c : X j, P.indiff (Function.update σ.base j c) b :=
  archimedean_slice_crossing P σ hσ harchim b hUpper hLower habove
    (archimedean_weaklyDescending_escape_below P σ hσ harchim hdesc b)

/-- **Crossing for a weakly-descending Archimedean grid seeded above `b`.**

The fully-reduced engine-B form: when the grid's first point `α 0` is **not
weakly below** `b` (the natural seed condition — the descending grid starts at
or above the target), the upper escape is witnessed at `n = 0`, the lower escape
is automatic from descent, and the IVT supplies the crossing.  **No escape
hypothesis at all** beyond the seed-above condition.

This is the cleanest possible engine-B residual: the only inputs are the
topology bundle (connectedness + continuity), the strict descending Archimedean
grid, and the seed condition `¬ b ≽ α 0`.  Everything analytic is
theorem-backed. -/
theorem archimedean_weaklyDescending_slice_crossing_of_seedAbove
    [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    [ConnectedSpace (X j)]
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (hdesc : ∀ n, P.weakPref (Function.update σ.base j (σ.α n))
                             (Function.update σ.base j (σ.α (n + 1))))
    (b : Profile X)
    (hUpper : IsClosed {x : Profile X | P.weakPref x b})
    (hLower : IsClosed {x : Profile X | P.weakPref b x})
    (hseed : ¬ P.weakPref b (Function.update σ.base j (σ.α 0))) :
    ∃ c : X j, P.indiff (Function.update σ.base j c) b :=
  archimedean_weaklyDescending_slice_crossing
    P σ hσ harchim hdesc b hUpper hLower ⟨0, hseed⟩

/-- **One-sided IVT crossing for a weakly-ascending Archimedean grid.**

Dual of `archimedean_weaklyDescending_slice_crossing`: for a weakly-ascending
strict Archimedean grid, the *upper* escape is automatic
(`archimedean_weaklyAscending_escape_above`), so only the **lower** escape (some
grid point not weakly above `b`) is needed to produce the indifferent crossing. -/
theorem archimedean_weaklyAscending_slice_crossing [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    [ConnectedSpace (X j)]
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (hasc : ∀ n, P.weakPref (Function.update σ.base j (σ.α (n + 1)))
                            (Function.update σ.base j (σ.α n)))
    (b : Profile X)
    (hUpper : IsClosed {x : Profile X | P.weakPref x b})
    (hLower : IsClosed {x : Profile X | P.weakPref b x})
    (hbelow : ∃ n : ℕ, ¬ P.weakPref (Function.update σ.base j (σ.α n)) b) :
    ∃ c : X j, P.indiff (Function.update σ.base j c) b :=
  archimedean_slice_crossing P σ hσ harchim b hUpper hLower
    (archimedean_weaklyAscending_escape_above P σ hσ harchim hasc b) hbelow

/-- **Crossing for a weakly-ascending Archimedean grid seeded below `b`.**

Dual of `archimedean_weaklyDescending_slice_crossing_of_seedAbove`: when the
grid's first point `α 0` is **not weakly above** `b` (the ascending grid starts
at or below the target), the lower escape is witnessed at `n = 0`, the upper
escape is automatic from ascent, and the IVT supplies the crossing.  No escape
hypothesis beyond the seed-below condition. -/
theorem archimedean_weaklyAscending_slice_crossing_of_seedBelow
    [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    [ConnectedSpace (X j)]
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (hasc : ∀ n, P.weakPref (Function.update σ.base j (σ.α (n + 1)))
                            (Function.update σ.base j (σ.α n)))
    (b : Profile X)
    (hUpper : IsClosed {x : Profile X | P.weakPref x b})
    (hLower : IsClosed {x : Profile X | P.weakPref b x})
    (hseed : ¬ P.weakPref (Function.update σ.base j (σ.α 0)) b) :
    ∃ c : X j, P.indiff (Function.update σ.base j c) b :=
  archimedean_weaklyAscending_slice_crossing
    P σ hσ harchim hasc b hUpper hLower ⟨0, hseed⟩

/-! ## §7.  The unifying residual: reference-direction monotonicity

Phase 25 identified that the genuine residual underlying the
extensibility/injectivity frontier — the `spaced ⟹ weakly-descending` bridge —
is a single **reference-direction monotonicity** fact on the auxiliary
coordinate `k`.  This section names that primitive cleanly and proves it
theorem-backs the descending property, isolating it as the one remaining
order-theoretic input.

### The two ingredients

The spaced indifference of a standard sequence is
`(α n at j, r at k) ∼ (α (n+1) at j, s at k)`.  To extract the descending
property `(α n at j) ≽ (α (n+1) at j)` (with `k` held at a common value), two
facts suffice:

* **reference direction** — moving `k` from `s` to `r` is weakly preferred, at
  the relevant `j`-values; and
* **coordinate independence at `k`** — a single-`k` comparison transports across
  the `j`-value (so the `k`-difference can be cancelled).

Both are §III.4 single-coordinate facts that `TradeoffConsistency` alone does
not supply; together they are the unifying residual. -/

/-- **Reference-direction monotonicity at a standard sequence's grid step.**

States the §III.4 single-coordinate fact in the exact form the descending bridge
consumes: at each grid step `n`, moving the auxiliary coordinate `k` from `s`
back to `r` (holding the pivot at the *successor* value `α (n+1)`) is weakly
preferred.  This is the "reference exchange is in the descending direction"
content. -/
def ReferenceDirectionAtStep
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j) (n : ℕ) : Prop :=
  P.weakPref
    (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.r)
    (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.s)

/-- **Coordinate-independence cancellation at a standard sequence's grid step.**

The §III.4 single-coordinate independence fact in the form the bridge consumes:
the `≽`-comparison between two `j`-values, carrying a common `k`-value `r`,
transports to the bare `j`-comparison (with `k` cancelled to its base value).
Concretely, preferring `(α n, r at k)` over `(α (n+1), r at k)` yields preferring
`α n` over `α (n+1)` at the base. -/
def CoordinateCancelAtStep
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j) (n : ℕ) : Prop :=
  P.weakPref
      (Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r)
      (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.r) →
    P.weakPref
      (Function.update σ.base j (σ.α n))
      (Function.update σ.base j (σ.α (n + 1)))

/-- **The `spaced ⟹ weakly-descending` bridge via coordinate cancellation.**

Given the transported `r`-carrying comparison `(α n, r at k) ≽ (α (n+1), r at k)`
and the coordinate-cancellation fact at step `n`, the bare descending property
`(α n at j) ≽ (α (n+1) at j)` follows by cancelling the common `k`-value.

This isolates the genuine §III.4 content as exactly the two single-coordinate
inputs (the transported comparison and the cancellation), with the descending
property — the `hdesc` hypothesis the IVT crossing consumes — derived. -/
theorem descendingStep_of_referenceDirection_and_cancel
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j) (n : ℕ)
    (htransported :
      P.weakPref
        (Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r)
        (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.r))
    (hcancel : CoordinateCancelAtStep P σ n) :
    P.weakPref
      (Function.update σ.base j (σ.α n))
      (Function.update σ.base j (σ.α (n + 1))) :=
  hcancel htransported

/-- **All-steps descending from a family of transported comparisons +
cancellations.**

If at every step the transported `r`-carrying comparison holds and coordinate
cancellation applies, then the grid is weakly descending — exactly the `hdesc`
hypothesis the IVT crossing consumes.  This packages the bridge across all
steps, reducing the descending property to the per-step reference-direction /
cancellation residual. -/
theorem weaklyDescending_of_referenceDirection_and_cancel
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (htransported : ∀ n,
      P.weakPref
        (Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r)
        (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.r))
    (hcancel : ∀ n, CoordinateCancelAtStep P σ n) :
    ∀ n, P.weakPref
      (Function.update σ.base j (σ.α n))
      (Function.update σ.base j (σ.α (n + 1))) :=
  fun n => descendingStep_of_referenceDirection_and_cancel P σ n (htransported n) (hcancel n)

/-- **Fully-composed crossing from the unified reference-direction residual.**

The capstone: the IVT crossing for a standard-sequence grid follows from

* the topology inputs (connectedness via the `ConnectedSpace` instance,
  preference continuity via the closed `≽`-sets);
* the raw `Archimedean P j` axiom;
* the **unified residual** — per step, the transported `r`-carrying comparison
  and coordinate cancellation (which give the descending property); and
* the seed-above condition.

Every analytic and order-theoretic ingredient is theorem-backed; the inputs
`htransported` + `hcancel` are exactly the §III.4 reference-direction monotonicity
content, now the *single* named residual.  This is the complete reduction of the
extensibility crossing to that one primitive. -/
theorem archimedean_slice_crossing_of_referenceDirection [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    [ConnectedSpace (X j)]
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (htransported : ∀ n,
      P.weakPref
        (Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r)
        (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.r))
    (hcancel : ∀ n, CoordinateCancelAtStep P σ n)
    (b : Profile X)
    (hUpper : IsClosed {x : Profile X | P.weakPref x b})
    (hLower : IsClosed {x : Profile X | P.weakPref b x})
    (hseed : ¬ P.weakPref b (Function.update σ.base j (σ.α 0))) :
    ∃ c : X j, P.indiff (Function.update σ.base j c) b :=
  archimedean_weaklyDescending_slice_crossing_of_seedAbove
    P σ hσ harchim
    (weaklyDescending_of_referenceDirection_and_cancel P σ htransported hcancel)
    b hUpper hLower hseed

/-- **Reverse reference-direction monotonicity at a grid step.**

The descending-orientation companion of `ReferenceDirectionAtStep`: at each grid
step `n`, moving the auxiliary coordinate `k` from `r` to `s` (holding the pivot
at the *successor* value `α (n+1)`) is weakly preferred.  This is the
"reference exchange is in the *ascending* `k`-direction" content, which drives
the **descending** `j`-grid (each `j`-step trades against an upward `k`-move). -/
def ReverseReferenceDirectionAtStep
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j) (n : ℕ) : Prop :=
  P.weakPref
    (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.s)
    (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.r)

/-- **The transported `r`-carrying comparison from `spaced` + reverse reference
direction (descending orientation).**

Descending dual of `transportedComparison_of_spaced_and_referenceDirection`: the
`spaced` field gives `(α n, r) ∼ (α (n+1), s)`, so `(α n, r) ≽ (α (n+1), s)`;
composing with `ReverseReferenceDirectionAtStep` (`(α (n+1), s) ≽ (α (n+1), r)`)
by transitivity yields the descending transported comparison
`(α n, r) ≽ (α (n+1), r)`.  So the transported comparison consumed by the
descending bridge is **not** a separate residual: it follows from `spaced` (free)
plus the single reverse-reference-direction fact. -/
theorem transportedComparison_of_spaced_and_reverseReferenceDirection
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j) (n : ℕ)
    (hrev : ReverseReferenceDirectionAtStep P σ n) :
    P.weakPref
      (Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r)
      (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.r) :=
  -- (α n, r) ≽ (α(n+1), s)   [spaced n, first component]
  -- (α(n+1), s) ≽ (α(n+1), r) [reverse reference direction]
  ProductPref.IsWeakOrder.transitive _ _ _ (σ.spaced n).1 hrev

/-- **`spaced` + reverse reference direction + cancellation ⟹ weakly
descending.**

The descending analogue of `weaklyAscending_of_spaced_referenceDirection_and_cancel`,
with the transported comparison *derived* from `spaced` (reverse reference
direction is the only genuine input besides cancellation).  Produces exactly the
`hdesc` hypothesis the descending IVT crossing consumes. -/
theorem weaklyDescending_of_spaced_reverseReferenceDirection_and_cancel
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hrev : ∀ n, ReverseReferenceDirectionAtStep P σ n)
    (hcancel : ∀ n, CoordinateCancelAtStep P σ n) :
    ∀ n, P.weakPref
      (Function.update σ.base j (σ.α n))
      (Function.update σ.base j (σ.α (n + 1))) :=
  fun n => hcancel n
    (transportedComparison_of_spaced_and_reverseReferenceDirection P σ n (hrev n))

/-- **Fully-composed descending crossing from `spaced` + reverse reference
direction.**

The descending capstone, tighter than `archimedean_slice_crossing_of_referenceDirection`:
it consumes the standard sequence's own `spaced` field plus the reverse
reference-direction fact (instead of a separately-postulated transported
comparison) and the cancellation, producing the indifferent crossing from the
seed-above condition. -/
theorem archimedean_descending_slice_crossing_of_reverseReferenceDirection
    [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    [ConnectedSpace (X j)]
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (hrev : ∀ n, ReverseReferenceDirectionAtStep P σ n)
    (hcancel : ∀ n, CoordinateCancelAtStep P σ n)
    (b : Profile X)
    (hUpper : IsClosed {x : Profile X | P.weakPref x b})
    (hLower : IsClosed {x : Profile X | P.weakPref b x})
    (hseed : ¬ P.weakPref b (Function.update σ.base j (σ.α 0))) :
    ∃ c : X j, P.indiff (Function.update σ.base j c) b :=
  archimedean_weaklyDescending_slice_crossing_of_seedAbove
    P σ hσ harchim
    (weaklyDescending_of_spaced_reverseReferenceDirection_and_cancel P σ hrev hcancel)
    b hUpper hLower hseed

/-! ### Uniform reference direction: the family is one slice-fact repeated

Both `ReferenceDirectionAtStep` and `ReverseReferenceDirectionAtStep` are, at each
`n`, the *same* `k`-coordinate comparison between `σ.r` and `σ.s`, evaluated at
the base `update σ.base j (σ.α (n+1))` — they differ across `n` only in the
`j`-value.  So the entire n-indexed family is a single **uniform** `k`-exchange
direction that holds at *every* `j`-slice.  Naming that uniform fact collapses the
family to one predicate, instantiated per step. -/

/-- **Uniform reference direction.**  The `k`-exchange `r ≽ s` holds at every
`j`-slice (every value `v : X j` of the pivot coordinate). -/
def UniformReferenceDirection
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j) : Prop :=
  ∀ v : X j,
    P.weakPref
      (Function.update (Function.update σ.base j v) σ.k σ.r)
      (Function.update (Function.update σ.base j v) σ.k σ.s)

/-- **Uniform reverse reference direction.**  The `k`-exchange `s ≽ r` holds at
every `j`-slice. -/
def UniformReverseReferenceDirection
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j) : Prop :=
  ∀ v : X j,
    P.weakPref
      (Function.update (Function.update σ.base j v) σ.k σ.s)
      (Function.update (Function.update σ.base j v) σ.k σ.r)

/-- **The reference-direction family from one uniform fact.**

`∀ n, ReferenceDirectionAtStep P σ n` is just `UniformReferenceDirection`
instantiated at the successor grid values `v := σ.α (n+1)`.  So the per-step
family is one uniform `k`-exchange direction, not infinitely many separate
facts. -/
theorem referenceDirectionAtStep_family_of_uniform
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j)
    (huniform : UniformReferenceDirection P σ) :
    ∀ n, ReferenceDirectionAtStep P σ n :=
  fun n => huniform (σ.α (n + 1))

/-- **The reverse-reference-direction family from one uniform fact.**  Dual of
`referenceDirectionAtStep_family_of_uniform`. -/
theorem reverseReferenceDirectionAtStep_family_of_uniform
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j)
    (huniform : UniformReverseReferenceDirection P σ) :
    ∀ n, ReverseReferenceDirectionAtStep P σ n :=
  fun n => huniform (σ.α (n + 1))

/-- **The transported `r`-carrying comparison from `spaced` + reference
direction (ascending orientation).**

The standard sequence's own `spaced` field already gives
`(α n, r) ∼ (α (n+1), s)`.  Composing with `ReferenceDirectionAtStep`
(`(α (n+1), r) ≽ (α (n+1), s)`) by transitivity yields the transported
comparison `(α (n+1), r) ≽ (α n, r)` — the *ascending* direction.  This shows
the transported comparison is **not** a separate residual: it follows from
`spaced` (free) plus the single reference-direction fact. -/
theorem transportedComparison_of_spaced_and_referenceDirection
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j) (n : ℕ)
    (hrefdir : ReferenceDirectionAtStep P σ n) :
    P.weakPref
      (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.r)
      (Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r) :=
  -- (α(n+1), r) ≽ (α(n+1), s)  [reference direction]
  -- (α(n+1), s) ≽ (α n, r)     [spaced n, second component]
  ProductPref.IsWeakOrder.transitive _ _ _ hrefdir (σ.spaced n).2

/-- **Ascending coordinate-cancellation at a standard sequence's grid step.**

Dual of `CoordinateCancelAtStep`: the `r`-carrying comparison
`(α (n+1), r) ≽ (α n, r)` transports to the bare `j`-comparison
`(α (n+1)) ≽ (α n)` (the ascending step). -/
def CoordinateCancelAscAtStep
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j) (n : ℕ) : Prop :=
  P.weakPref
      (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.r)
      (Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r) →
    P.weakPref
      (Function.update σ.base j (σ.α (n + 1)))
      (Function.update σ.base j (σ.α n))

/-- **`spaced` + reference direction + ascending cancellation ⟹ weakly
ascending.**

The ascending analogue of `weaklyDescending_of_referenceDirection_and_cancel`,
but with the transported comparison *derived* from `spaced` (§III.4 reference
direction is the only genuine input besides cancellation).  Produces exactly the
`hasc` hypothesis the ascending IVT crossing consumes. -/
theorem weaklyAscending_of_spaced_referenceDirection_and_cancel
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hrefdir : ∀ n, ReferenceDirectionAtStep P σ n)
    (hcancel : ∀ n, CoordinateCancelAscAtStep P σ n) :
    ∀ n, P.weakPref
      (Function.update σ.base j (σ.α (n + 1)))
      (Function.update σ.base j (σ.α n)) :=
  fun n => hcancel n
    (transportedComparison_of_spaced_and_referenceDirection P σ n (hrefdir n))

/-- **Fully-composed ascending crossing from `spaced` + reference direction.**

The ascending capstone: the IVT crossing for a standard-sequence grid follows
from the topology inputs, the raw Archimedean axiom, the §III.4
reference-direction monotonicity (`hrefdir`) and ascending cancellation
(`hcancel`) — with the transported comparison now **derived from `spaced`** — and
the seed-below condition.  Dual of `archimedean_slice_crossing_of_referenceDirection`,
and tighter: it consumes the standard sequence's own `spaced` field instead of a
separately-postulated transported comparison. -/
theorem archimedean_ascending_slice_crossing_of_referenceDirection
    [∀ i, TopologicalSpace (X i)]
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {j : ι}
    [ConnectedSpace (X j)]
    (σ : ProductPref.StandardSequence P j) (hσ : σ.IsStrict)
    (harchim : ProductPref.Archimedean P j)
    (hrefdir : ∀ n, ReferenceDirectionAtStep P σ n)
    (hcancel : ∀ n, CoordinateCancelAscAtStep P σ n)
    (b : Profile X)
    (hUpper : IsClosed {x : Profile X | P.weakPref x b})
    (hLower : IsClosed {x : Profile X | P.weakPref b x})
    (hseed : ¬ P.weakPref (Function.update σ.base j (σ.α 0)) b) :
    ∃ c : X j, P.indiff (Function.update σ.base j c) b :=
  archimedean_weaklyAscending_slice_crossing_of_seedBelow
    P σ hσ harchim
    (weaklyAscending_of_spaced_referenceDirection_and_cancel P σ hrefdir hcancel)
    b hUpper hLower hseed

/-! ## §8.  Single-coordinate independence and the distinctness residual

The `compensating_reference_value_distinct` axiom of
`RawAxiomDischargersTopology.lean` is, per its docstring, the §III.4
**single-coordinate independence** content: strict preference between two
pivot values persists when a *different* coordinate is perturbed.  This section
names that primitive and shows it forces the distinctness conclusion directly —
reducing that topology axiom to the same single-coordinate independence
primitive that underlies the reference-direction residual. -/

/-- **Single-coordinate independence at a pivot pair.**

The §III.4 fact: if two pivot values `a0, a1` on coordinate `j₀` are
indifferent when a *second* coordinate `k` is set to a common value `r`
(i.e. `(a0 at j₀, r at k) ∼ (a1 at j₀, r at k)`), then they are indifferent at
the base too (`(a0 at j₀) ∼ (a1 at j₀)`).  This is exactly "the `k`-perturbation
does not affect the `j₀`-comparison" — cardinal coordinate independence on the
single pair.

`TradeoffConsistency` does **not** supply this on its own (it transports
indifferences differing in `j₀` alone; here the profiles differ in `k`), which
is why it is a genuine named residual. -/
def SingleCoordinateIndependenceAtPair
    (P : ProductPref X) (base : Profile X) (j₀ k : ι) (a0 a1 : X j₀) (r : X k) : Prop :=
  P.indiff
      (Function.update (Function.update base j₀ a0) k r)
      (Function.update (Function.update base j₀ a1) k r) →
    P.indiff
      (Function.update base j₀ a0)
      (Function.update base j₀ a1)

/-- **Strict distinctness of a compensating value, from single-coordinate
independence.**

If the compensated indifference holds at `(a0, r) ∼ (a1, s)` and, were `s = r`,
single-coordinate independence would force `a0 ∼ a1` at the base — but the strict
pivot pair `(hweak, hnotweak)` rules that out.  Hence `s ≠ r`.

This is the exact content of the topology module's
`compensating_reference_value_distinct` axiom, now **theorem-backed** from the
named single-coordinate independence primitive (the genuine §III.4 residual)
plus the strict pivot pair — no longer an opaque axiom. -/
theorem compensating_value_distinct_of_singleCoordinateIndependence
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) {j₀ k : ι} (a0 a1 : X j₀) (r s : X k)
    (hweak : P.weakPref (Function.update base j₀ a0) (Function.update base j₀ a1))
    (hnotweak : ¬ P.weakPref (Function.update base j₀ a1) (Function.update base j₀ a0))
    (hindep : SingleCoordinateIndependenceAtPair P base j₀ k a0 a1 r)
    (hcompensated :
      P.indiff
        (Function.update (Function.update base j₀ a0) k r)
        (Function.update (Function.update base j₀ a1) k s)) :
    s ≠ r := by
  intro hsr
  subst hsr
  -- Now hcompensated : (a0, r) ∼ (a1, r); independence gives a0 ∼ a1 at base.
  have hbase : P.indiff (Function.update base j₀ a0) (Function.update base j₀ a1) :=
    hindep hcompensated
  -- But the strict pair says ¬ (a1 ≽ a0); indifference gives a1 ≽ a0.  Contradiction.
  exact hnotweak hbase.2

/-- **Single-coordinate WEAK independence at a pivot pair.**

The weak-preference analogue of `SingleCoordinateIndependenceAtPair`: a *weak*
`≽`-comparison between two `j₀`-values carrying a common `k`-value `r` transports
to the bare `j₀`-comparison (cancel the common `k`-value).

This is the genuine §III.4 single-coordinate-**monotonicity** residual.  Unlike
the indifference form (`SingleCoordinateIndependenceAtPair`, supplied by the
topology bundle), the weak/strict direction is **not** a `TradeoffConsistency`
consequence (the hexagon transports indifferences only — see the Phase-29 scope
note).  It is the one primitive driving the `spaced ⟹ weakly-descending` bridge
and hence the obligation-12a injectivity half. -/
def SingleCoordinateWeakIndependenceAtPair
    (P : ProductPref X) (base : Profile X) (j₀ k : ι) (a0 a1 : X j₀) (r : X k) : Prop :=
  P.weakPref
      (Function.update (Function.update base j₀ a0) k r)
      (Function.update (Function.update base j₀ a1) k r) →
    P.weakPref
      (Function.update base j₀ a0)
      (Function.update base j₀ a1)

/-- **`CoordinateCancelAtStep` from weak single-coordinate independence.**

The descending coordinate-cancellation fact at a standard-sequence grid step is
exactly `SingleCoordinateWeakIndependenceAtPair` instantiated at the consecutive
grid values `(α n, α (n+1))` over the sequence's base and reference value `r`.
So the per-step cancellation residual is a direct consequence of the single named
weak-independence primitive. -/
theorem coordinateCancelAtStep_of_singleCoordinateWeakIndependence
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j) (n : ℕ)
    (hindep : SingleCoordinateWeakIndependenceAtPair P σ.base j σ.k (σ.α n) (σ.α (n + 1)) σ.r) :
    CoordinateCancelAtStep P σ n :=
  hindep

/-- **`CoordinateCancelAscAtStep` from weak single-coordinate independence.**

The ascending companion: the ascending cancellation residual at step `n` is
`SingleCoordinateWeakIndependenceAtPair` at the swapped grid pair
`(α (n+1), α n)`. -/
theorem coordinateCancelAscAtStep_of_singleCoordinateWeakIndependence
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j) (n : ℕ)
    (hindep : SingleCoordinateWeakIndependenceAtPair P σ.base j σ.k (σ.α (n + 1)) (σ.α n) σ.r) :
    CoordinateCancelAscAtStep P σ n :=
  hindep

/-! ### §8.1  Coordinate weak separability: the common root of both reach residuals

The two reach residuals isolated above — weak single-coordinate independence
(`SingleCoordinateWeakIndependenceAtPair`, the cancellation) and the uniform
reference direction (`UniformReferenceDirection`, the exchange direction) — are
both consequences of a **single** deeper §III.4 fact: *single-coordinate weak
preference is background-independent*.  Concretely, the comparison
`coordPref i a v w = (update a i v ≽ update a i w)` depends only on `v, w` (and
`i`), not on the off-`i` values of the base `a`.

Naming this one primitive collapses both reach residuals to it: the cancellation
is background-independence of the pivot coordinate `j₀` across a `k`-perturbation,
and the uniform exchange direction is background-independence of `k` across the
`j`-slice, seeded by a single base exchange. -/

/-- **Coordinate weak separability at coordinate `i`.**

Single-coordinate weak preference at `i` is independent of the background: for any
two bases `a, b` and any values `v, w : X i`, the `i`-comparison `v ≽ w` holds
over base `a` iff it holds over base `b`.  This is the §III.4
single-coordinate-independence content in its most basic form (the weak/strict
direction, not a `TradeoffConsistency` consequence — Phase-29 scope note). -/
def CoordinateWeakSeparable (P : ProductPref X) (i : ι) : Prop :=
  ∀ (a b : Profile X) (v w : X i),
    P.coordPref i a v w → P.coordPref i b v w

/-- **Weak single-coordinate independence from coordinate weak separability.**

`SingleCoordinateWeakIndependenceAtPair` is exactly background-independence of the
pivot coordinate `j₀` between the `k`-perturbed base `update base k r` and the
bare base `base`.  So the cancellation residual follows from
`CoordinateWeakSeparable P j₀`. -/
theorem singleCoordinateWeakIndependenceAtPair_of_coordinateWeakSeparable
    (P : ProductPref X) (base : Profile X) {j₀ k : ι} (hjk : j₀ ≠ k)
    (a0 a1 : X j₀) (r : X k)
    (hsep : CoordinateWeakSeparable P j₀) :
    SingleCoordinateWeakIndependenceAtPair P base j₀ k a0 a1 r := by
  intro hcarry
  -- hcarry : weakPref (update (update base j₀ a0) k r) (update (update base j₀ a1) k r)
  -- Rewrite into coordPref j₀ form over the base `update base k r`.
  have hcoord : P.coordPref j₀ (Function.update base k r) a0 a1 := by
    show P.weakPref
      (Function.update (Function.update base k r) j₀ a0)
      (Function.update (Function.update base k r) j₀ a1)
    rw [← Function.update_comm hjk a0 r base, ← Function.update_comm hjk a1 r base]
    exact hcarry
  exact hsep (Function.update base k r) base a0 a1 hcoord

/-- **Uniform reference direction from coordinate weak separability + one base
exchange.**

`UniformReferenceDirection P σ` (the `k`-exchange `r ≽ s` at every `j`-slice) is
background-independence of the auxiliary coordinate `k` across the `j`-slice,
seeded by a single base exchange `coordPref k σ.base r s`.  So the uniform
exchange direction follows from `CoordinateWeakSeparable P σ.k` plus one exchange
fact. -/
theorem uniformReferenceDirection_of_coordinateWeakSeparable
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j)
    (hsep : CoordinateWeakSeparable P σ.k)
    (hbase : P.coordPref σ.k σ.base σ.r σ.s) :
    UniformReferenceDirection P σ := by
  intro v
  -- Goal: weakPref (update (update σ.base j v) σ.k σ.r) (update (update σ.base j v) σ.k σ.s)
  -- This is coordPref σ.k (update σ.base j v) σ.r σ.s; transport from σ.base by separability.
  exact hsep σ.base (Function.update σ.base j v) σ.r σ.s hbase

/-- **Uniform reverse reference direction from coordinate weak separability + one
base exchange.**  Dual of `uniformReferenceDirection_of_coordinateWeakSeparable`,
seeded by the reverse exchange `coordPref k σ.base s r`. -/
theorem uniformReverseReferenceDirection_of_coordinateWeakSeparable
    (P : ProductPref X) {j : ι} (σ : ProductPref.StandardSequence P j)
    (hsep : CoordinateWeakSeparable P σ.k)
    (hbase : P.coordPref σ.k σ.base σ.s σ.r) :
    UniformReverseReferenceDirection P σ := by
  intro v
  exact hsep σ.base (Function.update σ.base j v) σ.s σ.r hbase

/-- **The indifference-form independence also follows from coordinate weak
separability.**

`SingleCoordinateIndependenceAtPair` (the indifference-form §III.4 fact, supplied
by the Phase-27 topology axiom) is *also* a consequence of `CoordinateWeakSeparable`:
indifference is weak preference in both directions, and separability of the pivot
`j₀` transports each direction (cancelling the common `k`-value `r`).

So the single primitive `CoordinateWeakSeparable P j₀` subsumes **both** §III.4
single-coordinate-independence axioms — the weak/strict form (Phase 52) and the
indifference form (Phase 27).  The project's two §III.4 coordinate-independence
primitives are thus one and the same content: weak separability of the
coordinate. -/
theorem singleCoordinateIndependenceAtPair_of_coordinateWeakSeparable
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) {j₀ k : ι} (hjk : j₀ ≠ k)
    (a0 a1 : X j₀) (r : X k)
    (hsep : CoordinateWeakSeparable P j₀) :
    SingleCoordinateIndependenceAtPair P base j₀ k a0 a1 r := by
  intro hcompensated
  -- hcompensated : indiff (a0, r) (a1, r); split into the two weak directions.
  refine ⟨?_, ?_⟩
  · -- weakPref a0 a1 at base, from the forward direction via separability.
    exact singleCoordinateWeakIndependenceAtPair_of_coordinateWeakSeparable
      P base hjk a0 a1 r hsep hcompensated.1
  · -- weakPref a1 a0 at base, from the backward direction via separability.
    exact singleCoordinateWeakIndependenceAtPair_of_coordinateWeakSeparable
      P base hjk a1 a0 r hsep hcompensated.2

/-- **Carry/cancel bridge for single-coordinate preference.**

`coordPref j (update base k c) v w` (the `j`-comparison over a `k`-perturbed base)
equals the `k`-outer carrying form `weakPref (v, c at k) (w, c at k)`, by commuting
the two updates (`j ≠ k`).  The algebraic glue between the `coordPref` form that
`CoordinateWeakSeparable` speaks about and the carrying form that `spaced`
produces. -/
private theorem coordPref_updateK_iff_carry
    (P : ProductPref X) {j k : ι} (hjk : j ≠ k)
    (base : Profile X) (v w : X j) (c : X k) :
    P.coordPref j (Function.update base k c) v w ↔
      P.weakPref
        (Function.update (Function.update base j v) k c)
        (Function.update (Function.update base j w) k c) := by
  unfold ProductPref.coordPref
  rw [← Function.update_comm hjk v c base, ← Function.update_comm hjk w c base]

/-- **Reverse-strict propagation (axiom 12b) from coordinate weak separability.**

The reverse-strict injectivity half — "if the gap `(α (n+1)) vs (α n)` does not
close, neither does `(α (n+2)) vs (α (n+1))`" — is theorem-backed from
`CoordinateWeakSeparable P j` plus the standard sequence's own `spaced` field.

Contrapositive: from `weakPref (α (n+2)) (α (n+1))` (bare), lift to the carrying
form at `k := s` (separability), compose with `spaced (n+1)` and `spaced n` to get
`(α (n+1), r) ≽ (α n, r)`, then cancel `r` (separability) to get
`weakPref (α (n+1)) (α n)` (bare) — exactly the gap whose closure the hypothesis
denies.

So **both** injectivity halves (12a weak-descending, Phase 48/56; 12b
reverse-strict, this result) reduce to the single `CoordinateWeakSeparable`
primitive plus `spaced`. -/
theorem reverseStrict_of_coordinateWeakSeparable
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hsep : CoordinateWeakSeparable P j) :
    ∀ n,
      ¬ P.weakPref (Function.update σ.base j (σ.α (n + 1)))
                   (Function.update σ.base j (σ.α n)) →
      ¬ P.weakPref (Function.update σ.base j (σ.α (n + 2)))
                   (Function.update σ.base j (σ.α (n + 1))) := by
  intro n hgap hbad
  apply hgap
  have hjk : j ≠ σ.k := σ.k_ne_j.symm
  -- Lift hbad (bare) to the carrying form at k := σ.s.
  have hbad_s :
      P.weakPref
        (Function.update (Function.update σ.base j (σ.α (n + 2))) σ.k σ.s)
        (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.s) := by
    have hcoord : P.coordPref j (Function.update σ.base σ.k σ.s) (σ.α (n + 2)) (σ.α (n + 1)) :=
      hsep σ.base (Function.update σ.base σ.k σ.s) (σ.α (n + 2)) (σ.α (n + 1)) hbad
    exact (coordPref_updateK_iff_carry P hjk σ.base (σ.α (n + 2)) (σ.α (n + 1)) σ.s).mp hcoord
  -- Chain: (α(n+1), r) ≽ (α(n+2), s) ≽ (α(n+1), s) ≽ (α n, r).
  have h1 := (σ.spaced (n + 1)).1
  have h2 := (σ.spaced n).2
  have hchain :
      P.weakPref
        (Function.update (Function.update σ.base j (σ.α (n + 1))) σ.k σ.r)
        (Function.update (Function.update σ.base j (σ.α n)) σ.k σ.r) :=
    ProductPref.IsWeakOrder.transitive _ _ _
      (ProductPref.IsWeakOrder.transitive _ _ _ h1 hbad_s) h2
  -- Cancel r: back to the bare gap (α(n+1)) ≽ (α n).
  have hcoord : P.coordPref j (Function.update σ.base σ.k σ.r) (σ.α (n + 1)) (σ.α n) :=
    (coordPref_updateK_iff_carry P hjk σ.base (σ.α (n + 1)) (σ.α n) σ.r).mpr hchain
  exact hsep (Function.update σ.base σ.k σ.r) σ.base (σ.α (n + 1)) (σ.α n) hcoord

/-- **Weakly-descending property from coordinate weak separability + one reverse
exchange (B1 reduction).**

The full descending property `∀ n, weakPref (α n) (α (n+1))` of a standard
sequence `σ` follows from:

* `hsep_j` — coordinate weak separability of the pivot `j` (drives the
  cancellation family);
* `hsep_k` — coordinate weak separability of the auxiliary coordinate `σ.k`
  (drives the reverse-reference-direction family); and
* `hexch` — a **single** base exchange comparison `coordPref σ.k σ.base σ.s σ.r`
  (the reference direction at the base).

So the entire descending family collapses to separability (both coordinates, the
A1 structural input) plus one reference-exchange fact at the base.  The
transported comparison and per-step reference direction are derived from the
sequence's own `spaced` field. -/
theorem weaklyDescending_of_separable_and_exchange
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hsep_j : CoordinateWeakSeparable P j)
    (hsep_k : CoordinateWeakSeparable P σ.k)
    (hexch : P.coordPref σ.k σ.base σ.s σ.r) :
    ∀ n, P.weakPref
      (Function.update σ.base j (σ.α n))
      (Function.update σ.base j (σ.α (n + 1))) := by
  have hrev : ∀ n, ReverseReferenceDirectionAtStep P σ n :=
    reverseReferenceDirectionAtStep_family_of_uniform P σ
      (uniformReverseReferenceDirection_of_coordinateWeakSeparable P σ hsep_k hexch)
  have hcancel : ∀ n, CoordinateCancelAtStep P σ n := by
    intro n
    exact coordinateCancelAtStep_of_singleCoordinateWeakIndependence P σ n
      (singleCoordinateWeakIndependenceAtPair_of_coordinateWeakSeparable
        P σ.base σ.k_ne_j.symm (σ.α n) (σ.α (n + 1)) σ.r hsep_j)
  exact weaklyDescending_of_spaced_reverseReferenceDirection_and_cancel P σ hrev hcancel

/-- **Reference exchange direction from step-0 strictness + separability (B1
seed discharge).**

The single base-exchange fact `coordPref σ.k σ.base σ.s σ.r` consumed by
`weaklyDescending_of_separable_and_exchange` is **not** a free input: in a
descending standard sequence it is pinned by the step-0 orientation.  From

* `σ.IsStrict` (step-0 weak preference `α 0 ≽ α 1`, available from `Essential`),
* the sequence's own reference indifference `σ.spaced 0`
  (`(α0, r) ~ (α1, s)`), and
* coordinate weak separability of both `j` and `σ.k`,

the reference direction `s ≽ r` at the base follows: carry the step-0 weak
preference to the `k := r` context (separability of `j`), giving
`(α0, r) ≽ (α1, r)`; chain with `spaced 0` (`(α1, s) ≽ (α0, r)`) to get
`(α1, s) ≽ (α1, r)`; cancel the pivot value back to the base (separability of
`σ.k`).  Only the **weak** half of step-0 strictness is needed.

This closes the last genuine residual of the §IV.2.6 weak-descending
injectivity half: the reference direction is a consequence of the seed, not an
extra assumption. -/
theorem referenceExchange_of_isStrict_and_separable
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hsep_j : CoordinateWeakSeparable P j)
    (hsep_k : CoordinateWeakSeparable P σ.k)
    (hσ : σ.IsStrict) :
    P.coordPref σ.k σ.base σ.s σ.r := by
  have hjk : j ≠ σ.k := σ.k_ne_j.symm
  -- Carry step-0 weak preference (α0 ≽ α1) to the k := r context.
  have hcarry_r :
      P.weakPref
        (Function.update (Function.update σ.base j (σ.α 0)) σ.k σ.r)
        (Function.update (Function.update σ.base j (σ.α 1)) σ.k σ.r) := by
    have hcoord : P.coordPref j (Function.update σ.base σ.k σ.r) (σ.α 0) (σ.α 1) :=
      hsep_j σ.base (Function.update σ.base σ.k σ.r) (σ.α 0) (σ.α 1) hσ.1
    exact (coordPref_updateK_iff_carry P hjk σ.base (σ.α 0) (σ.α 1) σ.r).mp hcoord
  -- `spaced 0` gives `(α1, s) ≽ (α0, r)`; chain to `(α1, s) ≽ (α1, r)`.
  have hsp := σ.spaced 0
  have hstep :
      P.weakPref
        (Function.update (Function.update σ.base j (σ.α 1)) σ.k σ.s)
        (Function.update (Function.update σ.base j (σ.α 1)) σ.k σ.r) :=
    ProductPref.IsWeakOrder.transitive _ _ _ hsp.2 hcarry_r
  -- Cancel the pivot value back to the base via separability of σ.k.
  exact hsep_k (Function.update σ.base j (σ.α 1)) σ.base σ.s σ.r hstep

/-- **Weakly-descending property from separability + step-0 strictness (axiom 12a
fully discharged).**

Combines `referenceExchange_of_isStrict_and_separable` with
`weaklyDescending_of_separable_and_exchange`: the entire descending family of a
standard sequence follows from coordinate weak separability of both coordinates
plus the step-0 strictness that the seed already carries — with **no** free
reference-direction input.  This is the theorem-backed form of the §IV.2.6
weak-descending injectivity half. -/
theorem weaklyDescending_of_separable_and_isStrict
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hsep_j : CoordinateWeakSeparable P j)
    (hsep_k : CoordinateWeakSeparable P σ.k)
    (hσ : σ.IsStrict) :
    ∀ n, P.weakPref
      (Function.update σ.base j (σ.α n))
      (Function.update σ.base j (σ.α (n + 1))) :=
  weaklyDescending_of_separable_and_exchange P σ hsep_j hsep_k
    (referenceExchange_of_isStrict_and_separable P σ hsep_j hsep_k hσ)

end RawAxiomDischargersIVT
end CertificateChecklist
end WakkerRoadmap

/-! ## Audit

Both results should depend only on the foundational axioms
`[propext, Classical.choice, Quot.sound]` — they are genuine Mathlib-backed
theorems (connectedness + completeness), carrying **no** `_from_raw_axioms`
or analytic-residual axiom. -/

#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.coordinate_slice_IVT
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.coordinate_slice_bracket
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.coordinate_slice_IVT_of_preferenceContinuous

-- Engine B (Archimedean reach) and the composed crossing: all should depend
-- only on the foundational axioms — pure order theory + the IVT engine.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_grid_escapes
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_reach_below
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_reach_above
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_slice_crossing

-- B1 reduction (Phase 72): the descending family from coordinate weak
-- separability (both coordinates) + one base exchange.  Foundational-axiom only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.weaklyDescending_of_separable_and_exchange

-- B1 seed discharge: the reference exchange direction and the full descending
-- family now follow from step-0 strictness + separability alone (no free
-- reference-direction input).  Foundational-axiom only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.referenceExchange_of_isStrict_and_separable
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.weaklyDescending_of_separable_and_isStrict

-- §6 monotone-grid escape: weakly-descending grids escape below automatically,
-- with no escape hypothesis.  Should be foundational-axiom only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.weaklyDescending_grid_le_first
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_weaklyDescending_escape_below
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_weaklyDescending_slice_crossing
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_weaklyDescending_slice_crossing_of_seedAbove

-- §6 dual: weakly-ascending grids escape above automatically (Phase 45).
-- Foundational-axiom only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.weaklyAscending_grid_ge_first
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_weaklyAscending_escape_above

-- §6 ascending crossing duals (Phase 46): one-sided crossing for ascending
-- grids seeded below.  Foundational-axiom only (the IVT engine).
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_weaklyAscending_slice_crossing
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_weaklyAscending_slice_crossing_of_seedBelow

-- §7 reference-direction bridge: the unifying residual.  The bridge theorems
-- should be foundational-axiom only (the residual is the named inputs, not the
-- bridge).
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.descendingStep_of_referenceDirection_and_cancel
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.weaklyDescending_of_referenceDirection_and_cancel
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_slice_crossing_of_referenceDirection

-- §7 ascending duals (Phase 47): the transported comparison is derived from the
-- standard sequence's own `spaced` field + reference direction; the ascending
-- crossing then follows.  Foundational-axiom only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.transportedComparison_of_spaced_and_referenceDirection
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.weaklyAscending_of_spaced_referenceDirection_and_cancel
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_ascending_slice_crossing_of_referenceDirection

-- §7 descending duals (Phase 54): the transported comparison is derived from
-- `spaced` + the reverse reference direction; the descending crossing then
-- consumes `spaced` directly.  Foundational-axiom only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.transportedComparison_of_spaced_and_reverseReferenceDirection
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.weaklyDescending_of_spaced_reverseReferenceDirection_and_cancel
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_descending_slice_crossing_of_reverseReferenceDirection

-- §7 uniform reference direction (Phase 55): the per-step reference-direction
-- families collapse to one uniform slice-fact.  Foundational-axiom only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.referenceDirectionAtStep_family_of_uniform
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.reverseReferenceDirectionAtStep_family_of_uniform

-- §8.1 coordinate weak separability (Phase 56): the single common root of both
-- reach residuals (cancellation + uniform exchange direction).  Foundational
-- axioms only — the unification is theorem-backed.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.singleCoordinateWeakIndependenceAtPair_of_coordinateWeakSeparable
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.uniformReferenceDirection_of_coordinateWeakSeparable
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.uniformReverseReferenceDirection_of_coordinateWeakSeparable

-- §8.1 (Phase 57): coordinate weak separability ALSO subsumes the
-- indifference-form independence (Phase-27 topology axiom content), so one
-- primitive subsumes both §III.4 coordinate-independence axioms.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.singleCoordinateIndependenceAtPair_of_coordinateWeakSeparable

-- §8.1 (Phase 58): the reverse-strict injectivity half (axiom 12b) ALSO follows
-- from coordinate weak separability + `spaced`, so BOTH injectivity halves reduce
-- to the single separability primitive.  Foundational-axiom only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.reverseStrict_of_coordinateWeakSeparable

-- §8 single-coordinate independence ⇒ distinctness: theorem-backs the topology
-- module's `compensating_reference_value_distinct` axiom from the named §III.4
-- independence primitive.  Foundational-axiom only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.compensating_value_distinct_of_singleCoordinateIndependence

-- §8 weak single-coordinate independence ⇒ coordinate cancellation (Phase 51):
-- the per-step cancellation residual (descending and ascending) from the single
-- named weak-independence primitive.  Foundational-axiom only.
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.coordinateCancelAtStep_of_singleCoordinateWeakIndependence
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.coordinateCancelAscAtStep_of_singleCoordinateWeakIndependence
