/-
Copyright (c) 2026 Wakker–Debreu–Koopmans project.
SPDX-License-Identifier: Apache-2.0

# Standard-sequence constructor infrastructure (spec §S0)

This file implements the **standard-sequence constructor package** named in
`RawAxiomDischargersSpec.md` §S0.  It is honest, theorem-backed Mathlib
development (no axioms): each lemma is either fully provable from the raw
axioms (`Essential`, `RestrictedSolvability`) or takes the genuinely
topology-derived `OneStepExtensible` predicate as an explicit input — exactly
as `Core.extend_to_standard_sequence` already does.

The point of §S0 is that obligations 1 and 2 of `RawAxiomDischargers.lean`
must *produce* standard sequences from the raw interface.  The seed, the
solvability-driven seed indifference, the recursive constructor wrapper, and
the injectivity-from-strict-steps lemma are all reusable building blocks for
that work, and they are all genuinely provable.

## What is honest here

* `standardSequence_seed_of_essential` — pure consequence of `Essential P j`
  (spec §S0.1).
* `standardSequence_seedIndiff_of_restrictedSolvability` — a direct
  application of `RestrictedSolvability` to a bracketing hypothesis
  (spec §S0.2, the one-step grid point).
* `standardSequence_exists_of_seed_and_oneStepExtensible` — a thin wrapper
  over `Core.extend_to_standard_sequence` (spec §S0.3).
* `standardSequence_alpha_injective_of_strictStep` — injectivity of the grid
  map from strictly monotone coordinate steps (spec §S0.4).  The "strict
  monotone steps" hypothesis is the documented residual (Wakker III.4
  derives it from tradeoff consistency + the strict seed + Archimedean).

## Build

```powershell
Set-Location "C:\Users\ORM\lean\research"
lake build WakkerDebreuKoopmans.RawAxiomDischargersStandardSequence
```

Like `RawAxiomDischargers.lean` and `RawAxiomDischargersTopology.lean`, this
file is deliberately **not** in the umbrella import.
-/
import WakkerDebreuKoopmans.Core

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace RawAxiomDischargersStandardSequence

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

open WakkerInfra
open Function

/-! ## §A.  Strict-preference order facts

Two small order facts about `ProductPref.strict` that are needed for the
injectivity argument.  Neither is in `Core.lean`. -/

variable {X : ι → Type v}

/-- Strict preference is **irreflexive**: no profile is strictly preferred to
itself. -/
lemma not_strict_self (P : ProductPref X) (x : Profile X) :
    ¬ P.strict x x := by
  rintro ⟨hxx, hnxx⟩
  exact hnxx hxx

/-- Strict preference is **transitive** under a weak order. -/
lemma strict_trans (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {x y z : Profile X} (hxy : P.strict x y) (hyz : P.strict y z) :
    P.strict x z := by
  obtain ⟨hxy_w, hxy_n⟩ := hxy
  obtain ⟨hyz_w, hyz_n⟩ := hyz
  refine ⟨ProductPref.IsWeakOrder.transitive _ _ _ hxy_w hyz_w, ?_⟩
  intro hzx
  -- `z ≽ x` and `x ≽ y` give `z ≽ y`, contradicting `¬ z ≽ y`.
  exact hyz_n (ProductPref.IsWeakOrder.transitive _ _ _ hzx hxy_w)

/-! ## §B.  Standard-sequence seed (spec §S0.1)

`Essential P j` says some pair of values in coordinate `j` is strictly ranked
on a common base profile.  This is exactly the strict seed comparison that
starts a standard sequence in coordinate `j`. -/

/-- **Standard-sequence seed from essentiality (spec §S0.1).**

If coordinate `j` is essential, there is a base profile and two values
`v ≻ⱼ w` (strict coordinate preference at that base).  This is the raw strict
comparison used to seed a standard sequence on coordinate `j`. -/
lemma standardSequence_seed_of_essential (P : ProductPref X) (j : ι)
    (h : ProductPref.Essential P j) :
    ∃ (base : Profile X) (v w : X j),
      P.strict (Function.update base j v) (Function.update base j w) := by
  obtain ⟨a, v, w, hvw, hnot⟩ := h
  exact ⟨a, v, w, hvw, hnot⟩

/-! ## §C.  Solvability-driven seed indifference (spec §S0.2)

`extend_to_standard_sequence` is seeded with an *indifference*

  `(a0 at j, base, r at k) ∼ (a1 at j, base, s at k)`.

Restricted solvability produces such an `a1` once the target profile
`(a0 at j, base, s at k)` is bracketed between two `j`-updates of the base.
This is the one-step grid construction (spec §S0.2). -/

/-- **Seed indifference from restricted solvability (spec §S0.2).**

Fix a base profile, a reference exchange `r ↦ s` in coordinate `k`, and a
value `a0 : X j`.  Write `target := (a0 at j, base, s at k)` for the profile
that already carries the `s`-value in coordinate `k`.  If `target` is
bracketed between two `j`-updates of `base` — i.e. there are values `v w : X j`
with `(v at j, base, s at k) ≽ target ≽ (w at j, base, s at k)` — then
restricted solvability yields a value `a1 : X j` making the canonical seed
indifference hold:

  `(a1 at j, base, s at k) ∼ target = (a0 at j, base, s at k)`.

In particular this gives the seed indifference at `r = s` directly; the
general `r ≠ s` seed is obtained by the same bracketing with `r` in place of
the inner `s` (Wakker IV.2 standard-sequence construction).  The bracketing
hypothesis is the honest residual: Wakker derives it from connectedness +
continuity. -/
lemma standardSequence_seedIndiff_of_restrictedSolvability
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (j k : ι) (base : Profile X) (a0 : X j) (s : X k) (v w : X j)
    (hupper :
      P.weakPref
        (Function.update (Function.update base k s) j v)
        (Function.update (Function.update base k s) j a0))
    (hlower :
      P.weakPref
        (Function.update (Function.update base k s) j a0)
        (Function.update (Function.update base k s) j w)) :
    ∃ a1 : X j,
      P.indiff
        (Function.update (Function.update base k s) j a1)
        (Function.update (Function.update base k s) j a0) := by
  -- Apply restricted solvability with base profile `(base, s at k)` in
  -- coordinate `j`, target `b := (a0 at j, base, s at k)`.
  exact hsolv (Function.update base k s)
    (Function.update (Function.update base k s) j a0) j v w hupper hlower

/-! ## §D.  Recursive constructor wrapper (spec §S0.3)

A thin, honest repackaging of `Core.extend_to_standard_sequence`: from a seed
indifference plus the one-step-extensibility predicate (the topology-derived
input), produce an actual `StandardSequence` record whose grid agrees with the
chosen seed at indices `0` and `1`. -/

/-- **Standard sequence from seed + one-step extensibility (spec §S0.3).**

Given the seed indifference between `(a0 at j, base, r at k)` and
`(a1 at j, base, s at k)` and the `OneStepExtensible` predicate (which Wakker
derives from connectedness/continuity, and which `RawAxiomDischargersTopology`
discharges from the topology bundle), there is a standard sequence in
coordinate `j` whose base is `base` and whose first two grid points are
`a0, a1`. -/
lemma standardSequence_exists_of_seed_and_oneStepExtensible
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (hsolv : ProductPref.RestrictedSolvability P)
    (j k : ι) (hjk : k ≠ j)
    (base : Profile X) (a0 a1 : X j) (r s : X k) (hrs : r ≠ s)
    (h01 :
      P.indiff
        (Function.update (Function.update base j a0) k r)
        (Function.update (Function.update base j a1) k s))
    (hext : ProductPref.OneStepExtensible P j base k r s) :
    ∃ σ : ProductPref.StandardSequence P j,
      σ.base = base ∧ σ.α 0 = a0 ∧ σ.α 1 = a1 :=
  WakkerRoadmap.TradeoffMeasurement.extend_to_standard_sequence
    P hsolv j k hjk base a0 a1 r s hrs h01 hext

/-- **Standard-sequence builder with the reference-exchange fields definitional
(spec §S0.3, record form).**

Returns the `StandardSequence` record **directly** (not via `Classical.choose`),
so that all of its fields reduce definitionally to the intended inputs:
`σ.k ≡ k`, `σ.r ≡ r`, `σ.s ≡ s`, `σ.base ≡ base`, `σ.α 0 ≡ a0`, `σ.α 1 ≡ a1`.

This is the field-transparent companion to
`standardSequence_exists_of_seed_and_oneStepExtensible` (which forgets the
reference-exchange fields behind the `∃`).  Consumers that must talk about
`σ.k`/`σ.r`/`σ.s` for the constructed sequence (e.g. the reverse-exchange
comparison `coordPref σ.k σ.base σ.s σ.r`) use this record form and get the
field facts by `rfl`.  Re-runs the same recursion as
`Core.extend_to_standard_sequence`. -/
noncomputable def standardSequenceBuild_of_seed_and_oneStepExtensible
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (j k : ι) (hjk : k ≠ j)
    (base : Profile X) (a0 a1 : X j) (r s : X k) (hrs : r ≠ s)
    (h01 :
      P.indiff
        (Function.update (Function.update base j a0) k r)
        (Function.update (Function.update base j a1) k s))
    (hext : ProductPref.OneStepExtensible P j base k r s) :
    ProductPref.StandardSequence P j := by
  classical
  refine
    { k       := k
      k_ne_j  := hjk
      r       := r
      s       := s
      r_ne_s  := hrs
      base    := base
      α       := fun n =>
        match n with
        | 0     => a0
        | 1     => a1
        | n+2   =>
          Classical.choose
            (hext (Nat.rec a1 (fun _ prev => Classical.choose (hext prev)) n))
      spaced  := ?_ }
  -- The spacing indifferences (same argument as Core.extend_to_standard_sequence).
  intro n
  match n with
  | 0     => exact h01
  | n'+1  =>
      let γ : ℕ → X j := fun m =>
        Nat.rec a1 (fun _ prev => Classical.choose (hext prev)) m
      have hβ_eq_γ : ∀ m,
          (fun n =>
            match n with
            | 0     => a0
            | 1     => a1
            | n+2   =>
              Classical.choose
                (hext (Nat.rec a1 (fun _ prev => Classical.choose (hext prev)) n)))
            (m+1) = γ m := by
        intro m
        induction m with
        | zero => rfl
        | succ m _ihm => rfl
      have hspec := Classical.choose_spec (hext (γ n'))
      show P.indiff
        (Function.update (Function.update base j
          ((fun n =>
            match n with
            | 0     => a0
            | 1     => a1
            | n+2   =>
              Classical.choose
                (hext (Nat.rec a1 (fun _ prev => Classical.choose (hext prev)) n)))
            (n'+1))) k r)
        (Function.update (Function.update base j
          ((fun n =>
            match n with
            | 0     => a0
            | 1     => a1
            | n+2   =>
              Classical.choose
                (hext (Nat.rec a1 (fun _ prev => Classical.choose (hext prev)) n)))
            (n'+1+1))) k s)
      rw [show (fun n =>
            match n with
            | 0     => a0
            | 1     => a1
            | n+2   =>
              Classical.choose
                (hext (Nat.rec a1 (fun _ prev => Classical.choose (hext prev)) n)))
            (n'+1) = γ n' from hβ_eq_γ n',
          show (fun n =>
            match n with
            | 0     => a0
            | 1     => a1
            | n+2   =>
              Classical.choose
                (hext (Nat.rec a1 (fun _ prev => Classical.choose (hext prev)) n)))
            (n'+1+1) = γ (n'+1) from hβ_eq_γ (n'+1)]
      exact hspec

/-- Field/spec facts for `standardSequenceBuild_of_seed_and_oneStepExtensible`:
the base profile and first two grid points are the intended seed values.  (The
reference-exchange fields `σ.k`, `σ.r`, `σ.s` are *definitionally* `k`, `r`, `s`
and need no lemma.) -/
lemma standardSequenceBuild_spec
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    [ProductPref.TradeoffConsistency P]
    (j k : ι) (hjk : k ≠ j)
    (base : Profile X) (a0 a1 : X j) (r s : X k) (hrs : r ≠ s)
    (h01 :
      P.indiff
        (Function.update (Function.update base j a0) k r)
        (Function.update (Function.update base j a1) k s))
    (hext : ProductPref.OneStepExtensible P j base k r s) :
    (standardSequenceBuild_of_seed_and_oneStepExtensible
        P j k hjk base a0 a1 r s hrs h01 hext).base = base ∧
      (standardSequenceBuild_of_seed_and_oneStepExtensible
        P j k hjk base a0 a1 r s hrs h01 hext).α 0 = a0 ∧
      (standardSequenceBuild_of_seed_and_oneStepExtensible
        P j k hjk base a0 a1 r s hrs h01 hext).α 1 = a1 :=
  ⟨rfl, rfl, rfl⟩

/-! ## §E.  Injectivity of the standard-sequence grid (spec §S0.4)

If the standard-sequence grid is **strictly monotone** in coordinate `j` — each
consecutive step `α n ≻ⱼ α (n+1)` at the base profile — then the grid map is
injective.  This is the order-theoretic core of standard-sequence injectivity:
strict monotonicity + transitivity already forces all grid points distinct, with
no representation needed.

The strict-step hypothesis is the documented residual.  Wakker III.4 obtains it
by propagating the strict seed `α 0 ≻ⱼ α 1` along the sequence using tradeoff
consistency (each spacing step has the same coordinate-`j` magnitude), with the
Archimedean axiom ruling out accumulation.  Here we expose the clean
order-theoretic consequence. -/

/-- The coordinate-`j` updates of a strictly stepping grid are **strictly
antitone**: for `m < n`, `(α m at j, base) ≻ (α n at j, base)`. -/
lemma standardSequence_strictAntitone_of_strictStep
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j : ι) (α : ℕ → X j)
    (hstep : ∀ n,
      P.strict (Function.update base j (α n))
               (Function.update base j (α (n + 1))))
    {m n : ℕ} (hmn : m < n) :
    P.strict (Function.update base j (α m))
             (Function.update base j (α n)) := by
  induction n with
  | zero => exact absurd hmn (Nat.not_lt_zero m)
  | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with hlt | heq
      · exact strict_trans P (ih hlt) (hstep n)
      · subst heq
        exact hstep m

/-- **Injectivity of a strictly stepping standard-sequence grid (spec §S0.4).**

If each consecutive coordinate-`j` step is strict, the grid map `α` is
injective. -/
lemma standardSequence_alpha_injective_of_strictStep
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j : ι) (α : ℕ → X j)
    (hstep : ∀ n,
      P.strict (Function.update base j (α n))
               (Function.update base j (α (n + 1)))) :
    Function.Injective α := by
  intro m n hmn
  by_contra hne
  -- WLOG `m < n` (the symmetric case is identical).
  rcases Nat.lt_or_ge m n with hlt | hge
  · have hstrict :=
      standardSequence_strictAntitone_of_strictStep P base j α hstep hlt
    -- `α m = α n` makes the two profiles equal, contradicting irreflexivity.
    rw [hmn] at hstrict
    exact not_strict_self P _ hstrict
  · have hlt : n < m := lt_of_le_of_ne hge (fun h => hne h.symm)
    have hstrict :=
      standardSequence_strictAntitone_of_strictStep P base j α hstep hlt
    rw [hmn] at hstrict
    exact not_strict_self P _ hstrict

/-- **Grid injectivity packaged on a `StandardSequence` record.**

Specialization of the previous lemma to the `α` field of a standard sequence,
under the same strict-step hypothesis. -/
lemma standardSequence_injective_of_strictStep
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hstep : ∀ n,
      P.strict (Function.update σ.base j (σ.α n))
               (Function.update σ.base j (σ.α (n + 1)))) :
    Function.Injective σ.α :=
  standardSequence_alpha_injective_of_strictStep P σ.base j σ.α hstep

/-! ## §F.  Strict-step propagation (spec §S0.4, Wakker IV.2.6 part a)

The injectivity lemma `standardSequence_alpha_injective_of_strictStep` takes the
*all-steps-strict* hypothesis `hstep`.  Wakker III.4 / IV.2.6 obtains `hstep`
from a single strict seed by **propagating** strictness along the sequence.

The honest decomposition of that propagation has two ingredients:

* **(a) step-0 strictness** — for the constructed pivot sequence this is exactly
  `σ.IsStrict`, which is available from `Essential` (the strict seed pair).
* **(b) a one-step strict lift** — "if step `n` is strict, so is step `n+1`".

Ingredient (b) is the genuinely deep residual.  As documented in
`M2Frontier.lean` (honest analysis, 2026-05-17), the hexagon condition
`TradeoffConsistency` does **not** supply even the *weak* per-step lift on its
own: the spaced indifferences of a standard sequence differ at *both* the pivot
coordinate `j` and the reference coordinate `k = σ.k`, so they fail the
hexagon's `agreeOff {j}` requirement; the genuine residual is a
single-coordinate-at-`k` reference direction that `TradeoffConsistency` alone
cannot provide.

What *is* fully theorem-backed — and is what we prove here — is the **inductive
propagation step**: step-0 strictness together with the one-step strict lift
yields all-steps strictness (and hence grid injectivity).  This converts the
opaque all-steps `hstep` into a single one-step lift residual plus an available
seed fact, exactly mirroring the `HexagonStepLiftCertificate` decomposition in
`M2Frontier.lean` but at the *strict* level needed for injectivity. -/

/-- **All-steps strictness from first-step strictness + one-step strict lift.**

If step `0` of the coordinate-`j` grid is strict and each strict step propagates
to the next (`hlift`), then *every* consecutive step is strict.  Pure induction
on `n`; no axioms beyond the weak order carried by the ambient `P`. -/
lemma standardSequence_allStepsStrict_of_firstStrict_and_oneStepLift
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j : ι) (α : ℕ → X j)
    (h0 : P.strict (Function.update base j (α 0))
                   (Function.update base j (α 1)))
    (hlift : ∀ n,
      P.strict (Function.update base j (α n))
               (Function.update base j (α (n + 1))) →
      P.strict (Function.update base j (α (n + 1)))
               (Function.update base j (α (n + 2)))) :
    ∀ n,
      P.strict (Function.update base j (α n))
               (Function.update base j (α (n + 1))) := by
  intro n
  induction n with
  | zero => exact h0
  | succ m ih => exact hlift m ih

/-- **Grid injectivity from first-step strictness + one-step strict lift.**

Combines the inductive propagation with
`standardSequence_alpha_injective_of_strictStep`: a strict seed plus the
one-step strict lift residual forces the grid map to be injective. -/
lemma standardSequence_alpha_injective_of_firstStrict_and_oneStepLift
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j : ι) (α : ℕ → X j)
    (h0 : P.strict (Function.update base j (α 0))
                   (Function.update base j (α 1)))
    (hlift : ∀ n,
      P.strict (Function.update base j (α n))
               (Function.update base j (α (n + 1))) →
      P.strict (Function.update base j (α (n + 1)))
               (Function.update base j (α (n + 2)))) :
    Function.Injective α :=
  standardSequence_alpha_injective_of_strictStep P base j α
    (standardSequence_allStepsStrict_of_firstStrict_and_oneStepLift
      P base j α h0 hlift)

/-- **`StandardSequence`-record propagation: all steps strict from `σ.IsStrict`
+ one-step strict lift.**

The first-step hypothesis is exactly the existing `σ.IsStrict` predicate
(`Core.StandardSequence.IsStrict`), so this version consumes the strict seed
that `Essential` already provides. -/
lemma standardSequence_allStepsStrict_of_isStrict_and_oneStepLift
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict)
    (hlift : ∀ n,
      P.strict (Function.update σ.base j (σ.α n))
               (Function.update σ.base j (σ.α (n + 1))) →
      P.strict (Function.update σ.base j (σ.α (n + 1)))
               (Function.update σ.base j (σ.α (n + 2)))) :
    ∀ n,
      P.strict (Function.update σ.base j (σ.α n))
               (Function.update σ.base j (σ.α (n + 1))) :=
  standardSequence_allStepsStrict_of_firstStrict_and_oneStepLift
    P σ.base j σ.α hσ hlift

/-- **`StandardSequence`-record injectivity from `σ.IsStrict` + one-step strict
lift.**

This is the propagation form directly consumable by the axiom-12 thinning:
grid injectivity follows from the strict seed (`σ.IsStrict`, available from
`Essential`) plus the single one-step strict lift residual. -/
lemma standardSequence_injective_of_isStrict_and_oneStepLift
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict)
    (hlift : ∀ n,
      P.strict (Function.update σ.base j (σ.α n))
               (Function.update σ.base j (σ.α (n + 1))) →
      P.strict (Function.update σ.base j (σ.α (n + 1)))
               (Function.update σ.base j (σ.α (n + 2)))) :
    Function.Injective σ.α :=
  standardSequence_injective_of_strictStep P σ
    (standardSequence_allStepsStrict_of_isStrict_and_oneStepLift P σ hσ hlift)

/-! ### §G Factoring the one-step strict lift into weak descending + reverse-strict

The one-step **strict** lift `hlift` consumed by the §F propagation lemmas is the
honest residual of axiom 12, but it is not itself irreducible: it splits cleanly
into two strictly smaller pieces, exposing exactly where the genuinely deep
content lives.

Recall `P.strict x y = P.weakPref x y ∧ ¬ P.weakPref y x`.  So a one-step strict
lift `strict (α n) (α (n+1)) → strict (α (n+1)) (α (n+2))` needs:

* the **forward weak descending** fact `weakPref (α (n+1)) (α (n+2))` — this is
  the per-step content of `M2Frontier.HexagonStepLiftCertificate`, which that
  file documents is derivable from the genuinely deep
  `StandardSequenceReferenceDirection` (single-coordinate-at-`k` monotonicity);
  and
* the **reverse-strict propagation** `¬ weakPref (α (n+1)) (α n) →
  ¬ weakPref (α (n+2)) (α (n+1))` — propagation of the "strict gap does not
  close" half.

Splitting `hlift` this way shows the forward half is *exactly* M2Frontier's
already-named weak lift, leaving the reverse-strict propagation as the only new
named seam. -/

/-- **One-step strict lift from weak descending + reverse-strict propagation.**

Genuine, sorry-free.  The forward conjunct of the lifted strict step is supplied
by the weak descending fact `hweak` at index `n+1`; the reverse conjunct (the
`¬ weakPref` half) is propagated by `hrev` from the strict hypothesis.  No axioms
beyond the ambient weak order. -/
lemma oneStepStrictLift_of_weakDescending_and_reverseStrict
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j : ι) (α : ℕ → X j)
    (hweak : ∀ n,
      P.weakPref (Function.update base j (α n))
                 (Function.update base j (α (n + 1))))
    (hrev : ∀ n,
      ¬ P.weakPref (Function.update base j (α (n + 1)))
                   (Function.update base j (α n)) →
      ¬ P.weakPref (Function.update base j (α (n + 2)))
                   (Function.update base j (α (n + 1)))) :
    ∀ n,
      P.strict (Function.update base j (α n))
               (Function.update base j (α (n + 1))) →
      P.strict (Function.update base j (α (n + 1)))
               (Function.update base j (α (n + 2))) := by
  intro n hstrict
  exact ⟨hweak (n + 1), hrev n hstrict.2⟩

/-- **All-steps strictness from a strict seed + weak descending + reverse-strict.**

Combines §G's lift factorization with the §F induction: a strict step-0, the
weak descending lift (M2Frontier's `HexagonStepLiftCertificate` content), and the
reverse-strict propagation together force every consecutive step to be strict. -/
lemma standardSequence_allStepsStrict_of_firstStrict_weakDescending_reverseStrict
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j : ι) (α : ℕ → X j)
    (h0 : P.strict (Function.update base j (α 0))
                   (Function.update base j (α 1)))
    (hweak : ∀ n,
      P.weakPref (Function.update base j (α n))
                 (Function.update base j (α (n + 1))))
    (hrev : ∀ n,
      ¬ P.weakPref (Function.update base j (α (n + 1)))
                   (Function.update base j (α n)) →
      ¬ P.weakPref (Function.update base j (α (n + 2)))
                   (Function.update base j (α (n + 1)))) :
    ∀ n,
      P.strict (Function.update base j (α n))
               (Function.update base j (α (n + 1))) :=
  standardSequence_allStepsStrict_of_firstStrict_and_oneStepLift
    P base j α h0
    (oneStepStrictLift_of_weakDescending_and_reverseStrict P base j α hweak hrev)

/-- **`StandardSequence`-record grid injectivity from `σ.IsStrict` + weak
descending + reverse-strict propagation.**

The fully-factored axiom-12 thinning: grid injectivity follows from the strict
seed (`σ.IsStrict`, available from `Essential`), the weak descending lift (the
documented `M2Frontier` reference-direction residual), and the reverse-strict
propagation residual — with no remaining opaque all-steps assumption. -/
lemma standardSequence_injective_of_isStrict_weakDescending_reverseStrict
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (hσ : σ.IsStrict)
    (hweak : ∀ n,
      P.weakPref (Function.update σ.base j (σ.α n))
                 (Function.update σ.base j (σ.α (n + 1))))
    (hrev : ∀ n,
      ¬ P.weakPref (Function.update σ.base j (σ.α (n + 1)))
                   (Function.update σ.base j (σ.α n)) →
      ¬ P.weakPref (Function.update σ.base j (σ.α (n + 2)))
                   (Function.update σ.base j (σ.α (n + 1)))) :
    Function.Injective σ.α :=
  standardSequence_injective_of_isStrict_and_oneStepLift P σ hσ
    (oneStepStrictLift_of_weakDescending_and_reverseStrict P σ.base j σ.α hweak hrev)

end RawAxiomDischargersStandardSequence
end CertificateChecklist
end WakkerRoadmap
