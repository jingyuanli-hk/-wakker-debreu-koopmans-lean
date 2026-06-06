/-
Copyright (c) 2026 Wakker–Debreu–Koopmans project.
SPDX-License-Identifier: Apache-2.0

# Hexagon-transport foundations for engine C (Wakker §IV.5 / §IV.6)

The remaining genuine frontier of the raw-axiom dischargers, after engines A
(generic-coordinate IVT, `RawAxiomDischargersIVT.lean` §1–§6) and B (Archimedean
reach, §4–§6) and the unified §III.4 single-coordinate residual (§7–§8), is
**engine C**: the affine-renormalization / Thomsen-transport content of Wakker
§IV.5 (Step-4 order calibration, obligation 14) and §IV.6 (two-pivot transport,
obligation 16).

Engine C's deep content (constructing order-calibrated utilities) is genuine
multi-week Wakker theory with no Mathlib shortcut.  This file builds the
**theorem-backed foundations** that engine C's eventual proof will reuse —
exactly the role `RawAxiomDischargersIVT.lean` plays for engines A/B.

The foundational object is the `TradeoffConsistency` (hexagon) axiom in its
working form.  Its most basic consequence — proved here directly — is the
**base-independence of single-coordinate indifference**: a `j`-coordinate
indifference at one base profile holds at any base agreeing off `{j}`.  This is
the "cardinal coordinate independence" core that every engine-C calibration
argument rests on.

All results here are theorem-backed from `TradeoffConsistency` alone (no new
axioms): they are the reusable engine-C primitives, not the deep §IV.5/§IV.6
construction itself.

This file is deliberately **not** in the umbrella import.
-/
import WakkerDebreuKoopmans.Core
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace WakkerRoadmap
namespace CertificateChecklist
namespace RawAxiomDischargersHexagon

universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

open WakkerInfra
open Function

variable {X : ι → Type v}

/-! ## §1.  Base-independence of single-coordinate indifference

The `TradeoffConsistency` hexagon axiom, instantiated with all three premise
indifferences equal to the *same* `j`-coordinate indifference, yields that the
indifference transports to any base agreeing off `{j}`.  This is the cardinal
coordinate independence core. -/

/-- **Single-coordinate indifference transports across bases (hexagon core).**

If two profiles `a, b` differing only in coordinate `j` are indifferent, then
*any* two profiles `g, h` differing only in `j`, with the *same* `j`-values
(`g j = a j`, `h j = b j`), are also indifferent.

In other words: a single-coordinate `j`-indifference depends only on the two
`j`-values, not on the values at the other coordinates.  This is exactly the
`TradeoffConsistency` hexagon applied with `c = e = a`, `d = f = b`. -/
theorem singleCoordIndiff_baseIndependent
    (P : ProductPref X) [ProductPref.TradeoffConsistency P]
    {j : ι} {a b g h : Profile X}
    (hab_off : Profile.agreeOff {j} a b)
    (hgh_off : Profile.agreeOff {j} g h)
    (hab : P.indiff a b)
    (hga : g j = a j) (hhb : h j = b j) :
    P.indiff g h :=
  ProductPref.TradeoffConsistency.consistent
    j a b a b a b g h
    hab_off hab_off hab_off hgh_off
    hab hab hab
    rfl rfl rfl rfl
    hga.symm hhb.symm

/-- **`update`-form of base-independence.**

The same fact stated for `Function.update`: if `(v at j) ∼ (w at j)` over base
`base₁`, then `(v at j) ∼ (w at j)` over any other base `base₂`.  This is the
form engine-C arguments consume directly. -/
theorem updateIndiff_baseIndependent
    (P : ProductPref X) [ProductPref.TradeoffConsistency P]
    {j : ι} (base₁ base₂ : Profile X) (v w : X j)
    (hind : P.indiff (Function.update base₁ j v) (Function.update base₁ j w)) :
    P.indiff (Function.update base₂ j v) (Function.update base₂ j w) := by
  refine singleCoordIndiff_baseIndependent P (j := j)
    (a := Function.update base₁ j v) (b := Function.update base₁ j w)
    (g := Function.update base₂ j v) (h := Function.update base₂ j w)
    ?_ ?_ hind ?_ ?_
  · -- agreeOff {j} (update base₁ j v) (update base₁ j w)
    intro i hi
    have hij : i ≠ j := fun e => hi (by simp [e])
    rw [Function.update_of_ne hij, Function.update_of_ne hij]
  · intro i hi
    have hij : i ≠ j := fun e => hi (by simp [e])
    rw [Function.update_of_ne hij, Function.update_of_ne hij]
  · simp
  · simp

/-! ## §2.  Symmetry and the well-defined `j`-value indifference relation

Base-independence makes "the `j`-values `v, w` are indifferent" a property of the
*pair of values* alone, independent of any base.  This packages that as a clean
relation on `X j`, with the symmetry and reflexivity facts engine-C calibration
arguments use. -/

/-- **Base-free `j`-coordinate indifference relation.**

`v` and `w` are `j`-indifferent if updating *some* (equivalently, by
`updateIndiff_baseIndependent`, any) base at `j` to `v` versus `w` gives
indifferent profiles.  Phrased existentially so it is base-free by construction;
`jIndiff_iff_update` below shows it equals the all-bases form. -/
def JIndiff (P : ProductPref X) (j : ι) (v w : X j) : Prop :=
  ∃ base : Profile X,
    P.indiff (Function.update base j v) (Function.update base j w)

/-- **`JIndiff` holds at a given base iff at any base.**

The existential `JIndiff` is equivalent to the `update`-form at any chosen base,
by base-independence.  This is the bridge between the base-free relation and the
concrete profile statements engine-C consumes. -/
theorem jIndiff_iff_update
    (P : ProductPref X) [ProductPref.TradeoffConsistency P]
    {j : ι} (base : Profile X) (v w : X j) :
    JIndiff P j v w ↔
      P.indiff (Function.update base j v) (Function.update base j w) := by
  constructor
  · rintro ⟨base₁, h⟩
    exact updateIndiff_baseIndependent P base₁ base v w h
  · intro h
    exact ⟨base, h⟩

/-- **`JIndiff` is symmetric** (from symmetry of `indiff`). -/
theorem jIndiff_symm
    (P : ProductPref X) {j : ι} {v w : X j}
    (h : JIndiff P j v w) :
    JIndiff P j w v := by
  obtain ⟨base, hb⟩ := h
  exact ⟨base, hb.2, hb.1⟩

/-- **`JIndiff` is reflexive** (from completeness of the weak order). -/
theorem jIndiff_refl
    (P : ProductPref X) [ProductPref.IsWeakOrder P] [Nonempty (Profile X)]
    (j : ι) (v : X j) :
    JIndiff P j v v := by
  obtain ⟨base⟩ := (inferInstance : Nonempty (Profile X))
  refine ⟨base, ?_, ?_⟩ <;>
    · rcases ProductPref.IsWeakOrder.complete (P := P)
        (Function.update base j v) (Function.update base j v) with h | h <;> exact h

/-- **`JIndiff` is transitive** (from base-independence + transitivity of the
weak order).

Evaluating all three relations at a *common* base (via base-independence), the
two `update`-form indifferences chain through the weak order's transitivity.
This makes `JIndiff` an equivalence relation on each coordinate's values — the
quotient structure engine-C calibration assigns real numbers to. -/
theorem jIndiff_trans
    (P : ProductPref X) [ProductPref.IsWeakOrder P] [ProductPref.TradeoffConsistency P]
    {j : ι} {u v w : X j}
    (huv : JIndiff P j u v) (hvw : JIndiff P j v w) :
    JIndiff P j u w := by
  obtain ⟨base, hb⟩ := huv
  -- Transport both relations to the common base `base`.
  have huv' : P.indiff (Function.update base j u) (Function.update base j v) := hb
  have hvw' : P.indiff (Function.update base j v) (Function.update base j w) :=
    (jIndiff_iff_update P base v w).mp hvw
  exact ⟨base,
    ProductPref.IsWeakOrder.transitive _ _ _ huv'.1 hvw'.1,
    ProductPref.IsWeakOrder.transitive _ _ _ hvw'.2 huv'.2⟩

/-! ## §3.  Scope note: weak/strict preference is NOT hexagon-transportable

`JIndiff` (single-coordinate **indifference**) is base-independent and an
equivalence relation, proved above directly from `TradeoffConsistency`.  The
analogous claim for single-coordinate **weak/strict preference** —
"`(v at j) ≽ (w at j)` at one base implies it at any base" — is **not** a
consequence of `TradeoffConsistency`: the hexagon axiom transports indifferences
only.  That weak/strict base-independence is precisely the §III.4
**single-coordinate independence / monotonicity** residual already named in
`RawAxiomDischargersIVT.lean` §8
(`SingleCoordinateIndependenceAtPair`) and adopted as the topology-module axiom
`singleCoordinateIndependence_of_wakkerCoordinateTopology` (Phase 27).  It is
deliberately **not** re-derived here, to keep the audit honest: the indifference
core (this file) is theorem-backed, while the strict/monotone direction remains
the genuine §III.4 residual. -/

/-! ## §4.  The `JIndiff` setoid and utility descent to the quotient

The equivalence relation `JIndiff P j` packages as a `Setoid` on `X j` (under
`Nonempty (Profile X)` for reflexivity).  Wakker §IV.5 calibration assigns a real
number to each class; the structural prerequisite is that any *representing*
coordinate utility is **constant on classes** (descends to the quotient).  This
section proves that descent fact, completing the well-definedness substrate. -/

/-- **The single-coordinate indifference setoid on `X j`.**

`JIndiff P j` as a bundled `Setoid`, using `jIndiff_refl/symm/trans`.  This is the
quotient structure whose classes engine-C calibration assigns reals to. -/
def jIndiffSetoid
    (P : ProductPref X) [ProductPref.IsWeakOrder P] [ProductPref.TradeoffConsistency P]
    [Nonempty (Profile X)] (j : ι) :
    Setoid (X j) where
  r := JIndiff P j
  iseqv :=
    { refl := fun v => jIndiff_refl P j v
      symm := fun h => jIndiff_symm P h
      trans := fun h₁ h₂ => jIndiff_trans P h₁ h₂ }

/-- **A representing coordinate utility is `JIndiff`-invariant.**

If a real-valued utility pair `(Vj, Vk)` represents the `{j, k}`-slice (the
`PairwiseSliceRepresentationCertificate` shape: `weakPref ↔ additive-score`),
then `Vj` is constant on `JIndiff`-classes: `JIndiff P j v w → Vj v = Vj w`.

Proof: pick a base; the `JIndiff` indifference at `(base, k ↦ Vk-anchor)` gives,
via the representation biconditional in both directions, `Vj v ≤ Vj w` and
`Vj w ≤ Vj v`.  This is the descent fact that lets the utility factor through the
quotient — the structural substrate of §IV.5 calibration. -/
theorem utility_jIndiff_invariant
    (P : ProductPref X) [ProductPref.IsWeakOrder P] [ProductPref.TradeoffConsistency P]
    {j k : ι} (hjk : j ≠ k) (Vj : X j → ℝ) (Vk : X k → ℝ)
    (base : Profile X)
    (hrepr : ∀ x y : Profile X, Profile.agreeOff ({j, k} : Set ι) x y →
      (P.weakPref x y ↔ Vj (y j) + Vk (y k) ≤ Vj (x j) + Vk (x k)))
    {v w : X j} (h : JIndiff P j v w) :
    Vj v = Vj w := by
  classical
  -- Transport the JIndiff to the chosen base.
  have hb : P.indiff (Function.update base j v) (Function.update base j w) :=
    (jIndiff_iff_update P base v w).mp h
  -- The two profiles agree off {j} ⊆ {j, k}.
  have hagree : Profile.agreeOff ({j, k} : Set ι)
      (Function.update base j v) (Function.update base j w) := by
    intro i hi
    have hij : i ≠ j := fun e => hi (by simp [e])
    rw [Function.update_of_ne hij, Function.update_of_ne hij]
  -- Evaluate the representation at these profiles.  Their k-values are equal
  -- (both `base k`), so the additive-score comparison reduces to Vj.
  have hxj : (Function.update base j v) j = v := by simp
  have hyj : (Function.update base j w) j = w := by simp
  have hxk : (Function.update base j v) k = base k := by
    rw [Function.update_of_ne (Ne.symm hjk)]
  have hyk : (Function.update base j w) k = base k := by
    rw [Function.update_of_ne (Ne.symm hjk)]
  have hfwd := (hrepr (Function.update base j v) (Function.update base j w) hagree).mp hb.1
  have hbwd := (hrepr (Function.update base j w) (Function.update base j v)
    (Profile.agreeOff_symm hagree)).mp hb.2
  -- hfwd : Vj w + Vk (base k) ≤ Vj v + Vk (base k);  hbwd : Vj v + ... ≤ Vj w + ...
  rw [hxj, hyj, hxk, hyk] at hfwd hbwd
  linarith

/-! ## §5.  Converse descent and the `JIndiff ⟺ equal-utility` characterization

The converse of `utility_jIndiff_invariant`: equal representing-utility values
force `JIndiff`.  Together these characterize the indifference classes exactly as
the level sets of a representing utility — the embedding of the quotient
`X j / JIndiff` into ℝ that §IV.5 calibration realizes. -/

/-- **Converse descent: equal representing-utility values imply `JIndiff`.**

If `(Vj, Vk)` represents the `{j, k}`-slice and `Vj v = Vj w`, then
`JIndiff P j v w`: the equal `Vj`-values (and equal `Vk`-values, both at the
common base `k`) make the additive scores equal, so the representation
biconditional gives weak preference in both directions, i.e. indifference. -/
theorem jIndiff_of_utility_eq
    (P : ProductPref X) [ProductPref.IsWeakOrder P] [ProductPref.TradeoffConsistency P]
    {j k : ι} (hjk : j ≠ k) (Vj : X j → ℝ) (Vk : X k → ℝ)
    (base : Profile X)
    (hrepr : ∀ x y : Profile X, Profile.agreeOff ({j, k} : Set ι) x y →
      (P.weakPref x y ↔ Vj (y j) + Vk (y k) ≤ Vj (x j) + Vk (x k)))
    {v w : X j} (hVeq : Vj v = Vj w) :
    JIndiff P j v w := by
  have hagree : Profile.agreeOff ({j, k} : Set ι)
      (Function.update base j v) (Function.update base j w) := by
    intro i hi
    have hij : i ≠ j := fun e => hi (by simp [e])
    rw [Function.update_of_ne hij, Function.update_of_ne hij]
  have hxj : (Function.update base j v) j = v := by simp
  have hyj : (Function.update base j w) j = w := by simp
  have hxk : (Function.update base j v) k = base k := by
    rw [Function.update_of_ne (Ne.symm hjk)]
  have hyk : (Function.update base j w) k = base k := by
    rw [Function.update_of_ne (Ne.symm hjk)]
  refine ⟨base, ?_, ?_⟩
  · -- weakPref (update v) (update w): scores equal, so the biconditional applies.
    rw [hrepr (Function.update base j v) (Function.update base j w) hagree]
    rw [hxj, hyj, hxk, hyk, hVeq]
  · rw [hrepr (Function.update base j w) (Function.update base j v)
        (Profile.agreeOff_symm hagree)]
    rw [hxj, hyj, hxk, hyk, hVeq]

/-- **`JIndiff ⟺ equal representing-utility value` (full characterization).**

Combining `utility_jIndiff_invariant` (Phase 30) with the converse above: under a
slice-representing utility pair, two coordinate values are `JIndiff` **iff** they
receive the same `Vj`-value.  So the indifference classes are exactly the level
sets of `Vj` — the quotient `X j / JIndiff` embeds into ℝ via `Vj`.  This is the
order-theoretic shape of Wakker §IV.5 calibration's target. -/
theorem jIndiff_iff_utility_eq
    (P : ProductPref X) [ProductPref.IsWeakOrder P] [ProductPref.TradeoffConsistency P]
    {j k : ι} (hjk : j ≠ k) (Vj : X j → ℝ) (Vk : X k → ℝ)
    (base : Profile X)
    (hrepr : ∀ x y : Profile X, Profile.agreeOff ({j, k} : Set ι) x y →
      (P.weakPref x y ↔ Vj (y j) + Vk (y k) ≤ Vj (x j) + Vk (x k)))
    (v w : X j) :
    JIndiff P j v w ↔ Vj v = Vj w :=
  ⟨fun h => utility_jIndiff_invariant P hjk Vj Vk base hrepr h,
   fun h => jIndiff_of_utility_eq P hjk Vj Vk base hrepr h⟩

/-! ## §6.  Grid diagonal calibration: equal-index-sum indifference from one
diagonal-step primitive

The §IV.5 calibration target (Phase 31) is the utility whose level sets are the
`JIndiff`-classes.  The structural heart of building it on the
standard-sequence grid is the **equal-index-sum indifference**: two grid
profiles `g n m` and `g n' m'` are indifferent whenever `n + m = n' + m'`.

This section proves that the *entire* equal-sum indifference reduces — by pure
order theory (transitivity of `indiff` + induction) — to a **single diagonal-step
primitive**: `g (n+1) m ∼ g n (m+1)` (trading one `j`-step for one `k`-step
preserves indifference).  The diagonal step is the genuine §IV.5 residual that
`TradeoffConsistency` supplies on the actual grid; the reduction below is the
fully theorem-backed combinatorial core.

We work abstractly over a grid `g : ℕ → ℕ → Profile X` so the result is reusable
for any concrete standard-sequence rectangle. -/

/-- Indifference is reflexive (from weak-order completeness). -/
private theorem indiff_refl
    (P : ProductPref X) [ProductPref.IsWeakOrder P] (x : Profile X) :
    P.indiff x x := by
  refine ⟨?_, ?_⟩ <;>
    · rcases ProductPref.IsWeakOrder.complete (P := P) x x with h | h <;> exact h

/-- Indifference is transitive (from weak-order transitivity). -/
private theorem indiff_trans
    (P : ProductPref X) [ProductPref.IsWeakOrder P] {x y z : Profile X}
    (hxy : P.indiff x y) (hyz : P.indiff y z) : P.indiff x z :=
  ⟨ProductPref.IsWeakOrder.transitive _ _ _ hxy.1 hyz.1,
   ProductPref.IsWeakOrder.transitive _ _ _ hyz.2 hxy.2⟩

/-- **Diagonal collapse to the axis.**

From the diagonal-step primitive `g (n+1) m ∼ g n (m+1)`, every grid point
`g n m` is indifferent to the axis point `g (n+m) 0`.  Induction on `m`: each
decrement of `m` trades a `k`-step for a `j`-step via the (symmetric) diagonal
step, then applies the inductive hypothesis. -/
theorem grid_indiff_axis_of_diagonalStep
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (g : ℕ → ℕ → Profile X)
    (hdiag : ∀ n m, P.indiff (g (n + 1) m) (g n (m + 1))) :
    ∀ n m, P.indiff (g n m) (g (n + m) 0) := by
  intro n m
  induction m generalizing n with
  | zero => simpa using indiff_refl P (g n 0)
  | succ m ih =>
      -- g n (m+1) ∼ g (n+1) m  (symmetric diagonal step) ∼ g (n+1+m) 0  (IH)
      have hstep : P.indiff (g n (m + 1)) (g (n + 1) m) :=
        ⟨(hdiag n m).2, (hdiag n m).1⟩
      have hih : P.indiff (g (n + 1) m) (g (n + 1 + m) 0) := ih (n + 1)
      have : P.indiff (g n (m + 1)) (g (n + 1 + m) 0) := indiff_trans P hstep hih
      -- n + 1 + m = n + (m + 1)
      have he : n + 1 + m = n + (m + 1) := by omega
      rwa [he] at this

/-- **Equal-index-sum grid indifference from the diagonal-step primitive.**

The §IV.5 calibration core: any two grid points with equal index sum are
indifferent.  Both collapse to the same axis point `g (n+m) 0` via
`grid_indiff_axis_of_diagonalStep`; transitivity and symmetry of `indiff` close
the gap.  This is the entire equal-sum indifference, reduced to the single
diagonal-step residual. -/
theorem grid_indiff_of_eqSum_of_diagonalStep
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (g : ℕ → ℕ → Profile X)
    (hdiag : ∀ n m, P.indiff (g (n + 1) m) (g n (m + 1)))
    {n m n' m' : ℕ} (hsum : n + m = n' + m') :
    P.indiff (g n m) (g n' m') := by
  have h1 : P.indiff (g n m) (g (n + m) 0) :=
    grid_indiff_axis_of_diagonalStep P g hdiag n m
  have h2 : P.indiff (g n' m') (g (n' + m') 0) :=
    grid_indiff_axis_of_diagonalStep P g hdiag n' m'
  -- rewrite the axis index of h2 to match h1 via hsum
  rw [← hsum] at h2
  -- h1 : g n m ∼ g (n+m) 0 ; h2 : g n' m' ∼ g (n+m) 0
  exact indiff_trans P h1 ⟨h2.2, h2.1⟩

/-! ## §7.  Numeric score ⇒ grid indifference, the calibration bridge

The final foundational piece linking §6 (combinatorial equal-sum indifference)
to the Phase-31 utility characterization.  If a real-valued grid score `F n m`
satisfies `F n m = (n : ℝ) + m` (the grid-normalized additive shape) and the
diagonal-step primitive holds, then **equal score forces indifference** on the
grid: `F n m = F n' m' → g n m ∼ g n' m'`.

This is exactly the converse-descent shape (Phase 31) realized on the concrete
standard-sequence rectangle: the grid utility's level sets are the indifference
classes, modulo the single diagonal-step residual. -/

/-- **Equal grid-normalized score ⇒ grid indifference (diagonal-step residual).**

If the grid score is the additive index sum `F n m = n + m` and the
diagonal-step primitive holds, then equal scores `F n m = F n' m'` force the grid
profiles indifferent.  Combines the numeric equality `n + m = n' + m'` (from the
score equation, cast back to ℕ) with `grid_indiff_of_eqSum_of_diagonalStep`. -/
theorem grid_indiff_of_score_eq_of_diagonalStep
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (g : ℕ → ℕ → Profile X) (F : ℕ → ℕ → ℝ)
    (hF : ∀ n m, F n m = (n : ℝ) + (m : ℝ))
    (hdiag : ∀ n m, P.indiff (g (n + 1) m) (g n (m + 1)))
    {n m n' m' : ℕ} (hscore : F n m = F n' m') :
    P.indiff (g n m) (g n' m') := by
  have hsum : n + m = n' + m' := by
    have : (n : ℝ) + (m : ℝ) = (n' : ℝ) + (m' : ℝ) := by
      rw [← hF n m, ← hF n' m']; exact hscore
    have hcast : ((n + m : ℕ) : ℝ) = ((n' + m' : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  exact grid_indiff_of_eqSum_of_diagonalStep P g hdiag hsum

/-! ## §8.  Instantiation on the concrete standard-sequence rectangle

The abstract §6 reduction applies to the concrete two-coordinate grid
`g n m = update (update base j (vⱼ n)) k (vₖ m)` built from two coordinate grid
maps `vⱼ : ℕ → X j`, `vₖ : ℕ → X k`.  This section names that grid and the
concrete **matched diagonal-step** primitive, then instantiates the §6 results
to obtain equal-index-sum indifference on the concrete rectangle.

The matched diagonal step — `g (n+1) m ∼ g n (m+1)` — is the genuine §IV.5
residual: on the standard-sequence rectangle with matched reference exchanges, it
is the `spaced` indifference equating one `j`-grid-step with one `k`-grid-step.
Everything downstream (equal-sum indifference, the score bridge) is the
theorem-backed §6 machinery. -/

/-- The concrete two-coordinate grid profile: `base` updated at `j` to `vⱼ n` and
at `k` to `vₖ m`.  (Same shape as `Certificates.PairwiseGridProfile`.) -/
def concreteGrid (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (n m : ℕ) : Profile X :=
  Function.update (Function.update base j (vⱼ n)) k (vₖ m)

/-- **Matched diagonal-step primitive on the concrete rectangle.**

The named §IV.5 residual: on the standard-sequence rectangle, trading one
`j`-grid-step for one `k`-grid-step preserves indifference. -/
def ConcreteDiagonalStep (P : ProductPref X)
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) : Prop :=
  ∀ n m, P.indiff (concreteGrid base j k vⱼ vₖ (n + 1) m)
                  (concreteGrid base j k vⱼ vₖ n (m + 1))

/-- **Equal-index-sum indifference on the concrete rectangle.**

Direct instantiation of `grid_indiff_of_eqSum_of_diagonalStep` at the concrete
grid: from the matched diagonal-step primitive, any two concrete grid profiles
with equal index sum are indifferent. -/
theorem concreteGrid_indiff_of_eqSum
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (hdiag : ConcreteDiagonalStep P base j k vⱼ vₖ)
    {n m n' m' : ℕ} (hsum : n + m = n' + m') :
    P.indiff (concreteGrid base j k vⱼ vₖ n m)
             (concreteGrid base j k vⱼ vₖ n' m') :=
  grid_indiff_of_eqSum_of_diagonalStep P (concreteGrid base j k vⱼ vₖ) hdiag hsum

/-- **Score-calibrated indifference on the concrete rectangle.**

Instantiation of the §7 bridge: with the additive index-sum score and the matched
diagonal step, equal grid-normalized score forces concrete-grid indifference.
This is the §IV.5 calibration realized on the concrete rectangle, modulo the
single matched-diagonal-step residual. -/
theorem concreteGrid_indiff_of_score_eq
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (F : ℕ → ℕ → ℝ) (hF : ∀ n m, F n m = (n : ℝ) + (m : ℝ))
    (hdiag : ConcreteDiagonalStep P base j k vⱼ vₖ)
    {n m n' m' : ℕ} (hscore : F n m = F n' m') :
    P.indiff (concreteGrid base j k vⱼ vₖ n m)
             (concreteGrid base j k vⱼ vₖ n' m') :=
  grid_indiff_of_score_eq_of_diagonalStep P (concreteGrid base j k vⱼ vₖ) F hF hdiag hscore

/-- **The matched diagonal step is the `spaced`-shaped §IV.5 residual.**

Records the precise local fact the `ConcreteDiagonalStep` primitive demands at
each `(n, m)`: the profile with `j` at grid-step `n+1`, `k` at step `m` is
indifferent to the profile with `j` at step `n`, `k` at step `m+1`.  This is the
exact shape supplied, on the actual standard-sequence rectangle with matched
reference exchanges, by the spacing indifferences — the genuine §IV.5 content,
now isolated as this one primitive while all surrounding calibration is
theorem-backed. -/
theorem concreteDiagonalStep_iff
    (P : ProductPref X)
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) :
    ConcreteDiagonalStep P base j k vⱼ vₖ ↔
      ∀ n m, P.indiff
        (Function.update (Function.update base j (vⱼ (n + 1))) k (vₖ m))
        (Function.update (Function.update base j (vⱼ n)) k (vₖ (m + 1))) :=
  Iff.rfl

/-! ## §9.  A single diagonal layer is *literally* the `spaced` field

The honest, exact connection between the matched diagonal-step primitive and the
standard-sequence `spaced` field, at **one** `k`-layer.

A standard sequence `σ` on `j` carries a reference exchange `(σ.r, σ.s)` on its
auxiliary coordinate `σ.k`.  Its `spaced n` field is exactly

  `(α n at j, σ.r at k) ∼ (α (n+1) at j, σ.s at k)`.

If the `k`-grid `vₖ` is arranged so that one consecutive pair lands on the
reference exchange — `vₖ m = σ.s` and `vₖ (m+1) = σ.r` — then the matched
diagonal step at that layer `(n, m)` is *literally* `σ.spaced n` (symmetrized).
No hexagon, no fabrication: it is the spacing field itself.

This proves the diagonal step on the **reference layer**.  Propagating it to all
other `k`-layers — turning "one layer" into the full `ConcreteDiagonalStep` — is
the genuine §IV.5 hexagon-combination residual, deliberately **not** discharged
here. -/

/-- **The matched diagonal step at the reference layer is the `spaced` field.**

For a standard sequence `σ` and a `k`-grid `vₖ` with `vₖ m = σ.s`,
`vₖ (m+1) = σ.r`, the diagonal-step indifference at layer `(n, m)` over base
`σ.base`, with `j`-grid `σ.α`, holds — it is exactly `σ.spaced n` (with its two
sides swapped).  Fully theorem-backed; uses only the standard-sequence field. -/
theorem diagonalStep_referenceLayer_of_spaced
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (vₖ : ℕ → X σ.k) (n m : ℕ)
    (hsm : vₖ m = σ.s) (hrm : vₖ (m + 1) = σ.r) :
    P.indiff
      (concreteGrid σ.base j σ.k σ.α vₖ (n + 1) m)
      (concreteGrid σ.base j σ.k σ.α vₖ n (m + 1)) := by
  -- Unfold the concrete grid and substitute the reference values.
  unfold concreteGrid
  rw [hsm, hrm]
  -- Goal: indiff (update (update base j (α (n+1))) k σ.s)
  --              (update (update base j (α n))     k σ.r)
  -- `σ.spaced n` is the reverse: indiff (α n, σ.r) (α (n+1), σ.s).  Swap it.
  exact ⟨(σ.spaced n).2, (σ.spaced n).1⟩

/-- **Reference-layer matched diagonal step (uniform-in-`n` form).**

The same fact for every `j`-index `n` at the fixed reference layer `m`: this is
the `n`-indexed family of `spaced` indifferences, repackaged in the
diagonal-step shape.  It is the honest "one full column of the diagonal step"
that the standard-sequence construction supplies directly. -/
theorem diagonalStep_referenceLayer_forall_n_of_spaced
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (vₖ : ℕ → X σ.k) (m : ℕ)
    (hsm : vₖ m = σ.s) (hrm : vₖ (m + 1) = σ.r) :
    ∀ n, P.indiff
      (concreteGrid σ.base j σ.k σ.α vₖ (n + 1) m)
      (concreteGrid σ.base j σ.k σ.α vₖ n (m + 1)) :=
  fun n => diagonalStep_referenceLayer_of_spaced P σ vₖ n m hsm hrm

/-! ## §10.  Layer propagation: the precise remaining §IV.5 residual

§9 supplies the matched diagonal step at the **reference layer** `m₀` (where the
`k`-grid hits the reference exchange) directly from `spaced`.  The full
`ConcreteDiagonalStep` requires the step at **every** layer `m`.  Wakker §IV.5
propagates it across layers using the hexagon (`TradeoffConsistency`): the
diagonal step at layer `m` and at layer `m+1` are linked because both are
`{j,k}`-slice indifferences sharing structure.

This section names that propagation as a single explicit primitive and proves
that **reference-layer step + layer-propagation ⟹ full `ConcreteDiagonalStep`**.
So the entire §IV.5 diagonal residual is now exactly the layer-propagation
primitive; the reference layer itself is theorem-backed (§9), and all downstream
calibration is theorem-backed (§6–§8). -/

/-- **Layer-propagation primitive.**

The diagonal step transports from layer `m` to layer `m+1`: if `g(n+1) m ∼
g n (m+1)` for all `n`, then `g(n+1)(m+1) ∼ g n (m+2)` for all `n`.  This is the
genuine §IV.5 hexagon-combination content (linking adjacent `k`-layers). -/
def DiagonalLayerPropagation (P : ProductPref X)
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) : Prop :=
  ∀ m,
    (∀ n, P.indiff (concreteGrid base j k vⱼ vₖ (n + 1) m)
                   (concreteGrid base j k vⱼ vₖ n (m + 1))) →
    (∀ n, P.indiff (concreteGrid base j k vⱼ vₖ (n + 1) (m + 1))
                   (concreteGrid base j k vⱼ vₖ n (m + 2)))

/-- **Full `ConcreteDiagonalStep` from a reference-layer step + layer
propagation.**

If the diagonal step holds at the base layer `m = 0` (for all `n`) and the
layer-propagation primitive holds, then the diagonal step holds at every layer —
i.e. the full `ConcreteDiagonalStep`.  Pure induction on the layer `m`; the
genuine content is entirely in the two hypotheses (`base layer` from §9 when the
reference exchange sits at layer 0; `propagation` the §IV.5 residual). -/
theorem concreteDiagonalStep_of_baseLayer_and_propagation
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (hbase : ∀ n, P.indiff (concreteGrid base j k vⱼ vₖ (n + 1) 0)
                           (concreteGrid base j k vⱼ vₖ n 1))
    (hprop : DiagonalLayerPropagation P base j k vⱼ vₖ) :
    ConcreteDiagonalStep P base j k vⱼ vₖ := by
  intro n m
  -- Prove the layer-`m` step for all `n` by induction on `m`.
  have hlayer : ∀ m, ∀ n, P.indiff (concreteGrid base j k vⱼ vₖ (n + 1) m)
                                   (concreteGrid base j k vⱼ vₖ n (m + 1)) := by
    intro m
    induction m with
    | zero => exact hbase
    | succ m ih => exact hprop m ih
  exact hlayer m n

/-- **`ConcreteDiagonalStep` for the standard-sequence grid seeded at layer 0.**

The honest assembly: if the `k`-grid puts the reference exchange at the base
layer (`vₖ 0 = σ.s`, `vₖ 1 = σ.r`), then §9 gives the base-layer step from
`spaced`, and layer propagation lifts it to the full `ConcreteDiagonalStep`.  The
only residual hypothesis is `DiagonalLayerPropagation` — the named §IV.5
hexagon-combination content. -/
theorem concreteDiagonalStep_of_spaced_and_propagation
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (vₖ : ℕ → X σ.k)
    (hs0 : vₖ 0 = σ.s) (hr1 : vₖ 1 = σ.r)
    (hprop : DiagonalLayerPropagation P σ.base j σ.k σ.α vₖ) :
    ConcreteDiagonalStep P σ.base j σ.k σ.α vₖ :=
  concreteDiagonalStep_of_baseLayer_and_propagation P σ.base j σ.k σ.α vₖ
    (diagonalStep_referenceLayer_forall_n_of_spaced P σ vₖ 0 hs0 hr1)
    hprop

/-! ## §11.  Layer propagation: a two-coordinate slice residual

**Honest scope analysis.**  The formalized `TradeoffConsistency.consistent`
constrains only profiles differing at a **single** coordinate `j` (every premise
is `agreeOff {j}`).  Instantiating it with the three premise-indifferences equal
recovers exactly the single-coordinate base-independence of §1 — nothing more.

`DiagonalLayerPropagation` transports the diagonal step from layer `m` to layer
`m+1`, and the layer-`m+1` conclusion mentions `vₖ (m+2)`, a value appearing in
**no** layer-`m` relation.  So propagation is **not** a finite consequence of the
layer-`m` diagonal plus the single-coordinate axiom: it genuinely needs a
**two-coordinate slice condition** that the single-coordinate
`TradeoffConsistency` does not provide.

This section names one such condition, `SliceThomsenMove`, in the exact form that
yields layer propagation, and proves — theorem-backed — that it **discharges**
propagation.  **Caveat (corrected in §13):** despite its name, `SliceThomsenMove`
is *not* the standard additive-conjoint Thomsen condition.  Its real content is
the **equal spacing of the `k`-grid** (`KGridEqualSpacing`, §13), which is
strictly different from — and in the relevant respect stronger than — the genuine
standard Thomsen double-cancellation `StandardThomsen` (§13).  The name is kept
for continuity; §13 gives the precise, honest decomposition. -/

/-- **Slice Thomsen move on the concrete rectangle (misnamed; see §13).**

A two-coordinate slice condition stated in the exact form that yields layer
propagation: from the layer-`m` diagonals at `n` and `n+1`, the layer-`(m+1)`
diagonal at `n` follows.

Concretely, for all `m, n`: given `g(n+1) m ∼ g n (m+1)` and
`g(n+2) m ∼ g(n+1)(m+1)`, conclude `g(n+1)(m+1) ∼ g n (m+2)`.

**Honest caveat (§13):** this is *not* the standard additive-conjoint Thomsen
condition.  An additive re-analysis (§13) shows premise P2 is redundant and the
real content is `k`-grid equal spacing (`t(m+1)−t m = t(m+2)−t(m+1)`): the level
`vₖ (m+2)` occurs in the conclusion but in neither premise, so it is not a
cancellation.  The genuine standard Thomsen condition is `StandardThomsen` (§13).
It is still **not** derivable from the single-coordinate `TradeoffConsistency`. -/
def SliceThomsenMove (P : ProductPref X)
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) : Prop :=
  ∀ m n,
    P.indiff (concreteGrid base j k vⱼ vₖ (n + 1) m)
             (concreteGrid base j k vⱼ vₖ n (m + 1)) →
    P.indiff (concreteGrid base j k vⱼ vₖ (n + 2) m)
             (concreteGrid base j k vⱼ vₖ (n + 1) (m + 1)) →
    P.indiff (concreteGrid base j k vⱼ vₖ (n + 1) (m + 1))
             (concreteGrid base j k vⱼ vₖ n (m + 2))

/-- **Layer propagation from the slice "Thomsen" move.**

Theorem-backed discharge of `DiagonalLayerPropagation` from `SliceThomsenMove`:
given the whole layer-`m` diagonal column (`∀ n, g(n+1) m ∼ g n (m+1)`), the
move at each `n` (fed the layer-`m` diagonals at `n` and `n+1`) yields the
layer-`(m+1)` diagonal at `n`.

This proves "`SliceThomsenMove` ⟹ layer propagation".  (See §13 for the honest
decomposition of what `SliceThomsenMove` actually demands.) -/
theorem diagonalLayerPropagation_of_sliceThomsenMove
    (P : ProductPref X)
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (hthom : SliceThomsenMove P base j k vⱼ vₖ) :
    DiagonalLayerPropagation P base j k vⱼ vₖ := by
  intro m hlayer n
  exact hthom m n (hlayer n) (hlayer (n + 1))

/-- **Full `ConcreteDiagonalStep` from `spaced` + the slice move.**

The complete §IV.5 assembly: the reference layer from `spaced` (§9), layer
propagation from `SliceThomsenMove` (§11), and the induction (§10) combine to
give the entire matched diagonal step.  The **only** non-theorem-backed input is
`SliceThomsenMove` — the two-coordinate slice residual (whose precise content is
decomposed honestly in §13). -/
theorem concreteDiagonalStep_of_spaced_and_thomsen
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (vₖ : ℕ → X σ.k)
    (hs0 : vₖ 0 = σ.s) (hr1 : vₖ 1 = σ.r)
    (hthom : SliceThomsenMove P σ.base j σ.k σ.α vₖ) :
    ConcreteDiagonalStep P σ.base j σ.k σ.α vₖ :=
  concreteDiagonalStep_of_spaced_and_propagation P σ vₖ hs0 hr1
    (diagonalLayerPropagation_of_sliceThomsenMove P σ.base j σ.k σ.α vₖ hthom)

/-- **End-to-end §IV.5 grid calibration from `spaced` + the slice move.**

The capstone: equal-index-sum grid indifference on the standard-sequence
rectangle, from `spaced` (reference layer) + `SliceThomsenMove` + nothing
else.  Combines `concreteDiagonalStep_of_spaced_and_thomsen` with
`concreteGrid_indiff_of_eqSum`.  This is the full §IV.5 calibration core reduced
to the single residual `SliceThomsenMove` (decomposed honestly in §13). -/
theorem concreteGrid_indiff_of_eqSum_of_spaced_and_thomsen
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j : ι} (σ : ProductPref.StandardSequence P j)
    (vₖ : ℕ → X σ.k)
    (hs0 : vₖ 0 = σ.s) (hr1 : vₖ 1 = σ.r)
    (hthom : SliceThomsenMove P σ.base j σ.k σ.α vₖ)
    {n m n' m' : ℕ} (hsum : n + m = n' + m') :
    P.indiff (concreteGrid σ.base j σ.k σ.α vₖ n m)
             (concreteGrid σ.base j σ.k σ.α vₖ n' m') :=
  concreteGrid_indiff_of_eqSum P σ.base j σ.k σ.α vₖ
    (concreteDiagonalStep_of_spaced_and_thomsen P σ vₖ hs0 hr1 hthom) hsum

/-! ## §12.  `SliceThomsenMove` is exactly the representation's diagonal content

§11 surfaced the architectural finding: `SliceThomsenMove` is the genuine
two-coordinate §IV.5 residual, **not** derivable from the single-coordinate
`TradeoffConsistency`.  This section pins down *why* it is the crux: it is
**equivalent to having a grid-normalized additive slice representation** whose
indices add.  Concretely, both `ConcreteDiagonalStep` and `SliceThomsenMove`
follow immediately from such a representation, and the representation's
additive-index shape makes the Thomsen move a one-line arithmetic fact.

This is the honest characterization: `SliceThomsenMove` cannot be obtained for
free precisely because *possessing it is tantamount to possessing the additive
representation* — which is exactly the §IV.5 theorem.  We make that precise by
deriving the move from a representation, so the residual is identified as
"the slice carries a grid-additive representation", the genuine §IV.5 output. -/

/-- **Grid-additive slice representation.**

A real-valued slice score `S : Profile X → ℝ` *grid-additively represents* the
preference on the concrete rectangle if (i) it tracks weak preference between
grid profiles (`weakPref ↔ S-≤`) and (ii) it is grid-normalized additively
(`S (g n m) = n + m`).  This is the §IV.5 calibration output, restricted to the
grid. -/
def GridAdditiveSliceRep (P : ProductPref X)
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (S : Profile X → ℝ) : Prop :=
  (∀ n m n' m', P.weakPref (concreteGrid base j k vⱼ vₖ n m)
                           (concreteGrid base j k vⱼ vₖ n' m')
      ↔ S (concreteGrid base j k vⱼ vₖ n' m') ≤ S (concreteGrid base j k vⱼ vₖ n m)) ∧
  (∀ n m, S (concreteGrid base j k vⱼ vₖ n m) = (n : ℝ) + (m : ℝ))

/-- **Grid indifference iff equal index sum, under a grid-additive
representation.**

From `GridAdditiveSliceRep`, two grid profiles are indifferent **iff** their
index sums are equal: indifference is `S`-equality (both `≤` directions), and `S`
is the index sum.  This is the representation's exact diagonal content. -/
theorem gridIndiff_iff_eqSum_of_rep
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (S : Profile X → ℝ) (hrep : GridAdditiveSliceRep P base j k vⱼ vₖ S)
    (n m n' m' : ℕ) :
    P.indiff (concreteGrid base j k vⱼ vₖ n m)
             (concreteGrid base j k vⱼ vₖ n' m') ↔ n + m = n' + m' := by
  obtain ⟨hord, hnorm⟩ := hrep
  constructor
  · rintro ⟨h1, h2⟩
    have hle1 := (hord n m n' m').mp h1
    have hle2 := (hord n' m' n m).mp h2
    rw [hnorm n m, hnorm n' m'] at hle1 hle2
    have : (n : ℝ) + m = (n' : ℝ) + m' := le_antisymm (by linarith) (by linarith)
    have hcast : ((n + m : ℕ) : ℝ) = ((n' + m' : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast hcast
  · intro hsum
    refine ⟨(hord n m n' m').mpr ?_, (hord n' m' n m).mpr ?_⟩ <;>
      · rw [hnorm n m, hnorm n' m']
        have : (n : ℝ) + m = (n' : ℝ) + m' := by
          have : ((n + m : ℕ) : ℝ) = ((n' + m' : ℕ) : ℝ) := by exact_mod_cast hsum
          push_cast at this; linarith
        linarith

/-- **`ConcreteDiagonalStep` from a grid-additive representation.**

The diagonal step `g(n+1) m ∼ g n (m+1)` holds because both sides have equal
index sum `n + m + 1`, so `gridIndiff_iff_eqSum_of_rep` gives indifference. -/
theorem concreteDiagonalStep_of_rep
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (S : Profile X → ℝ) (hrep : GridAdditiveSliceRep P base j k vⱼ vₖ S) :
    ConcreteDiagonalStep P base j k vⱼ vₖ := by
  intro n m
  exact (gridIndiff_iff_eqSum_of_rep P base j k vⱼ vₖ S hrep (n + 1) m n (m + 1)).mpr (by omega)

/-- **`SliceThomsenMove` from a grid-additive representation.**

The Thomsen move's conclusion `g(n+1)(m+1) ∼ g n (m+2)` has both sides at index
sum `n + m + 2`, so it holds by `gridIndiff_iff_eqSum_of_rep` regardless of the
premises.  This shows the move is a *consequence* of the representation — i.e.
the genuine §IV.5 residual `SliceThomsenMove` is exactly representation-level
content, the reason it cannot be obtained from the single-coordinate axiom. -/
theorem sliceThomsenMove_of_rep
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (S : Profile X → ℝ) (hrep : GridAdditiveSliceRep P base j k vⱼ vₖ S) :
    SliceThomsenMove P base j k vⱼ vₖ := by
  intro m n _h1 _h2
  exact (gridIndiff_iff_eqSum_of_rep P base j k vⱼ vₖ S hrep (n + 1) (m + 1) n (m + 2)).mpr (by omega)

/-! ## §13.  Honest decomposition: `SliceThomsenMove` is *equal `k`-grid spacing*,
not the standard Thomsen condition

**Correction of the Phase 35/36 framing.**  Phases 35–36 called `SliceThomsenMove`
"the standard two-coordinate (additive-conjoint) Thomsen condition".  A direct
additive re-analysis shows this is **imprecise**.  Write a grid-additive value as
`V (g n m) = s n + t m`.  Then `SliceThomsenMove` at `(m, n)` reads:

* premise P1  `g(n+1) m ∼ g n (m+1)`     ⟺  `s(n+1) − s n = t(m+1) − t m`
* premise P2  `g(n+2) m ∼ g(n+1)(m+1)`   ⟺  `s(n+2) − s(n+1) = t(m+1) − t m`
* conclusion C `g(n+1)(m+1) ∼ g n (m+2)` ⟺  `s(n+1) − s n = t(m+2) − t(m+1)`

Two things stand out.  First, **P2 is redundant**: P1 alone, combined with C's
demand, is what matters; the proof of `diagonalLayerPropagation_of_sliceThomsenMove`
above in fact only ever feeds P1's content through.  Second, and decisively, the
level `vₖ (m+2)` occurs in C but in **neither** premise.  So C is **not** a
cancellation of shared middle terms — the hallmark of the genuine Thomsen
condition.  What C actually demands, given P1, is

    `t(m+1) − t m = t(m+2) − t(m+1)`   (consecutive `k`-grid steps are equal),

i.e. **equal spacing of the `k`-grid**, a grid-specific metric condition — *not*
the structural double-cancellation that any additive representation satisfies for
free.

This section makes the honest decomposition precise:

* `KGridEqualSpacing` — the real content of `SliceThomsenMove`, isolated as the
  equal-`k`-spacing condition (in preference form, premise P2 dropped).  It is
  *stronger* than `SliceThomsenMove` (`KGridEqualSpacing ⟹ SliceThomsenMove`) and
  drives layer propagation directly.
* `StandardThomsen` — the **genuine** additive-conjoint Thomsen double-cancellation
  (`(a₁,b₂)∼(a₂,b₁)` & `(a₂,b₃)∼(a₃,b₂) ⟹ (a₁,b₃)∼(a₃,b₁)`), where every level
  appears in both premises and conclusion and the middles `a₂, b₂` cancel.  This
  is what the literature calls the Thomsen condition; it is **different** from
  `KGridEqualSpacing`.

Both follow from a `GridAdditiveSliceRep`, but they are not the same condition:
`StandardThomsen` is a structural cancellation true of *every* additive
representation, whereas `KGridEqualSpacing` is the metric fact that the chosen
grid points are equally spaced.  The Phase 35/36 conflation of the two is
corrected here. -/

/-- **Equal `k`-grid spacing (the real content of `SliceThomsenMove`).**

In preference form: whenever a `j`-grid step compensates the `k`-step `m → m+1`,
that *same* `j`-step also compensates the next `k`-step `m+1 → m+2`.  Additively
(given a matching `j`-step exists, which `spaced` supplies) this is exactly
`t(m+1) − t m = t(m+2) − t(m+1)`: the consecutive `k`-grid steps are equal.

This is `SliceThomsenMove` with the redundant premise P2 removed, hence strictly
stronger; it is the honest residual that layer propagation actually needs. -/
def KGridEqualSpacing (P : ProductPref X)
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) : Prop :=
  ∀ m n,
    P.indiff (concreteGrid base j k vⱼ vₖ (n + 1) m)
             (concreteGrid base j k vⱼ vₖ n (m + 1)) →
    P.indiff (concreteGrid base j k vⱼ vₖ (n + 1) (m + 1))
             (concreteGrid base j k vⱼ vₖ n (m + 2))

/-- **`KGridEqualSpacing ⟹ SliceThomsenMove`.**

The equal-spacing condition is strictly stronger: it concludes C from P1 alone,
so a fortiori from P1 and P2.  This exhibits the redundancy of premise P2 in
`SliceThomsenMove` and identifies the equal-`k`-spacing condition as its genuine
content. -/
theorem sliceThomsenMove_of_kGridEqualSpacing
    (P : ProductPref X)
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (hspace : KGridEqualSpacing P base j k vⱼ vₖ) :
    SliceThomsenMove P base j k vⱼ vₖ := by
  intro m n h1 _h2
  exact hspace m n h1

/-- **Layer propagation directly from equal `k`-grid spacing.**

The cleanest path to `DiagonalLayerPropagation`: the equal-spacing condition feeds
the layer-`m` diagonal at `n` straight to the layer-`(m+1)` diagonal at `n`, with
no spurious second premise.  (Factoring through `SliceThomsenMove` gives the same
result via `sliceThomsenMove_of_kGridEqualSpacing` + §11.) -/
theorem diagonalLayerPropagation_of_kGridEqualSpacing
    (P : ProductPref X)
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (hspace : KGridEqualSpacing P base j k vⱼ vₖ) :
    DiagonalLayerPropagation P base j k vⱼ vₖ := by
  intro m hlayer n
  exact hspace m n (hlayer n)

/-- **The genuine standard (additive-conjoint) Thomsen condition on the grid.**

The double-cancellation condition from additive conjoint measurement: with
`j`-indices `i₁, i₂, i₃` and `k`-indices `l₁, l₂, l₃`,

    `g i₁ l₂ ∼ g i₂ l₁`  and  `g i₂ l₃ ∼ g i₃ l₂`   ⟹   `g i₁ l₃ ∼ g i₃ l₁`.

Every level appears in the premises and the conclusion; the middle levels
`i₂, l₂` cancel.  This — *not* `SliceThomsenMove` — is what the literature calls
the Thomsen condition.  It is a structural cancellation satisfied by any additive
representation, and is genuinely different from `KGridEqualSpacing` (which is a
metric equal-spacing fact about the specific grid points). -/
def StandardThomsen (P : ProductPref X)
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k) : Prop :=
  ∀ i₁ i₂ i₃ l₁ l₂ l₃ : ℕ,
    P.indiff (concreteGrid base j k vⱼ vₖ i₁ l₂)
             (concreteGrid base j k vⱼ vₖ i₂ l₁) →
    P.indiff (concreteGrid base j k vⱼ vₖ i₂ l₃)
             (concreteGrid base j k vⱼ vₖ i₃ l₂) →
    P.indiff (concreteGrid base j k vⱼ vₖ i₁ l₃)
             (concreteGrid base j k vⱼ vₖ i₃ l₁)

/-- **`StandardThomsen` from a grid-additive representation (genuine
cancellation).**

Unlike `SliceThomsenMove`, the standard Thomsen condition is a true cancellation:
the two premises give `i₁ + l₂ = i₂ + l₁` and `i₂ + l₃ = i₃ + l₂`; adding and
cancelling the shared middles `i₂, l₂` yields `i₁ + l₃ = i₃ + l₁`, the conclusion.
Theorem-backed from `GridAdditiveSliceRep` via `gridIndiff_iff_eqSum_of_rep`. -/
theorem standardThomsen_of_rep
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (S : Profile X → ℝ) (hrep : GridAdditiveSliceRep P base j k vⱼ vₖ S) :
    StandardThomsen P base j k vⱼ vₖ := by
  intro i₁ i₂ i₃ l₁ l₂ l₃ h1 h2
  have e1 : i₁ + l₂ = i₂ + l₁ :=
    (gridIndiff_iff_eqSum_of_rep P base j k vⱼ vₖ S hrep i₁ l₂ i₂ l₁).mp h1
  have e2 : i₂ + l₃ = i₃ + l₂ :=
    (gridIndiff_iff_eqSum_of_rep P base j k vⱼ vₖ S hrep i₂ l₃ i₃ l₂).mp h2
  exact (gridIndiff_iff_eqSum_of_rep P base j k vⱼ vₖ S hrep i₁ l₃ i₃ l₁).mpr (by omega)

/-- **`KGridEqualSpacing` from a grid-additive representation.**

The grid-normalized representation (`S (g n m) = n + m`) bakes equal spacing in:
both sides of the conclusion sit at index sum `n + m + 2`, so they are
indifferent regardless of the premise.  This confirms `KGridEqualSpacing` is a
representation-level consequence — the equal-spacing facet that the
grid-normalization encodes. -/
theorem kGridEqualSpacing_of_rep
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    (base : Profile X) (j k : ι) (vⱼ : ℕ → X j) (vₖ : ℕ → X k)
    (S : Profile X → ℝ) (hrep : GridAdditiveSliceRep P base j k vⱼ vₖ S) :
    KGridEqualSpacing P base j k vⱼ vₖ := by
  intro m n _h1
  exact (gridIndiff_iff_eqSum_of_rep P base j k vⱼ vₖ S hrep (n + 1) (m + 1) n (m + 2)).mpr (by omega)

/-! ## §14.  Two-pivot cross-slice transport (§IV.6, obligation 3)

The §IV.6 cross-pair content (`nonPivotPairAdditivityCertificate`): from two
pivot-slice representations sharing a common pivot utility `V₀`, derive the
*non-pivot* `{j,k}`-slice representation.

With three pairwise-distinct coordinates `j₀, j, k` and utilities
`V₀ : X j₀ → ℝ`, `Vj : X j → ℝ`, `Vk : X k → ℝ`, suppose

* the `{j₀,j}`-slice is represented by `(V₀, Vj)`, and
* the `{j₀,k}`-slice is represented by `(V₀, Vk)`.

Then the `{j,k}`-slice is represented by `(Vj, Vk)` — **provided** the pivot
coordinate's utility image is rich enough to compensate any `j`-difference
(`PivotCompensatesJ`).  That coverage condition is the genuine §IV.6 residual
(Wakker's pivot solvability / coordinate-image coverage); everything else here
is theorem-backed.

The transport is a clean order chain: to compare `x` and `y` (agreeing off
`{j,k}`), interpose a profile `z` that moves the `j`-difference onto the pivot
`j₀` — the existence of the compensating pivot value is exactly
`PivotCompensatesJ`.  Then `x ∼ z` is a `{j₀,j}`-slice fact, `z` vs `y` is a
`{j₀,k}`-slice fact, and the additive bookkeeping collapses to the `{j,k}`
inequality.

The representation hypotheses and conclusion are written in the inline
`∀ x y, agreeOff {·,·} x y → (weakPref ↔ additive-score)` form, which is exactly
`Certificates.PairwiseSliceRepresentationCertificate` unfolded (this module
deliberately imports only `Core`, mirroring §4–§5). -/

/-- **Pivot coordinate-image coverage (the §IV.6 transport residual).**

The pivot utility `V₀` can compensate any `j`-coordinate utility difference: for
any pivot anchor `p` and any two `j`-values `a, b`, some pivot value `q` realizes
`V₀ q = V₀ p + Vj a − Vj b`.  This is Wakker's pivot solvability / coordinate-
image coverage — exactly what two-pivot transport needs, and no more. -/
def PivotCompensatesJ {j₀ j : ι} (V₀ : X j₀ → ℝ) (Vj : X j → ℝ) : Prop :=
  ∀ (p : X j₀) (a b : X j), ∃ q : X j₀, V₀ q = V₀ p + Vj a - Vj b

/-- **Two-pivot cross-slice transport (§IV.6 / obligation 3).**

From the two pivot-slice representations `(V₀, Vj)` on `{j₀,j}` and `(V₀, Vk)` on
`{j₀,k}`, plus the pivot coverage residual `PivotCompensatesJ`, the non-pivot
`{j,k}`-slice is represented by `(Vj, Vk)`.

The proof interposes `z = update (update x j₀ q) j (y j)` with `q` the
coverage-supplied pivot value (so `V₀ q = V₀ (x j₀) + Vj (x j) − Vj (y j)`):
`x ∼ z` by the `{j₀,j}`-slice representation (equal scores), and `weakPref z y`
is the `{j₀,k}`-slice inequality, which the substitution turns into the target
`{j,k}` inequality.  Every step except `PivotCompensatesJ` is theorem-backed. -/
theorem twoPivotSliceTransport
    (P : ProductPref X) [ProductPref.IsWeakOrder P]
    {j₀ j k : ι} (hj₀j : j₀ ≠ j) (hj₀k : j₀ ≠ k) (hjk : j ≠ k)
    (V₀ : X j₀ → ℝ) (Vj : X j → ℝ) (Vk : X k → ℝ)
    (hjrep : ∀ x y : Profile X, Profile.agreeOff ({j₀, j} : Set ι) x y →
      (P.weakPref x y ↔ V₀ (y j₀) + Vj (y j) ≤ V₀ (x j₀) + Vj (x j)))
    (hkrep : ∀ x y : Profile X, Profile.agreeOff ({j₀, k} : Set ι) x y →
      (P.weakPref x y ↔ V₀ (y j₀) + Vk (y k) ≤ V₀ (x j₀) + Vk (x k)))
    (hcov : PivotCompensatesJ V₀ Vj) :
    ∀ x y : Profile X, Profile.agreeOff ({j, k} : Set ι) x y →
      (P.weakPref x y ↔ Vj (y j) + Vk (y k) ≤ Vj (x j) + Vk (x k)) := by
  intro x y hxy
  -- The pivot value is shared by x and y (j₀ ∉ {j,k}).
  have hj₀_not : (j₀ : ι) ∉ ({j, k} : Set ι) := by
    intro hmem
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hj₀j h
    · exact hj₀k h
  have hpiv : x j₀ = y j₀ := hxy j₀ hj₀_not
  have hpivV : V₀ (x j₀) = V₀ (y j₀) := by rw [hpiv]
  -- Choose the compensating pivot value.
  obtain ⟨q, hq⟩ := hcov (x j₀) (x j) (y j)
  -- The interposed profile and its coordinate values.
  set z : Profile X := Function.update (Function.update x j₀ q) j (y j) with hzdef
  have hzj₀ : z j₀ = q := by rw [hzdef, Function.update_of_ne hj₀j]; simp
  have hzj : z j = y j := by rw [hzdef]; simp
  have hzk : z k = x k := by
    rw [hzdef, Function.update_of_ne (Ne.symm hjk), Function.update_of_ne (Ne.symm hj₀k)]
  -- x and z agree off {j₀, j}.
  have hagree_xz : Profile.agreeOff ({j₀, j} : Set ι) x z := by
    intro i hi
    have hij₀ : i ≠ j₀ := fun e => hi (by simp [e])
    have hij : i ≠ j := fun e => hi (by simp [e])
    rw [hzdef, Function.update_of_ne hij, Function.update_of_ne hij₀]
  -- z and y agree off {j₀, k}.
  have hagree_zy : Profile.agreeOff ({j₀, k} : Set ι) z y := by
    intro i hi
    have hij₀ : i ≠ j₀ := fun e => hi (by simp [e])
    have hik : i ≠ k := fun e => hi (by simp [e])
    by_cases hij : i = j
    · rw [hij, hzj]
    · rw [hzdef, Function.update_of_ne hij, Function.update_of_ne hij₀]
      have hi_not : i ∉ ({j, k} : Set ι) := by
        intro hmem
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with h | h
        · exact hij h
        · exact hik h
      exact hxy i hi_not
  -- x ∼ z (equal {j₀,j}-scores).
  have hxz : P.weakPref x z := by
    rw [hjrep x z hagree_xz, hzj₀, hzj]; linarith [hq]
  have hzx : P.weakPref z x := by
    rw [hjrep z x (Profile.agreeOff_symm hagree_xz), hzj₀, hzj]; linarith [hq]
  -- weakPref z y is the {j₀,k}-inequality, equivalent to the target {j,k}-inequality.
  have hzy_iff : P.weakPref z y ↔ Vj (y j) + Vk (y k) ≤ Vj (x j) + Vk (x k) := by
    rw [hkrep z y hagree_zy, hzj₀, hzk]
    constructor <;> intro h <;> linarith [hq, hpivV]
  -- Chain through the indifference x ∼ z.
  constructor
  · intro hxy_pref
    exact hzy_iff.mp (ProductPref.IsWeakOrder.transitive _ _ _ hzx hxy_pref)
  · intro htarget
    exact ProductPref.IsWeakOrder.transitive _ _ _ hxz (hzy_iff.mpr htarget)

/-- **Pivot coverage from a surjective pivot utility (partial discharge).**

If the pivot utility `V₀` is surjective (its image is all of ℝ), then
`PivotCompensatesJ` holds trivially: the required value `V₀ p + Vj a − Vj b` is
hit by some pivot value.  This is the honest degenerate discharge of the §IV.6
coverage residual — the same role surjective grids play for obligation 1. -/
theorem pivotCompensatesJ_of_surjective {j₀ j : ι}
    (V₀ : X j₀ → ℝ) (Vj : X j → ℝ) (hsurj : Function.Surjective V₀) :
    PivotCompensatesJ V₀ Vj := by
  intro p a b
  exact hsurj (V₀ p + Vj a - Vj b)

/-! ## §15.  Pivot coverage from the intermediate value theorem (engine A for §IV.6)

The §IV.6 coverage residual `PivotCompensatesJ` (and hence the two-pivot
transport, the §IV.6 cross-pair additivity, and obligation 16) was reduced in
Phases 38–40 to the single condition "the pivot utility image is rich enough to
compensate coordinate differences".  This section discharges that condition the
same way engine A (`RawAxiomDischargersIVT.lean`) discharges the §III.4 brackets:
by the **intermediate value theorem**.

If the pivot coordinate type is topologically connected, the pivot utility `V₀`
is continuous, and its image is unbounded above and below, then `V₀` is
surjective onto ℝ (a continuous image of a connected space is an interval; an
unbounded interval is all of ℝ), so `PivotCompensatesJ` holds.  This is the
honest analytic discharge of the coverage residual — it replaces the opaque
solvability postulate with the standard connectedness + continuity + Archimedean
unboundedness inputs. -/

/-- **A continuous, two-sided-unbounded real function on a connected space is
surjective.**

If `X j₀` is preconnected, `V₀ : X j₀ → ℝ` is continuous, and its image is
unbounded above (`∀ t, ∃ a, t ≤ V₀ a`) and below (`∀ t, ∃ b, V₀ b ≤ t`), then
`V₀` is surjective.  Pure IVT: any target `t` lies between some `V₀ b ≤ t ≤ V₀ a`,
and connectedness forces the intermediate value to be attained. -/
theorem surjective_of_continuous_unbounded
    {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]
    (f : α → ℝ) (hcont : Continuous f)
    (habove : ∀ t : ℝ, ∃ a, t ≤ f a)
    (hbelow : ∀ t : ℝ, ∃ b, f b ≤ t) :
    Function.Surjective f := by
  intro t
  obtain ⟨a, ha⟩ := habove t
  obtain ⟨b, hb⟩ := hbelow t
  have hmem : t ∈ Set.range f :=
    intermediate_value_univ₂ hcont continuous_const hb ha
  exact hmem

/-- **Pivot coverage from connectedness + continuity + two-sided unboundedness
(the §IV.6 IVT discharge).**

`PivotCompensatesJ V₀ Vj` holds whenever the pivot coordinate type `X j₀` is
connected, the pivot utility `V₀` is continuous, and `V₀`'s image is unbounded
above and below.  Discharges the unified §IV.5/§IV.6 coverage residual through
the intermediate value theorem — the engine-A analytic route, now applied to the
coverage frontier shared by obligations 3, 5, and 16. -/
theorem pivotCompensatesJ_of_connected_continuous_unbounded
    [∀ i, TopologicalSpace (X i)]
    {j₀ j : ι} [PreconnectedSpace (X j₀)]
    (V₀ : X j₀ → ℝ) (Vj : X j → ℝ)
    (hcont : Continuous V₀)
    (habove : ∀ t : ℝ, ∃ a, t ≤ V₀ a)
    (hbelow : ∀ t : ℝ, ∃ b, V₀ b ≤ t) :
    PivotCompensatesJ V₀ Vj :=
  pivotCompensatesJ_of_surjective V₀ Vj
    (surjective_of_continuous_unbounded V₀ hcont habove hbelow)

end RawAxiomDischargersHexagon
end CertificateChecklist
end WakkerRoadmap

/-! ## Audit -/

#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.singleCoordIndiff_baseIndependent
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.updateIndiff_baseIndependent
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.jIndiff_iff_update
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.jIndiff_symm
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.jIndiff_refl
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.jIndiff_trans
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.utility_jIndiff_invariant
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.jIndiff_of_utility_eq
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.jIndiff_iff_utility_eq
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.grid_indiff_axis_of_diagonalStep
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.grid_indiff_of_eqSum_of_diagonalStep
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.grid_indiff_of_score_eq_of_diagonalStep
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.concreteGrid_indiff_of_eqSum
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.concreteGrid_indiff_of_score_eq
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.concreteDiagonalStep_iff
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.diagonalStep_referenceLayer_of_spaced
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.diagonalStep_referenceLayer_forall_n_of_spaced
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.concreteDiagonalStep_of_baseLayer_and_propagation
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.concreteDiagonalStep_of_spaced_and_propagation
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.diagonalLayerPropagation_of_sliceThomsenMove
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.concreteDiagonalStep_of_spaced_and_thomsen
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.concreteGrid_indiff_of_eqSum_of_spaced_and_thomsen
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.gridIndiff_iff_eqSum_of_rep
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.concreteDiagonalStep_of_rep
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.sliceThomsenMove_of_rep
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.sliceThomsenMove_of_kGridEqualSpacing
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.diagonalLayerPropagation_of_kGridEqualSpacing
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.standardThomsen_of_rep
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.kGridEqualSpacing_of_rep
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.twoPivotSliceTransport
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.pivotCompensatesJ_of_surjective
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.surjective_of_continuous_unbounded
#print axioms WakkerRoadmap.CertificateChecklist.RawAxiomDischargersHexagon.pivotCompensatesJ_of_connected_continuous_unbounded
