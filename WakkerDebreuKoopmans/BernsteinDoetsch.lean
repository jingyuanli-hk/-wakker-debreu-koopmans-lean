/-
This file is part of the split `WakkerDebreuKoopmans` module family.
The public import surface remains `WakkerDebreuKoopmans.lean`.

# Bernstein–Doetsch / Sierpiński upgrade theorem

A midpoint-concave function continuous on a convex subset of `ℝ` is
concave.  This file discharges the Phase-8 named residue
`MidpointAndContinuityToConcavityResidual` (closing both slices
simultaneously), and thereby reduces the Phase-8 C4 / C5 closure
surfaces in `M2Frontier.lean` from "named residue" to "fully theorem-
backed" up to the Wakker-IV.2 structural inputs.

## Proof outline

1. **Combining step** (`combo_step`).  Given midpoint-concavity and the
   concavity inequality at two parameters `a, b ∈ [0,1]`, derive the
   concavity inequality at their average `(a+b)/2`.
2. **Dyadic concavity** (`dyadic_concave`).  By induction on the dyadic
   denominator, the concavity inequality holds at every dyadic-rational
   convex parameter `k / 2^n` with `0 ≤ k ≤ 2^n`.
3. **Density + closedness** (`concaveOn_of_continuousOn_of_midpoint`).
   For arbitrary `b ∈ [0,1]`, the dyadic sequence `⌊b·2^n⌋ / 2^n`
   converges to `b`.  Continuity of `V` along the affine path
   `t ↦ (1-t)·x + t·y` (which stays in `s` by convexity) lets the dyadic
   inequality pass to the limit.

The headline `theorem midpointAndContinuityToConcavityResidual_holds`
delivers the named residue from the Phase-8 Certificate ladder
unconditionally (i.e. with no Sierpiński/Bernstein–Doetsch hypothesis on
the input side).
-/

import WakkerDebreuKoopmans.Certificates
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.Floor.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace WakkerRoadmap

open Set Filter Topology

namespace BernsteinDoetsch

/-- **Combining step.**  Given midpoint-concavity of `f` on a convex set
`s`, plus the concavity inequality at two parameters `a, b ∈ [0,1]`, the
concavity inequality holds at their average `(a+b)/2`. -/
private lemma combo_step {s : Set ℝ} {f : ℝ → ℝ} (hs : Convex ℝ s)
    (hmid : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → (f u + f v) / 2 ≤ f ((u + v) / 2))
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s)
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hA : (1 - a) * f x + a * f y ≤ f ((1 - a) * x + a * y))
    (hB : (1 - b) * f x + b * f y ≤ f ((1 - b) * x + b * y)) :
    (1 - (a + b) / 2) * f x + ((a + b) / 2) * f y ≤
      f ((1 - (a + b) / 2) * x + ((a + b) / 2) * y) := by
  have hP : (1 - a) * x + a * y ∈ s :=
    hs hx hy (by linarith) ha0 (by ring)
  have hQ : (1 - b) * x + b * y ∈ s :=
    hs hx hy (by linarith) hb0 (by ring)
  have hM := hmid hP hQ
  have heq_x :
      ((1 - a) * x + a * y + ((1 - b) * x + b * y)) / 2 =
        (1 - (a + b) / 2) * x + ((a + b) / 2) * y := by ring
  have heq_y :
      ((1 - a) * f x + a * f y + ((1 - b) * f x + b * f y)) / 2 =
        (1 - (a + b) / 2) * f x + ((a + b) / 2) * f y := by ring
  calc (1 - (a + b) / 2) * f x + ((a + b) / 2) * f y
      = ((1 - a) * f x + a * f y + ((1 - b) * f x + b * f y)) / 2 := heq_y.symm
    _ ≤ (f ((1 - a) * x + a * y) + f ((1 - b) * x + b * y)) / 2 := by linarith
    _ ≤ f ((((1 - a) * x + a * y) + ((1 - b) * x + b * y)) / 2) := hM
    _ = f ((1 - (a + b) / 2) * x + ((a + b) / 2) * y) := by rw [heq_x]

/-- **Dyadic concavity.**  Midpoint-concavity extends, by induction on
the dyadic denominator, to every dyadic-rational convex parameter
`k / 2^n` with `0 ≤ k ≤ 2^n`. -/
private lemma dyadic_concave {s : Set ℝ} {f : ℝ → ℝ} (hs : Convex ℝ s)
    (hmid : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → (f u + f v) / 2 ≤ f ((u + v) / 2))
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    ∀ n k : ℕ, k ≤ 2 ^ n →
      (1 - (k : ℝ) / (2 : ℝ) ^ n) * f x + ((k : ℝ) / (2 : ℝ) ^ n) * f y ≤
        f ((1 - (k : ℝ) / (2 : ℝ) ^ n) * x + ((k : ℝ) / (2 : ℝ) ^ n) * y) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hk' : k ≤ 1 := by simpa using hk
    interval_cases k
    · simp
    · simp
  | succ n ih =>
    intro k hk
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have h2succ : ((2 : ℝ) ^ (n + 1)) = 2 * (2 : ℝ) ^ n := by ring
    have hpow_nat : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by
      rw [pow_succ]; ring
    rcases Nat.even_or_odd k with hE | hO
    · -- k = m + m (even case)
      obtain ⟨m, rfl⟩ := hE
      have hm : m ≤ 2 ^ n := by omega
      have htk : ((m + m : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) =
          (m : ℝ) / (2 : ℝ) ^ n := by
        rw [h2succ]
        push_cast
        field_simp
        ring
      rw [htk]
      exact ih m hm
    · -- k = 2 * m + 1 (odd case)
      obtain ⟨m, rfl⟩ := hO
      have hm1 : m + 1 ≤ 2 ^ n := by omega
      have hm : m ≤ 2 ^ n := Nat.le_of_succ_le hm1
      -- Set u := m / 2^n, v := (m+1) / 2^n; both in [0,1]
      set u : ℝ := (m : ℝ) / (2 : ℝ) ^ n with hu_def
      set v : ℝ := ((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n with hv_def
      have hu_nn : 0 ≤ u := by rw [hu_def]; positivity
      have hu_le : u ≤ 1 := by
        rw [hu_def, div_le_one h2pos]; exact_mod_cast hm
      have hv_nn : 0 ≤ v := by rw [hv_def]; positivity
      have hv_le : v ≤ 1 := by
        rw [hv_def, div_le_one h2pos]; exact_mod_cast hm1
      -- (u + v) / 2 = (2m + 1) / 2^(n+1)
      have huv_avg :
          (u + v) / 2 = ((2 * m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) := by
        rw [hu_def, hv_def, h2succ]
        push_cast
        field_simp
        ring
      rw [← huv_avg]
      exact combo_step hs hmid hx hy hu_nn hu_le hv_nn hv_le
        (by simpa [hu_def] using ih m hm)
        (by simpa [hv_def] using ih (m + 1) hm1)

/-- **Bernstein–Doetsch / Sierpiński upgrade theorem.**

A midpoint-concave function `f` continuous on a convex subset `s ⊆ ℝ`
is concave on `s`.  The proof is the classical density-plus-closedness
argument:

* By `dyadic_concave`, the concavity inequality holds at every dyadic
  rational in `[0,1]`.
* For arbitrary `b ∈ [0,1]`, the dyadic sequence
  `bn n := ⌊b · 2^n⌋ / 2^n` converges to `b`.
* Continuity of `f` along the affine path
  `t ↦ (1-t)·x + t·y` (which stays in `s` by convexity) lets the
  inequality pass to the limit.
-/
theorem concaveOn_of_continuousOn_of_midpoint
    {s : Set ℝ} (hs : Convex ℝ s) {f : ℝ → ℝ} (hcont : ContinuousOn f s)
    (hmid : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s →
      (f u + f v) / 2 ≤ f ((u + v) / 2)) :
    ConcaveOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Reduce to a = 1 - b
  have hb1 : b ≤ 1 := by linarith
  obtain rfl : a = 1 - b := by linarith
  -- Translate the smul-form goal to plain multiplication
  show (1 - b) * f x + b * f y ≤ f ((1 - b) * x + b * y)
  -- Dyadic approximating sequence
  set bn : ℕ → ℝ := fun n => (⌊b * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n with hbn_def
  -- Pointwise bounds on bn
  have hbn_nn : ∀ n, 0 ≤ bn n := fun n => by
    rw [hbn_def]; positivity
  have hbn_le : ∀ n, bn n ≤ b := by
    intro n
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    rw [hbn_def, div_le_iff₀ h2pos]
    exact Nat.floor_le (by positivity)
  have hbn_le1 : ∀ n, bn n ≤ 1 := fun n => le_trans (hbn_le n) hb1
  have hbn_floor_le : ∀ n, ⌊b * (2 : ℝ) ^ n⌋₊ ≤ 2 ^ n := by
    intro n
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hbound : (b * (2 : ℝ) ^ n) ≤ (2 : ℝ) ^ n := by
      have := mul_le_mul_of_nonneg_right hb1 h2pos.le
      linarith
    have hfloor : (⌊b * (2 : ℝ) ^ n⌋₊ : ℝ) ≤ (2 : ℝ) ^ n :=
      le_trans (Nat.floor_le (by positivity)) hbound
    have hcast : ((⌊b * (2 : ℝ) ^ n⌋₊ : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
      simpa using hfloor
    exact_mod_cast hcast
  -- Each bn n satisfies the concavity inequality (dyadic step)
  have hbn_concave : ∀ n,
      (1 - bn n) * f x + bn n * f y ≤
        f ((1 - bn n) * x + bn n * y) := by
    intro n
    have := dyadic_concave hs hmid hx hy n (⌊b * (2 : ℝ) ^ n⌋₊) (hbn_floor_le n)
    simpa [hbn_def] using this
  -- bn → b
  have hbn_tendsto : Tendsto bn atTop (𝓝 b) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- 1/2^n → 0
    have htend_pow : Tendsto (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
      have hgeom : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have heq : (fun n : ℕ => ((1 : ℝ) / 2) ^ n) =
          (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ n) := by
        funext n; rw [div_pow, one_pow]
      rw [heq] at hgeom
      exact hgeom
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 : ℝ) / (2 : ℝ) ^ N < ε := by
      have := (htend_pow.eventually (gt_mem_nhds hε)).exists
      simpa using this
    refine ⟨N, fun n hn => ?_⟩
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have h2Npos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have hlt : b * (2 : ℝ) ^ n < (⌊b * (2 : ℝ) ^ n⌋₊ : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one (b * (2 : ℝ) ^ n)
    have hge : (⌊b * (2 : ℝ) ^ n⌋₊ : ℝ) ≤ b * (2 : ℝ) ^ n :=
      Nat.floor_le (by positivity)
    -- 0 ≤ b - bn n and b - bn n < 1 / 2^n
    have hdiff_nn : 0 ≤ b - bn n := by linarith [hbn_le n]
    have hdiff_lt : b - bn n < 1 / (2 : ℝ) ^ n := by
      rw [hbn_def]
      have heq : b - (⌊b * (2 : ℝ) ^ n⌋₊ : ℝ) / (2 : ℝ) ^ n =
          (b * (2 : ℝ) ^ n - (⌊b * (2 : ℝ) ^ n⌋₊ : ℝ)) / (2 : ℝ) ^ n := by
        field_simp
      rw [heq, div_lt_iff₀ h2pos]
      have : (1 : ℝ) / (2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by
        field_simp
      rw [this]
      linarith
    -- |bn n - b| = b - bn n (since b ≥ bn n)
    have hdist_eq : dist (bn n) b = b - bn n := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hdiff_nn]
    -- 1/2^n ≤ 1/2^N
    have hpow_mono : (1 : ℝ) / (2 : ℝ) ^ n ≤ 1 / (2 : ℝ) ^ N := by
      apply one_div_le_one_div_of_le h2Npos
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    linarith
  -- Affine path γ(t) = (1-t)*x + t*y
  let γ : ℝ → ℝ := fun t => (1 - t) * x + t * y
  have hγ_cont : Continuous γ := by
    show Continuous (fun t : ℝ => (1 - t) * x + t * y)
    fun_prop
  have hγ_mem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ s := by
    intro t ⟨ht0, ht1⟩
    show (1 - t) * x + t * y ∈ s
    exact hs hx hy (by linarith) ht0 (by ring)
  have hγ_b_mem : γ b ∈ s := hγ_mem b ⟨hb, hb1⟩
  have hγ_bn_mem : ∀ n, γ (bn n) ∈ s := fun n =>
    hγ_mem (bn n) ⟨hbn_nn n, hbn_le1 n⟩
  -- γ ∘ bn → γ b
  have hγ_bn_tendsto : Tendsto (fun n => γ (bn n)) atTop (𝓝 (γ b)) :=
    (hγ_cont.tendsto _).comp hbn_tendsto
  -- f ∘ γ ∘ bn → f (γ b) using ContinuousWithinAt
  have hf_γ_b_within : ContinuousWithinAt f s (γ b) := hcont _ hγ_b_mem
  have hγ_bn_within : Tendsto (fun n => γ (bn n)) atTop (𝓝[s] (γ b)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hγ_bn_tendsto, Eventually.of_forall hγ_bn_mem⟩
  have hf_tendsto : Tendsto (fun n => f (γ (bn n))) atTop (𝓝 (f (γ b))) :=
    hf_γ_b_within.tendsto.comp hγ_bn_within
  -- LHS tendsto
  have hL_cont : Continuous (fun t : ℝ => (1 - t) * f x + t * f y) := by fun_prop
  have hL_tendsto : Tendsto (fun n => (1 - bn n) * f x + bn n * f y) atTop
      (𝓝 ((1 - b) * f x + b * f y)) :=
    (hL_cont.tendsto _).comp hbn_tendsto
  -- Pass to the limit
  have hgoal :
      Tendsto (fun n => f ((1 - bn n) * x + bn n * y)) atTop
        (𝓝 (f ((1 - b) * x + b * y))) := by
    have : (fun n => f ((1 - bn n) * x + bn n * y)) =
        (fun n => f (γ (bn n))) := by
      funext n; show _ = f (γ (bn n)); rfl
    rw [this]
    have hγ_b_eq : f (γ b) = f ((1 - b) * x + b * y) := by show f _ = f _; rfl
    rw [← hγ_b_eq]
    exact hf_tendsto
  exact le_of_tendsto_of_tendsto' hL_tendsto hgoal hbn_concave

end BernsteinDoetsch

/-! ## Discharge of `MidpointAndContinuityToConcavityResidual`

The classical Bernstein–Doetsch theorem `concaveOn_of_continuousOn_of_midpoint`
delivers the named Phase-8 residue directly: continuity plus midpoint
concavity on each slice gives joint concavity on each slice. -/

/-- **The Sierpiński / Bernstein–Doetsch residue is theorem-backed.**

This discharges `MidpointAndContinuityToConcavityResidual` for both
slices simultaneously, closing the C4 + C5 Phase-8 frontier surfaces
from `M2Frontier.lean` up to the structural Wakker-IV.2 inputs. -/
theorem CertificateChecklist.midpointAndContinuityToConcavityResidual_holds
    (S₁ S₂ : Set ℝ) (V₁ V₂ : ℝ → ℝ) :
    CertificateChecklist.MidpointAndContinuityToConcavityResidual S₁ S₂ V₁ V₂ := by
  intro hS₁ hS₂ hCont hMid
  obtain ⟨hC₁, hC₂⟩ := hCont
  obtain ⟨hM₁, hM₂⟩ := hMid
  refine ⟨?_, ?_⟩
  · exact BernsteinDoetsch.concaveOn_of_continuousOn_of_midpoint hS₁ hC₁ hM₁
  · exact BernsteinDoetsch.concaveOn_of_continuousOn_of_midpoint hS₂ hC₂ hM₂

end WakkerRoadmap
