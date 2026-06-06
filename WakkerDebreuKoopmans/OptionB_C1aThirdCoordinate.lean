/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — WP-C1.a: the third-coordinate (Debreu) derivation of double cancellation

This file executes the **forward construction** half of WP-C1.a, following the
probe verdict (`OptionB_C1aHexagonProbe.lean`): single-coordinate independence A1
does **not** imply the hexagon, so the derivation must use the **third
coordinate** (Debreu 1960 / KLST 1971 Thm 6.2) — the `n ≥ 3` measuring-stick
argument.

## The classical argument (worked out, then mechanized)

Fix distinct coordinates `j, k, t`, a background `a`, and write `[u | v | c]` for
the profile equal to `a` off `{j,k,t}` with `j ↦ u`, `k ↦ v`, `t ↦ c`
(here `c := a t`).  `DoubleCancellation P j k` asks: from
* **P1** `[x | q | c] ∼ [y | p | c]`  and
* **P2** `[y | r | c] ∼ [z | q | c]`,
conclude `[x | r | c] ∼ [z | p | c]`.

Debreu's third-coordinate route introduces a *transfer level* `w : X t` and uses:
* **J2** `[x | r | w] ∼ [y | r | c]` — a `{j,t}`-compensation moving `j:x→y`
  against `t:w→c` (its size is fixed by P1: under a rep, `V_j y − V_j x =
  V_k q − V_k p`, and the transfer chooses `w` with `V_t w − V_t c` equal to that
  common difference);
* **Kz** `[z | q | c] ∼ [z | p | w]` — the matching `{k,t}`-compensation moving
  `k:q→p` against `t:c→w`;
* **strip** the indifference `[x | r | w] ∼ [z | p | w]` (at the common
  transfer level `w`) transports down to `[x | r | c] ∼ [z | p | c]` (a
  block move on `t`).

Chaining J2 ∼ P2 ∼ Kz gives `[x | r | w] ∼ [z | p | w]`; the strip closes the
goal.  The genuine §IV.5/solvability content is *existence of the transfer level
`w` and the strip* — which the probe's finite countermodel lacks (its `Fin 3`
coordinates are not solvable).

## What this file delivers (all machine-checked)

* `ThirdCoordinateTransfer P j k t` — the named transfer residual (J2, Kz, strip
  bundled per Thomsen datum).
* `doubleCancellation_of_thirdCoordinateTransfer` — the **sound reduction**: DC
  from the transfer, by pure weak-order transitivity.  *(This is the honest
  forward step: it turns the hexagon into the Debreu transfer, exactly as the
  paper argument does.)*
* `thirdCoordinateTransfer_of_additiveRep` — **necessity**: every additive
  representation supplies the transfer (so the residual is sound — assuming it
  hides nothing false), via `V_t`-surjectivity-free explicit witness when the
  rep's `V_t` hits the required level.  We state the version that takes the
  transfer level as given by the representation's coverage.

The remaining genuine residual is the **existence of the transfer level `w`** from
restricted solvability + connectedness (the continuum the probe countermodel
lacks) — the §IV.2.7/§IV.5 standard-sequence/solvability content.  This file
reduces the hexagon to exactly that, soundly.

This file imports `OptionB_CoordinateIndependence` (for the score helpers and
`DoubleCancellation`) and is **not** in the umbrella import.
-/

import WakkerDebreuKoopmans.OptionB_CoordinateIndependence
import WakkerDebreuKoopmans.RawAxiomDischargersIVT

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

/-- Profile with `j ↦ u`, `k ↦ v`, `t ↦ c` over background `a`. -/
def tri (a : Profile X) (j k t : ι) (u : X j) (v : X k) (c : X t) :
    Profile X :=
  Function.update (Function.update (Function.update a j u) k v) t c

/-- **Third-coordinate transfer residual (the Debreu measuring-stick datum).**

For the Thomsen datum `(a; x,y,z; p,q,r)` on the pair `{j,k}` with third
coordinate `t`, the existence of a transfer level `w : X t` realizing:

* **J2** `[x|r|w] ∼ [y|r|c]`,
* **Kz** `[z|q|c] ∼ [z|p|w]`, and
* **strip** `[x|r|w] ∼ [z|p|w] → [x|r|c] ∼ [z|p|c]`

where `c = a t`.  This is the genuine cross-block content the hexagon needs
beyond single-coordinate independence (the probe `OptionB_C1aHexagonProbe`
proved A1 alone does not give it). -/
def ThirdCoordinateTransfer (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (x y z : X j) (p q r : X k),
    P.indiff (tri a j k t x q (a t)) (tri a j k t y p (a t)) →
    P.indiff (tri a j k t y r (a t)) (tri a j k t z q (a t)) →
    ∃ w : X t,
      P.indiff (tri a j k t x r w) (tri a j k t y r (a t)) ∧
      P.indiff (tri a j k t z q (a t)) (tri a j k t z p w) ∧
      (P.indiff (tri a j k t x r w) (tri a j k t z p w) →
        P.indiff (tri a j k t x r (a t)) (tri a j k t z p (a t)))

/-- `tri` with `t ↦ a t` is the plain `{j,k}`-update (the `t`-coordinate is
unchanged from the background). -/
private lemma tri_at_base (a : Profile X) {j k t : ι} (hjt : j ≠ t) (hkt : k ≠ t)
    (u : X j) (v : X k) :
    tri a j k t u v (a t) =
      Function.update (Function.update a j u) k v := by
  unfold tri
  rw [Function.update_eq_self_iff.mpr]
  · rw [Function.update_of_ne (Ne.symm hkt), Function.update_of_ne (Ne.symm hjt)]

/-- **WP-C1.a sound reduction: `DoubleCancellation` from the third-coordinate
transfer.**

Pure weak-order transitivity: the transfer supplies `w` with J2, Kz, and the
strip; chaining J2 ∼ P2 ∼ Kz yields `[x|r|w] ∼ [z|p|w]`, and the strip closes the
goal.  Audit `[propext, Classical.choice, Quot.sound]`.

This is the honest Debreu forward step: it turns the hexagon into the transfer
residual, exactly as the monograph argument does.  The `tri … (a t)` profiles are
definitionally the `DoubleCancellation` profiles (the third coordinate is the
background value), bridged by `tri_at_base`. -/
theorem doubleCancellation_of_thirdCoordinateTransfer
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjt : j ≠ t) (hkt : k ≠ t)
    (htrans : ThirdCoordinateTransfer P j k t) :
    DoubleCancellation P j k := by
  intro a x y z p q r h1 h2
  -- Recast the DC premises/goal in `tri … (a t)` form.
  have e : ∀ (u : X j) (v : X k),
      Function.update (Function.update a j u) k v = tri a j k t u v (a t) :=
    fun u v => (tri_at_base a hjt hkt u v).symm
  rw [e, e] at h1 h2 ⊢
  -- Pull the transfer witness.
  obtain ⟨w, hJ2, hKz, hStrip⟩ := htrans a x y z p q r h1 h2
  -- Chain: [x|r|w] ∼ [y|r|c] ∼(P2) [z|q|c] ∼ [z|p|w].
  have hchain1 : P.indiff (tri a j k t x r w) (tri a j k t z q (a t)) :=
    ⟨ProductPref.IsWeakOrder.transitive _ _ _ hJ2.1 h2.1,
     ProductPref.IsWeakOrder.transitive _ _ _ h2.2 hJ2.2⟩
  have hchain2 : P.indiff (tri a j k t x r w) (tri a j k t z p w) :=
    ⟨ProductPref.IsWeakOrder.transitive _ _ _ hchain1.1 hKz.1,
     ProductPref.IsWeakOrder.transitive _ _ _ hKz.2 hchain1.2⟩
  exact hStrip hchain2

/-! ## Necessity of the transfer residual (soundness witness)

Every additive representation supplies the transfer, *given* that its
`t`-coordinate utility hits the level forced by P1.  We package the level
existence as a hypothesis (`htlevel`) — that is exactly the
`V_t`-surjectivity / solvability content the probe showed is not free; the rest
(J2, Kz, strip as scored equalities) is mechanical. -/

/-- **Necessity of the third-coordinate transfer (given the rep's level
coverage).**

Under an additive representation `R`, if the `t`-utility realizes the level
`R.V t (a t) + (R.V j y − R.V j x)` (the size P1 forces), then the transfer holds:
J2, Kz, and the strip are all scored equalities.  This proves the transfer
residual is a genuine consequence of having a representation whose `V t` is rich
enough — i.e. it hides nothing false; the level-coverage hypothesis `htlevel` is
the honest solvability residual. -/
theorem thirdCoordinateTransfer_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (htlevel : ∀ (a : Profile X) (x y : X j),
      ∃ w : X t, R.V t w = R.V t (a t) + (R.V j y - R.V j x)) :
    ThirdCoordinateTransfer P j k t := by
  intro a x y z p q r h1 h2
  -- P1 under the rep forces  V_j y − V_j x = V_k q − V_k p.
  have hkj : k ≠ j := Ne.symm hjk
  have htj : t ≠ j := Ne.symm hjt
  have htk : t ≠ k := Ne.symm hkt
  -- Score of a tri profile.
  have score_tri : ∀ (u : X j) (v : X k) (c : X t),
      (∑ i, R.V i (tri a j k t u v c i))
        = R.V j u + R.V k v + R.V t c
          + ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
    intro u v c
    unfold tri
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (show k ∈ Finset.univ.erase j from
          Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩),
        ← Finset.add_sum_erase _ _ (show t ∈ (Finset.univ.erase j).erase k from
          Finset.mem_erase.mpr ⟨htk, Finset.mem_erase.mpr ⟨htj, Finset.mem_univ t⟩⟩)]
    have hj : (Function.update (Function.update (Function.update a j u) k v) t c) j = u := by
      rw [Function.update_of_ne hjt, Function.update_of_ne hjk, Function.update_self]
    have hk : (Function.update (Function.update (Function.update a j u) k v) t c) k = v := by
      rw [Function.update_of_ne hkt, Function.update_self]
    have ht : (Function.update (Function.update (Function.update a j u) k v) t c) t = c := by
      rw [Function.update_self]
    rw [hj, hk, ht]
    have hrest : (∑ i ∈ ((Finset.univ.erase j).erase k).erase t,
          R.V i (Function.update (Function.update (Function.update a j u) k v) t c i))
        = ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hit : i ≠ t := Finset.ne_of_mem_erase hi
      have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      have hij : i ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij]
    rw [hrest]; ring
  -- Decode P1 into a utility equation.
  have hP1 : R.V j x + R.V k q = R.V j y + R.V k p := by
    have := (indiff_iff_score R).mp h1
    rw [score_tri, score_tri] at this
    linarith
  -- Choose the transfer level w.
  obtain ⟨w, hw⟩ := htlevel a x y
  refine ⟨w, ?_, ?_, ?_⟩
  · -- J2: [x|r|w] ∼ [y|r|c].   V_j x + V_t w = V_j y + V_t c.
    rw [indiff_iff_score R, score_tri, score_tri]
    rw [hw]; ring
  · -- Kz: [z|q|c] ∼ [z|p|w].   V_k q + V_t c = V_k p + V_t w.
    rw [indiff_iff_score R, score_tri, score_tri]
    rw [hw]; linarith
  · -- strip: scored indifference is level-independent in t.
    intro hstrip
    rw [indiff_iff_score R, score_tri, score_tri]
    have := (indiff_iff_score R).mp hstrip
    rw [score_tri, score_tri] at this
    linarith

/-! ## §D.  WP-C1.a forward step 2 — transfer-level existence

The transfer residual `ThirdCoordinateTransfer` decomposes into three pieces.
This section discharges the **transfer-level existence** by the WP-T IVT engine
plus two precisely-named sub-residuals, and proves both sub-residuals necessary
(so each hides nothing false).

* **J2 crossing** — a `t`-coordinate IVT crossing
  (`RawAxiomDischargersIVT.coordinate_slice_IVT_of_preferenceContinuous`)
  producing `w` with `[x|r|w] ∼ [y|r|c]`, from a `t`-bracket (connectedness +
  preference continuity + a reach pair).  Pure WP-T machinery.
* **`KzTransfer`** — the genuine §IV.5 *tradeoff-transfer* residual: at the
  J2-supplied `w`, the `{k,t}`-compensation follows from the `{j,t}`-compensation
  plus P1.  Under a rep this is the additive identity; it is **not** free from
  single-coordinate A1 (cross-pair content).  Necessity proved below.
* **`StripTransfer`** — the `t`-block independence strip (next forward step).

Honest determination: transfer-level existence = (WP-T IVT, free) + the `{k,t}`
tradeoff-transfer residual + the strip, with the two residuals proved necessary. -/

/-- **`{k,t}` tradeoff-transfer residual at a transfer level.**

At a transfer level `w`, the `{k,t}`-compensation `[z|q|c] ∼ [z|p|w]` follows from
the `{j,t}`-compensation `[x|r|w] ∼ [y|r|c]` (J2) plus P1.  Cross-pair §IV.5
content (not free from A1). -/
def KzTransfer (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (x y z : X j) (p q r : X k) (w : X t),
    P.indiff (tri a j k t x q (a t)) (tri a j k t y p (a t)) →   -- P1
    P.indiff (tri a j k t x r w) (tri a j k t y r (a t)) →       -- J2 at w
    P.indiff (tri a j k t z q (a t)) (tri a j k t z p w)         -- Kz at w

/-- **`t`-block strip residual.**  A `{j,k}`-difference indifference at the common
transfer level `w` transports to the background level `a t`. -/
def StripTransfer (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (x z : X j) (p r : X k) (w : X t),
    P.indiff (tri a j k t x r w) (tri a j k t z p w) →
    P.indiff (tri a j k t x r (a t)) (tri a j k t z p (a t))

/-- **Transfer-level existence ⟹ the transfer residual.**

Assembles `ThirdCoordinateTransfer` from a J2-witness supplier, the `{k,t}`
tradeoff-transfer residual, and the strip residual.  Audit foundational-only. -/
theorem thirdCoordinateTransfer_of_components
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hJ2 : ∀ (a : Profile X) (x y : X j) (r : X k),
      ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t)))
    (hKz : KzTransfer P j k t)
    (hStrip : StripTransfer P j k t) :
    ThirdCoordinateTransfer P j k t := by
  intro a x y z p q r h1 h2
  obtain ⟨w, hw⟩ := hJ2 a x y r
  exact ⟨w, hw, hKz a x y z p q r w h1 hw, fun hs => hStrip a x z p r w hs⟩

/-- **J2 crossing from the WP-T IVT engine.**

The `{j,t}`-compensation level `w` exists, given: connectedness of `X t`,
preference continuity (closed contour sets at the reference `[y|r|c]`), and a
`t`-coordinate reach pair (`cHi` with `[x|r|cHi] ≽ [y|r|c]`, `cLo` with `[y|r|c] ≽
[x|r|cLo]`).  Pure WP-T machinery: the slice map
`w ↦ tri a j k t x r w = update (tri a j k t x r (a t)) t w` feeds
`coordinate_slice_IVT_of_preferenceContinuous` with base `tri a j k t x r (a t)`,
coordinate `t`, reference `[y|r|c]`. -/
theorem thirdCoordinateTransfer_J2_of_IVT
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P]
    {j k t : ι}
    [ConnectedSpace (X t)]
    (a : Profile X) (x y : X j) (r : X k)
    (hUpper : IsClosed {z : Profile X | P.weakPref z (tri a j k t y r (a t))})
    (hLower : IsClosed {z : Profile X | P.weakPref (tri a j k t y r (a t)) z})
    (cHi cLo : X t)
    (hHi : P.weakPref (tri a j k t x r cHi) (tri a j k t y r (a t)))
    (hLo : P.weakPref (tri a j k t y r (a t)) (tri a j k t x r cLo)) :
    ∃ w : X t, P.indiff (tri a j k t x r w) (tri a j k t y r (a t)) := by
  classical
  set b : Profile X := tri a j k t y r (a t) with hb
  set base : Profile X := tri a j k t x r (a t) with hbase
  -- The slice map at coordinate t over `base` is `w ↦ tri a j k t x r w`.
  have hslice : ∀ w : X t, Function.update base t w = tri a j k t x r w := by
    intro w; rw [hbase]; unfold tri; rw [Function.update_idem]
  -- Recast the reach witnesses through the slice map.
  have hHi' : P.weakPref (Function.update base t cHi) b := by rw [hslice]; exact hHi
  have hLo' : P.weakPref b (Function.update base t cLo) := by rw [hslice]; exact hLo
  obtain ⟨w, hw⟩ :=
    WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.coordinate_slice_IVT_of_preferenceContinuous
      P base t b hUpper hLower hHi' hLo'
  refine ⟨w, ?_⟩
  rw [hslice] at hw; exact hw

/-- **Necessity of `KzTransfer`.**  Under an additive representation, P1 forces
`V_j y − V_j x = V_k q − V_k p`, and J2 at `w` forces `V_t w − V_t c =
V_j y − V_j x`; together they give Kz at `w`.  So `KzTransfer` holds for any
preference with a representation — it hides nothing false. -/
theorem kzTransfer_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    KzTransfer P j k t := by
  intro a x y z p q r w hP1 hJ2
  have hkj : k ≠ j := Ne.symm hjk
  have htj : t ≠ j := Ne.symm hjt
  have htk : t ≠ k := Ne.symm hkt
  have score_tri : ∀ (u : X j) (v : X k) (c : X t),
      (∑ i, R.V i (tri a j k t u v c i))
        = R.V j u + R.V k v + R.V t c
          + ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
    intro u v c
    unfold tri
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (show k ∈ Finset.univ.erase j from
          Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩),
        ← Finset.add_sum_erase _ _ (show t ∈ (Finset.univ.erase j).erase k from
          Finset.mem_erase.mpr ⟨htk, Finset.mem_erase.mpr ⟨htj, Finset.mem_univ t⟩⟩)]
    have hj : (Function.update (Function.update (Function.update a j u) k v) t c) j = u := by
      rw [Function.update_of_ne hjt, Function.update_of_ne hjk, Function.update_self]
    have hk : (Function.update (Function.update (Function.update a j u) k v) t c) k = v := by
      rw [Function.update_of_ne hkt, Function.update_self]
    have ht : (Function.update (Function.update (Function.update a j u) k v) t c) t = c := by
      rw [Function.update_self]
    rw [hj, hk, ht]
    have hrest : (∑ i ∈ ((Finset.univ.erase j).erase k).erase t,
          R.V i (Function.update (Function.update (Function.update a j u) k v) t c i))
        = ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hit : i ≠ t := Finset.ne_of_mem_erase hi
      have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      have hij : i ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij]
    rw [hrest]; ring
  have e1 := (indiff_iff_score R).mp hP1
  have e2 := (indiff_iff_score R).mp hJ2
  rw [score_tri, score_tri] at e1 e2
  rw [indiff_iff_score R, score_tri, score_tri]
  linarith

/-- **Necessity of `StripTransfer`.**  Under an additive representation, the
scored indifference at level `w` differs from the one at level `a t` only by the
common `V_t w − V_t (a t)` term, which cancels.  So `StripTransfer` holds for any
preference with a representation. -/
theorem stripTransfer_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    StripTransfer P j k t := by
  intro a x z p r w hstrip
  have hkj : k ≠ j := Ne.symm hjk
  have htj : t ≠ j := Ne.symm hjt
  have htk : t ≠ k := Ne.symm hkt
  have score_tri : ∀ (u : X j) (v : X k) (c : X t),
      (∑ i, R.V i (tri a j k t u v c i))
        = R.V j u + R.V k v + R.V t c
          + ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
    intro u v c
    unfold tri
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase _ _ (show k ∈ Finset.univ.erase j from
          Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩),
        ← Finset.add_sum_erase _ _ (show t ∈ (Finset.univ.erase j).erase k from
          Finset.mem_erase.mpr ⟨htk, Finset.mem_erase.mpr ⟨htj, Finset.mem_univ t⟩⟩)]
    have hj : (Function.update (Function.update (Function.update a j u) k v) t c) j = u := by
      rw [Function.update_of_ne hjt, Function.update_of_ne hjk, Function.update_self]
    have hk : (Function.update (Function.update (Function.update a j u) k v) t c) k = v := by
      rw [Function.update_of_ne hkt, Function.update_self]
    have ht : (Function.update (Function.update (Function.update a j u) k v) t c) t = c := by
      rw [Function.update_self]
    rw [hj, hk, ht]
    have hrest : (∑ i ∈ ((Finset.univ.erase j).erase k).erase t,
          R.V i (Function.update (Function.update (Function.update a j u) k v) t c i))
        = ∑ i ∈ ((Finset.univ.erase j).erase k).erase t, R.V i (a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hit : i ≠ t := Finset.ne_of_mem_erase hi
      have hik : i ≠ k := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
      have hij : i ≠ j := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
      rw [Function.update_of_ne hit, Function.update_of_ne hik, Function.update_of_ne hij]
    rw [hrest]; ring
  have e := (indiff_iff_score R).mp hstrip
  rw [score_tri, score_tri] at e
  rw [indiff_iff_score R, score_tri, score_tri]
  linarith

end ProductPref
end WakkerInfra

/-! ## WP-C1.a forward-construction audit -/

#print axioms WakkerInfra.ProductPref.doubleCancellation_of_thirdCoordinateTransfer
#print axioms WakkerInfra.ProductPref.thirdCoordinateTransfer_of_additiveRep
#print axioms WakkerInfra.ProductPref.thirdCoordinateTransfer_of_components
#print axioms WakkerInfra.ProductPref.thirdCoordinateTransfer_J2_of_IVT
#print axioms WakkerInfra.ProductPref.kzTransfer_of_additiveRep
#print axioms WakkerInfra.ProductPref.stripTransfer_of_additiveRep
