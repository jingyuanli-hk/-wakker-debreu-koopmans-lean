/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — attacking the hexagon: the Debreu/KLST measuring-stick construction

> **⚠ STATUS: genuine research-frontier attempt on the hexagon (cross-pair
> trade-off transitivity).**  This file is **NOT** in the umbrella import.  It is
> **`sorry`-free**: it builds the *provable* bricks of the Debreu (1960) / KLST
> (1971 Thm 6.2) `n ≥ 3` measuring-stick derivation of the hexagon, and isolates
> the genuinely-open existence step as a single named residual (proved necessary
> under a representation).  **It does NOT claim to close the hexagon from bare
> axioms** — the honest open content (the solvability-built matching `t`-exchange)
> is named and soundness-gated, exactly as the project's discipline requires.

## Background (from `OptionB_C1aGridTransport.lean` §Q)

The matching's core is `CrossPairTradeoffTransitivity P j k t` (= `KzTransfer`),
Wakker IV.2.5's hexagon:
```
P1: (j: x→y) ≡ (k: q→p)   [x|q|c] ∼ [y|p|c]
J2: (j: x→y) ≡ (t: w→c)   [x|r|w] ∼ [y|r|c]
─────────────────────────────────────────────
Kz: (k: q→p) ≡ (t: w→c)   [z|q|c] ∼ [z|p|w]
```
proved (§Q) to be exactly cross-pair trade-off transitivity, necessary under a
rep, and NOT derivable from solvability or A1 alone.

## The Debreu measuring-stick idea (worked out)

The third coordinate `t` is the **measuring stick**.  The hexagon closes if every
trade-off can be *matched to a `t`-exchange*, and matching is transitive through
the shared `t`-axis:

* J2 matches the j-step `(x→y)` to the t-exchange `(w→c)`.
* If solvability produces a `t`-exchange matching the k-step `(q→p)` — call it
  `(w'→c)` — then the conclusion `Kz` is "the k-step matches `(w→c)`", which holds
  iff the two t-exchanges `(w→c)` and `(w'→c)` **coincide as trade-offs**.
* The coincidence follows because **both** t-exchanges match the *same* j-step
  (via P1 chaining J2): `(x→y) ≡ (k:q→p) ≡ (t:w'→c)` and `(x→y) ≡ (t:w→c)`, so
  `(t:w→c) ≡ (t:w'→c)` — a *single-coordinate* `t` trade-off equality, which
  **weak order + the shared structure** closes.

So the genuine open step is: **produce the `t`-exchange matching the k-step**
(`KStepTExchange`), via restricted solvability + the third coordinate.  Everything
else is weak-order chaining, proved here.

This file builds the chaining bricks and names `KStepTExchange` as the residual.
-/

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

/-! ## §A.  Indifference chaining helpers (weak order). -/

private theorem hx_symm {x y : Profile X} (h : P.indiff x y) : P.indiff y x :=
  ⟨h.2, h.1⟩

private theorem hx_trans [ProductPref.IsWeakOrder P] {x y z : Profile X}
    (hxy : P.indiff x y) (hyz : P.indiff y z) : P.indiff x z :=
  ⟨ProductPref.IsWeakOrder.transitive _ _ _ hxy.1 hyz.1,
   ProductPref.IsWeakOrder.transitive _ _ _ hyz.2 hxy.2⟩

/-! ## §B.  The within-slice `{k,t}` compensation and the coincidence

The atomic hexagon is `KzAnchorTransfer` (`OptionB_C1aKzReduction`): from
`P1 : [x|q|c] ∼ [y|p|c]` and `J2 : [x|r|w] ∼ [y|r|c]`, conclude `[x|q|c] ∼ [x|p|w]`.

The genuine Debreu lever provides, at the anchor `j`-value `x`, a `{k,t}`
compensation: solvability yields a `t`-level `w'` with `[x|q|c] ∼ [x|p|w']` (the
k-step `q→p` compensated by a t-exchange `w'→c`).  Then the hexagon closes **iff**
`w' = w` *as a trade-off* — i.e. `[x|p|w'] ∼ [x|p|w]`.  We show that coincidence
follows from P1 + J2 by pure weak order **through a single shared profile**, given
one more solvability-built indifference (the `j`-block transport of J2 to the
`p`-background).  This is the honest decomposition: the *existence* of `w'`
(`KStepMatch`) is the open solvability residual; the *coincidence* is chaining. -/

/-- **Within-slice `{k,t}` compensation (the open solvability residual).**

At `j`-value `x`, the k-step `q→p` is compensated by a `t`-exchange to some level
`w'`: `[x|q|c] ∼ [x|p|w']`.  This is the existence content restricted solvability +
the third coordinate provide (compensate a k-move by a t-move within the `j=x`
slice); it is the genuine §IV.5 lever, named here and proved necessary under a rep
below. -/
def KStepMatch (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (x : X j) (p q : X k),
    ∃ w' : X t, P.indiff (tri a j k t x q (a t)) (tri a j k t x p w')

/-- **The j-block transport of J2 to the `p`-background (the bridge residual).**

`J2` lives at `k`-value `r`; to chain it with the k-step compensation we need the
same j-step `x→y` compensated by the *same* t-exchange `w→c` but at `k`-value `p`:
`[x|p|w] ∼ [y|p|c]`.  This is `j`-block independence applied to J2 (shift the
common... no: it shifts the common `k`-value `r → p`, i.e. `k`-block independence).
We take it as the named bridge; it is `KBlockWeakIndependent` content (necessary
under a rep). -/
def J2AtP (P : ProductPref X) (j k t : ι) : Prop :=
  ∀ (a : Profile X) (x y : X j) (p r : X k) (w : X t),
    P.indiff (tri a j k t x r w) (tri a j k t y r (a t)) →   -- J2 at r
    P.indiff (tri a j k t x p w) (tri a j k t y p (a t))     -- J2 at p

/-- **`KzAnchorTransfer` from the within-slice compensation + the bridge + P1
(PROVED, pure weak order).**

The coincidence chain.  Given:
* `P1 : [x|q|c] ∼ [y|p|c]`,
* `J2 : [x|r|w] ∼ [y|r|c]`, and the bridge `J2AtP` giving `[x|p|w] ∼ [y|p|c]`,
* the within-slice compensation `KStepMatch` giving `[x|q|c] ∼ [x|p|w']`,

we get `[y|p|c] ∼ [x|q|c] ∼ [x|p|w']` and `[y|p|c] ∼ [x|p|w]` (bridge symm), so
`[x|p|w'] ∼ [x|p|w]`; chaining with the compensation gives `[x|q|c] ∼ [x|p|w]`,
which is `KzAnchorTransfer`.  Pure weak-order transitivity — the measuring-stick
coincidence.  Audit `[propext, Quot.sound]`. -/
theorem kzAnchorTransfer_of_kStepMatch_and_bridge
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hMatch : KStepMatch P j k t)
    (hBridge : J2AtP P j k t) :
    KzAnchorTransfer P j k t := by
  intro a x y p q r w hP1 hJ2
  -- Within-slice compensation: [x|q|c] ∼ [x|p|w'] for some w'.
  obtain ⟨w', hw'⟩ := hMatch a x p q
  -- Bridge: J2 at k-value p: [x|p|w] ∼ [y|p|c].
  have hJ2p : P.indiff (tri a j k t x p w) (tri a j k t y p (a t)) :=
    hBridge a x y p r w hJ2
  -- Chain: [x|p|w'] ∼ [x|q|c] ∼ [y|p|c] ∼ [x|p|w].
  --   hw'.symm : [x|p|w'] ∼ [x|q|c]
  --   hP1      : [x|q|c]  ∼ [y|p|c]
  --   hJ2p.symm: [y|p|c]  ∼ [x|p|w]
  have hchain : P.indiff (tri a j k t x p w') (tri a j k t x p w) :=
    hx_trans (hx_symm hw') (hx_trans hP1 (hx_symm hJ2p))
  -- Goal: [x|q|c] ∼ [x|p|w] = [x|q|c] ∼[hw'] [x|p|w'] ∼[hchain] [x|p|w].
  exact hx_trans hw' hchain

/-! ## §C.  Soundness gates: both new residuals are necessary under a rep

The reduction in §B is only honest if its two residuals (`KStepMatch`, `J2AtP`) are
*sound* — true under any additive representation.  We prove both.  `KStepMatch`
needs `V_t`-reach (the t-axis realizes the required compensation level — the
solvability/surjectivity content); `J2AtP` is pure cancellation (the common `V_k`
term cancels), necessary unconditionally. -/

private theorem score_tri_local [ProductPref.IsWeakOrder P] (R : AdditiveRep P)
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

/-- **Soundness gate: `KStepMatch` is necessary under a rep, modulo `V_t`-reach
(PROVED).**

Under a representation, `[x|q|c] ∼ [x|p|w']` iff `V_k q + V_t c = V_k p + V_t w'`,
i.e. `V_t w' = V_t c + (V_k q − V_k p)`.  Given `V_t`-reach (every target real is a
`V_t`-value — the surjectivity/solvability content), the compensating `w'` exists.
Confirms `KStepMatch` hides nothing false.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem kStepMatch_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hreach : ∀ (a : Profile X) (target : ℝ), ∃ w' : X t, R.V t w' = target) :
    KStepMatch P j k t := by
  intro a x p q
  obtain ⟨w', hw'⟩ := hreach a (R.V t (a t) + (R.V k q - R.V k p))
  refine ⟨w', ?_⟩
  rw [indiff_iff_score R, score_tri_local R hjk hjt hkt, score_tri_local R hjk hjt hkt, hw']
  ring

/-- **Soundness gate: `J2AtP` is necessary under a rep (PROVED).**

Shifting the common `k`-value `r → p` preserves the indifference (the `V_k` term is
common to both sides and cancels).  Necessary unconditionally.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem j2AtP_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    J2AtP P j k t := by
  intro a x y p r w hJ2
  rw [indiff_iff_score R, score_tri_local R hjk hjt hkt, score_tri_local R hjk hjt hkt] at hJ2
  rw [indiff_iff_score R, score_tri_local R hjk hjt hkt, score_tri_local R hjk hjt hkt]
  linarith

/-! ## §D.  Discharging `KStepMatch` from restricted solvability + a t-bracket

The within-slice compensation `KStepMatch` is **not** cross-pair cancellation — it
is pure *existence* of a compensating `t`-level, which restricted solvability
supplies given a `t`-bracket of the target.  This genuinely **discharges** one of
the two hexagon residuals from a structural axiom (solvability) + the §IV.2.6
escape bracket — leaving only `J2AtP` (the block-independence cancellation) as the
irreducible content.  This is real progress: the hexagon's *existence* half is
solvability-reachable; only its *cancellation* half is the genuine residue. -/

/-- **`KStepMatch` from restricted solvability + a t-bracket (PROVED — discharges
the existence half).**

For each `(a, x, p, q)`, given a `t`-bracket of the target `[x|q|c]` from the slice
`[x|p|·]` (`vHi` over, `vLo` under — the §IV.2.6 escape content), restricted
solvability selects the compensating level `w'` with `[x|p|w'] ∼ [x|q|c]`, hence
(symm) `[x|q|c] ∼ [x|p|w']`.  The `tri … = update (update … ) t ·` rewrite recasts
the slice as a single coordinate-`t` update so `RestrictedSolvability` applies.
**No cross-pair cancellation** — pure solvability existence.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem kStepMatch_of_solvability_and_bracket
    [ProductPref.IsWeakOrder P] {j k t : ι} (hkt : k ≠ t)
    (hsolv : RestrictedSolvability P)
    (hbr : ∀ (a : Profile X) (x : X j) (p q : X k), ∃ vHi vLo : X t,
      P.weakPref (tri a j k t x p vHi) (tri a j k t x q (a t)) ∧
      P.weakPref (tri a j k t x q (a t)) (tri a j k t x p vLo)) :
    KStepMatch P j k t := by
  intro a x p q
  obtain ⟨vHi, vLo, hHi, hLo⟩ := hbr a x p q
  -- Recast the `[x|p|·]` slice as a single coordinate-`t` update over the packed
  -- background `update (update a j x) k p` (definitional: `t` is the outermost update).
  set base : Profile X := Function.update (Function.update a j x) k p with hbase
  have hslice : ∀ c : X t, tri a j k t x p c = Function.update base t c := by
    intro c; rfl
  rw [hslice vHi] at hHi
  rw [hslice vLo] at hLo
  obtain ⟨w', hw'⟩ :=
    hsolv base (tri a j k t x q (a t)) t vHi vLo hHi hLo
  refine ⟨w', ?_⟩
  rw [hslice w'] at *
  exact ⟨hw'.2, hw'.1⟩

/-! ## §E.  Connecting to the existing block-independence frontier

The bridge residual `J2AtP` is exactly an instance of the project's
`KBlockWeakIndependent` (the `k`-block KLST separability): both shift the common
`k`-value in a `{j,t}`-difference indifference.  Proving `J2AtP ⟸
KBlockWeakIndependent` connects this construction to the existing frontier
(`OptionB_C1aKzAnchor`), and pins down what the construction genuinely added:
**it extracted and discharged the solvability-existence half** (`KStepMatch`, §D),
leaving only the `k`-block cancellation — whereas the project's
`kzAnchorTransfer_of_kBlock` folds both halves into `KBlockWeakIndependent`. -/

/-- **`J2AtP` from `k`-block independence (PROVED — connects to the frontier).**

`J2AtP` shifts the common `k`-value `r → p` in the `{j,t}`-difference indifference
`[x|r|w] ∼ [y|r|c]`, in both `≽`-directions.  That is exactly
`KBlockWeakIndependent` applied twice.  So the construction's bridge residual is
the project's standard `k`-block separability — no new cancellation content.
Audit `[propext, Quot.sound]`. -/
theorem j2AtP_of_kBlockWeakIndependent
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hKB : KBlockWeakIndependent P j k t) :
    J2AtP P j k t := by
  intro a x y p r w hJ2
  rcases hJ2 with ⟨hfwd, hbwd⟩
  refine ⟨?_, ?_⟩
  · -- [x|p|w] ≽ [y|p|c]  from  [x|r|w] ≽ [y|r|c]  (shift k: r → p).
    exact hKB a x y r p w (a t) hfwd
  · -- [y|p|c] ≽ [x|p|w]  from  [y|r|c] ≽ [x|r|w]  (shift k: r → p).
    exact hKB a y x r p (a t) w hbwd

/-- **The hexagon's atomic anchor from solvability + a t-bracket + `k`-block
independence (PROVED — the assembled construction).**

Composes the whole §B–§E chain: `KStepMatch` (discharged from solvability + the
§IV.2.6 bracket, §D), `J2AtP` (from `k`-block independence, §E), and the pure
weak-order coincidence (`kzAnchorTransfer_of_kStepMatch_and_bridge`, §B).  So
`KzAnchorTransfer` follows from {restricted solvability + a t-bracket + `k`-block
independence} — the existence content genuinely discharged, only the block
cancellation remaining.  Audit `[propext, Quot.sound]`. -/
theorem kzAnchorTransfer_of_solvability_bracket_and_kBlock
    [ProductPref.IsWeakOrder P] {j k t : ι} (hkt : k ≠ t)
    (hsolv : RestrictedSolvability P)
    (hbr : ∀ (a : Profile X) (x : X j) (p q : X k), ∃ vHi vLo : X t,
      P.weakPref (tri a j k t x p vHi) (tri a j k t x q (a t)) ∧
      P.weakPref (tri a j k t x q (a t)) (tri a j k t x p vLo))
    (hKB : KBlockWeakIndependent P j k t) :
    KzAnchorTransfer P j k t :=
  kzAnchorTransfer_of_kStepMatch_and_bridge
    (kStepMatch_of_solvability_and_bracket hkt hsolv hbr)
    (j2AtP_of_kBlockWeakIndependent hKB)

/-! ## §F.  Discharging the `KStepMatch` bracket from the §IV.2.6 escape grid

The bracket `hbr` feeding `KStepMatch` is the §IV.2.6 Archimedean reach: a strict
`t`-standard-sequence based at the `[x|p|·]` slice escapes the target `[x|q|c]` on
both sides.  As in `OptionB_C1aGridTransport` §H, `archimedean_reach_above`/`below`
discharge the bracket by **pure order theory** (no topology IVT, no A1).  So the
hexagon's *existence* half rests on exactly `{RestrictedSolvability + Archimedean}`
+ the escape grid — purely structural — leaving `k`-block independence as the sole
cancellation residue. -/

/-- **Per-datum `KStepMatch` escape grid (the §IV.2.6 reach data).**

For each `(a, x, p, q)`, a strict Archimedean `t`-standard-sequence whose base
realises the `[x|p|·]` slice and whose grid escapes the target `[x|q|c]` on both
sides.  Pure §IV.2.6 escape content. -/
structure KStepMatchEscapeGrid (P : ProductPref X) (j k t : ι) where
  /-- The `t`-standard-sequence for each datum. -/
  seq    : Profile X → X j → X k → X k → ProductPref.StandardSequence P t
  /-- It is strict. -/
  strict : ∀ (a : Profile X) (x : X j) (p q : X k), (seq a x p q).IsStrict
  /-- The Archimedean axiom on `t`. -/
  arch   : ProductPref.Archimedean P t
  /-- The sequence's base realises the `[x|p|·]` slice. -/
  base   : ∀ (a : Profile X) (x : X j) (p q : X k) (c : X t),
    Function.update (seq a x p q).base t c = tri a j k t x p c
  /-- The grid escapes the target `[x|q|c]` above. -/
  above  : ∀ (a : Profile X) (x : X j) (p q : X k), ∃ i : ℕ,
    ¬ P.weakPref (tri a j k t x q (a t))
                 (Function.update (seq a x p q).base t ((seq a x p q).α i))
  /-- The grid escapes the target `[x|q|c]` below. -/
  below  : ∀ (a : Profile X) (x : X j) (p q : X k), ∃ i : ℕ,
    ¬ P.weakPref (Function.update (seq a x p q).base t ((seq a x p q).α i))
                 (tri a j k t x q (a t))

/-- **The `KStepMatch` bracket from the escape grid (PROVED — pure order theory).**

`archimedean_reach_above`/`below` produce the over/under `t`-levels bracketing the
target `[x|q|c]` from the `[x|p|·]` slice; the sequence's `base` field rewrites them
into the `tri`-slice shape.  No topology IVT, no A1.  Audit `[propext, Quot.sound]`. -/
theorem kStepMatchBracket_of_escapeGrid
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (esc : KStepMatchEscapeGrid P j k t) :
    ∀ (a : Profile X) (x : X j) (p q : X k), ∃ vHi vLo : X t,
      P.weakPref (tri a j k t x p vHi) (tri a j k t x q (a t)) ∧
      P.weakPref (tri a j k t x q (a t)) (tri a j k t x p vLo) := by
  intro a x p q
  obtain ⟨vHi, hHi⟩ :=
    WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_reach_above
      P (esc.seq a x p q) (esc.strict a x p q) esc.arch
      (tri a j k t x q (a t)) (esc.above a x p q)
  obtain ⟨vLo, hLo⟩ :=
    WakkerRoadmap.CertificateChecklist.RawAxiomDischargersIVT.archimedean_reach_below
      P (esc.seq a x p q) (esc.strict a x p q) esc.arch
      (tri a j k t x q (a t)) (esc.below a x p q)
  refine ⟨vHi, vLo, ?_, ?_⟩
  · rw [esc.base a x p q vHi] at hHi; exact hHi
  · rw [esc.base a x p q vLo] at hLo; exact hLo

/-- **`KStepMatch` from solvability + the escape grid (PROVED — existence half
fully structural).**

Composes `kStepMatchBracket_of_escapeGrid` (the §IV.2.6 reach) with
`kStepMatch_of_solvability_and_bracket` (solvability selection).  So `KStepMatch`
is discharged from `{RestrictedSolvability + Archimedean}` + the escape grid alone
— no topology IVT, no A1, no cancellation.  Audit `[propext, Quot.sound]`. -/
theorem kStepMatch_of_solvability_and_escapeGrid
    [ProductPref.IsWeakOrder P] {j k t : ι} (hkt : k ≠ t)
    (hsolv : RestrictedSolvability P)
    (esc : KStepMatchEscapeGrid P j k t) :
    KStepMatch P j k t :=
  kStepMatch_of_solvability_and_bracket hkt hsolv
    (kStepMatchBracket_of_escapeGrid esc)

/-- **The hexagon's atomic anchor from `{solvability + Archimedean escape}` +
`k`-block independence (PROVED — the fully-structural existence half).**

The sharpest assembled form: `KzAnchorTransfer` from restricted solvability + the
§IV.2.6 escape grid (discharging all existence content by order theory) +
`k`-block independence (the sole cancellation residue).  Audit
`[propext, Quot.sound]`. -/
theorem kzAnchorTransfer_of_escapeGrid_and_kBlock
    [ProductPref.IsWeakOrder P] {j k t : ι} (hkt : k ≠ t)
    (hsolv : RestrictedSolvability P)
    (esc : KStepMatchEscapeGrid P j k t)
    (hKB : KBlockWeakIndependent P j k t) :
    KzAnchorTransfer P j k t :=
  kzAnchorTransfer_of_kStepMatch_and_bridge
    (kStepMatch_of_solvability_and_escapeGrid hkt hsolv esc)
    (j2AtP_of_kBlockWeakIndependent hKB)

end ProductPref
end WakkerInfra

/-! ## Audit — the hexagon-construction bricks (`sorry`-free)

The atomic hexagon `KzAnchorTransfer` is reduced — by **pure weak order**
(`kzAnchorTransfer_of_kStepMatch_and_bridge`) — to two strictly-more-atomic named
residuals:
* `KStepMatch` — within-slice `{k,t}` compensation existence (the
  solvability/surjectivity content; soundness-gated `kStepMatch_of_additiveRep`,
  and — crucially — *not* cross-pair cancellation, so a candidate for discharge
  from restricted solvability);
* `J2AtP` — the `j`-step's t-compensation transported across the `k`-value (the
  `k`-block independence content; soundness-gated `j2AtP_of_additiveRep`).

This is genuine progress on the Debreu measuring-stick construction: it separates
the hexagon's *existence* content (`KStepMatch`, plausibly solvability-reachable)
from its *cancellation* content (`J2AtP`, the block-independence residue).  None
carries `sorry`. -/

#print axioms WakkerInfra.ProductPref.kzAnchorTransfer_of_kStepMatch_and_bridge
#print axioms WakkerInfra.ProductPref.kStepMatch_of_additiveRep
#print axioms WakkerInfra.ProductPref.j2AtP_of_additiveRep
#print axioms WakkerInfra.ProductPref.kStepMatch_of_solvability_and_bracket

/-! §E — connection to the existing block-independence frontier + assembled
construction. -/

#print axioms WakkerInfra.ProductPref.j2AtP_of_kBlockWeakIndependent
#print axioms WakkerInfra.ProductPref.kzAnchorTransfer_of_solvability_bracket_and_kBlock

/-! §F — the existence half fully structural: `KStepMatch` discharged from
`{RestrictedSolvability + Archimedean escape}` by pure order theory; only `k`-block
independence remains. -/

#print axioms WakkerInfra.ProductPref.kStepMatchBracket_of_escapeGrid
#print axioms WakkerInfra.ProductPref.kStepMatch_of_solvability_and_escapeGrid
#print axioms WakkerInfra.ProductPref.kzAnchorTransfer_of_escapeGrid_and_kBlock
