# Step-4 Tradeoff Family Discharge — Roadmap

**Scope.** This file scopes the discharge of the *last* `_from_raw_axioms` axiom in
the Wakker / Debreu–Koopmans mechanization:

```
axiom sharedPivotStep4TradeoffFamilyOnDataCertificate_from_raw_axioms
```

(`Classical Lottery/WakkerDebreuKoopmans/RawAxiomDischargers.lean:5034`).

Discharging it makes the canonical end-to-end route fully axiom-free
(foundation-only: `[propext, Classical.choice, Quot.sound]` + the accepted
topology bundle), i.e. it converts the conditional capstone
`additiveRep_nonempty_from_structural_axioms_reachAxiomFree` into an
**unconditional** construction once the residual frontier is also discharged.

> Status of the campaign at the time of writing: axioms 6, 16, 17, 19 discharged
> or restated; the two §IV.2.6 standard-sequence injectivity halves (12a/12b)
> discharged as theorems. **This is the single remaining `_from_raw_axioms`
> declaration.**

---

## ⚠ SUPERSEDING FINDING (this session) — the keystone is provably irreducible

While scoping Residual B, I discovered a **parallel, completed effort** — the
`OptionB_EqualSpacing*` file series (see `OptionB_ConsolidationSummary.md`) — that
has already executed *both links* of the §IV.5 grid construction (work packages
G1–G4 + Link A/B capstones, all `sorry`-free and audited) **and** localized the
genuine crux with **seven machine-checked impossibility/irreducibility findings**.

**The decisive result:** the keystone (Residual A — deriving the Thomsen /
`DoubleCancellation` condition, equivalently the per-slice grid representation)
is **machine-checked to be irreducible from Wakker's exact axiom set**
{coordinate independence A1 + restricted solvability + Archimedean + topology}.
Concretely `OptionB_C1aHexagonProbe` exhibits an `n=3` comonotone
Thomsen-violating model that satisfies A1 on *every* coordinate yet violates
`DoubleCancellation`. So:

* **Residual A keystone A1b is NOT provable** as I originally scoped it
  (`DoubleCancellation` from coordinate independence + a third coordinate alone).
  Link A (`doubleCancellation_of_blockIndependence_and_escapeJ2`) shows the third
  coordinate only *reduces* `DoubleCancellation` to the block condition
  `TBlockWeakIndependent` (≡ the Thomsen hexagon) — which is itself the
  irreducible, A1-non-derivable input.
* **Residual B is already done** (`OptionB_EqualSpacingSliceExtend`): the naive
  density extension is a proven **no-go** (§N.2 moving-target obstruction); the
  off-grid representation *is* the named order-calibration residual, produced from
  restricted solvability, not 2-D density.

**Consequence for this roadmap.** The "fully axiom-free *unconditional* route from
Wakker's exact axioms" is **not achievable** — it is machine-checked impossible,
not merely hard. The remaining `sharedPivotStep4TradeoffFamilyOnDataCertificate_from_raw_axioms`
axiom corresponds precisely to this irreducible content. The §2–§4 construction
plan below is **retained for historical context only**; its keystone A1b is now
known impossible from the bare axioms.

**Honest endpoints (the only two ways forward):**

1. **Named-input endpoint — ✅ DONE (this session).** The last axiom is now a
   **theorem** consuming `SharedPivotGridAdditiveRepresentationFamily` (via
   `sharedPivotStep4TradeoffFamilyOnDataCertificate_of_gridAdditiveRepresentationFamily`,
   `RawAxiomDischargers.lean:1699`). **Zero `_from_raw_axioms` axioms remain** in
   the tree (verified: `grep "^axiom .*_from_raw_axioms"` → no matches; full
   `ClassicalLotteryInAction` builds green). The restated theorem audits at
   `[propext, Classical.choice, Quot.sound]` + the two accepted §III.4.2 topology
   bracket-reach seams; the single irreducible content is now an explicit,
   proven-necessary hypothesis. The only remaining `axiom` declarations in the
   whole tree are those two topology bracket-reach seams
   (`coordinateOneStepBracket{Upper,Lower}Reach_of_wakkerCoordinateTopology`,
   part of the accepted topology base, eliminated separately in the
   reach-axiom-free target).
2. **Different axiom set** (separate research direction, scoped in
   `OptionB_AlternativeAxiomScoping.md`): difference/measurement structures
   (KLST Ch. 4), comonotone/CPT, or strengthened solvability — axiom sets where the
   cross-pair content is free. Each to be soundness-gated before construction.
   **← next.**

---

## 0. What the axiom payload reduces to

`SharedPivotStep4TradeoffFamilyOnDataCertificate P j₀ hdata` is, per non-pivot
slice `(j₀, k)`, a `PairwiseStep4TradeoffMachineryCertificate`
(`Certificates.lean:379`). Unfolded, that asks: from the (theorem-backed)
assembly input, produce a **grid-normalized** utility pair representing the whole
slice:

```
∃ Vⱼ₀ : X j₀ → ℝ, ∃ Vₖ : X k → ℝ,
  (∀ n, Vⱼ₀ (σⱼ₀.α n) = n) ∧ (∀ n, Vₖ (σₖ.α n) = n)        -- PairwiseGridNormalizationWitness
  ∧ (∀ x y, agreeOff {j₀,k} x y →                           -- PairwiseSliceRepresentationCertificate
       (P.weakPref x y ↔ Vⱼ₀(y j₀)+Vₖ(y k) ≤ Vⱼ₀(x j₀)+Vₖ(x k)))
```

`PairwiseOrderCalibrationCertificate` is *definitionally* this
`PairwiseSliceRepresentationCertificate` (`Certificates.lean:342`).

**Cleanest entry points (already theorem-backed):**

| Theorem | File:line | Produces from |
|---|---|---|
| `sharedPivotStep4TradeoffFamilyOnDataCertificate_of_representationFamily` | `RawAxiomDischargers.lean:1656` | per-slice grid-normalized slice rep |
| `sharedPivotStep4TradeoffFamilyOnDataCertificate_of_gridAdditiveRepresentationFamily` | `RawAxiomDischargers.lean:1699` | one common `V₀` for all slices |
| `pairwiseStep4TradeoffMachineryCertificate_of_gridNormalized_representation` | `RawAxiomDischargers.lean:1610` | a single slice's `(Vⱼ, Vₖ)` |

So the axiom is discharged by proving **`SharedPivotGridAdditiveRepresentationFamily`**
(`RawAxiomDischargers.lean:1681`) — equivalently, a per-slice grid-normalized
slice representation that glues to one pivot scale `V₀`.

---

## 1. Scaffolding already theorem-backed (do NOT rebuild)

Engine-C (`RawAxiomDischargersHexagon.lean`) already proves most of the discrete
grid algebra:

| Fact | File:line | Content |
|---|---|---|
| `concreteGrid_indiff_of_eqSum` | `Hexagon:463` | diagonal step ⟹ equal index-sum grid profiles indifferent |
| `concreteGrid_indiff_of_score_eq` | `Hexagon:478` | grid calibration modulo diagonal-step residual |
| `diagonalStep_referenceLayer_forall_n_of_spaced` | `Hexagon:554` | **m=0 base layer free from `σ.spaced`** |
| `concreteDiagonalStep_of_spaced_and_propagation` | `Hexagon:624` | diagonal step ⟸ base layer + `DiagonalLayerPropagation` |
| `diagonalLayerPropagation_of_kGridEqualSpacing` | `Hexagon:907` | propagation ⟸ `KGridEqualSpacing` |
| `GridAdditiveSliceRep` ⟺ `StandardThomsen`/`KGridEqualSpacing` | `Hexagon:759–960` | grid-rep ⟺ Thomsen / equal-spacing |
| `twoPivotSliceTransport` | `Hexagon:1010` | §IV.6 cross-pair transport (done) |
| `surjective_of_continuous_unbounded` | `Hexagon:1100` | IVT coverage discharge (done) |
| `sharedPivotGridAdditiveRepresentationFamily_of_step4Family_continuous_dense` | `RawAxiomDischargers.lean:7260` | forces per-slice pivot utilities to coincide via density+continuity |
| `sharedPivotGrid_global_agreement` | (engine-C/M5) | two continuous grid-normalized utilities agreeing on a dense grid are equal |

The construction therefore collapses to **two genuine residuals** + a (mostly
built) gluing step.

---

## 2. Residual A — discrete grid Thomsen / equal spacing

**Target:** `KGridEqualSpacing P base j₀ k σⱼ₀.α (σₖ k hk).α`
(`Hexagon:876`), which feeds `diagonalLayerPropagation_of_kGridEqualSpacing` →
`concreteDiagonalStep` → `GridAdditiveSliceRep`.

**Why it is the crux.** Engine-C notes correctly that `KGridEqualSpacing` /
`SliceThomsenMove` are **not** derivable from the single-coordinate
`TradeoffConsistency`. The classical resolution: for **n ≥ 3 essential
coordinates**, the Thomsen condition on a slice `{j₀,k}` follows from a **third
coordinate** `l ∉ {j₀,k}` together with coordinate independence
(Krantz–Luce–Suppes–Tversky Vol. 1, Ch. 6, Thm. 6.2; Wakker 1989 §IV.6). This is
the first essential use of `[Fact (3 ≤ Fintype.card ι)]` in the calibration core.

**The recognized residual.** `OptionB_CoordinateIndependence.lean` already names
the literature object: `WakkerInfra.ProductPref.DoubleCancellation P j₀ k` — the
additive-conjoint double-cancellation / Thomsen condition. Its own docstring
records that for `n = 2` it is extra and for `n ≥ 3` it is derivable from
coordinate independence via a third coordinate (KLST Vol. 1, Thm. 6.2).

> **SHARPENED FINDING (this session).** Working the index algebra shows the
> Thomsen condition **alone does not close `KGridEqualSpacing` in one step**. A
> single `DoubleCancellation` / `StandardThomsen` application cannot bridge the
> `k`-grid steps `(βm, β(m+1)) → (β(m+1), β(m+2))`, because the two
> standard-sequence grids `σⱼ₀.α` and `σₖ.α` are each built against *their own*
> auxiliary coordinates (`σⱼ₀.k`, `σₖ.k`), **not against each other**. Matching
> `DoubleCancellation`'s two equal-sum premises to the available layer-`m` /
> base-column grid indifferences forces a "double `k`-step" (k-indices differing
> by 2), which is not a known one-step fact; the same obstruction blocks
> `StandardThomsen` + base-column induction.
>
> **Consequence:** the genuine keystone content is **mutual calibration of the
> two grids** (Wakker §IV.5 affine renormalization) — constructing
> `ConcreteDiagonalStep` / `GridAdditiveSliceRep` directly — and it needs Thomsen
> **plus** the intrinsic spacing of *both* standard sequences (their `spaced`
> fields, on `σⱼ₀.k` and `σₖ.k`). Thomsen is necessary but not sufficient. This
> is why A1 is the multi-week core, not a one-shot lemma.

**Sub-lemmas:**

- **A1a. `standardThomsen_of_doubleCancellation`** (DONE, `RawAxiomDischargersThomsen.lean`).
  `DoubleCancellation P j₀ k` specializes directly to engine-C's grid Thomsen
  `StandardThomsen` on the concrete rectangle. Sound, foundation-only — the
  forward bridge tying the recognized residual to the grid machinery.

- **A1b. `doubleCancellation_of_coordinateIndependence_thirdCoordinate`** (NEW — keystone part 1).
  Derive `DoubleCancellation P j₀ k` from `CoordinateWeakSeparable` (the A1 / htop
  separability field, available) + a third coordinate `l` (`exists_third_coordinate`,
  DONE). Classical KLST 6.2 / Wakker §IV.6 n ≥ 3 argument.
  - **Effort: 1.5–3 weeks. Highest risk.** No Mathlib analogue.

- **A1c. `concreteDiagonalStep_of_doubleCancellation_and_bothSpacings`** (NEW — keystone part 2).
  Calibrate the two grids: combine `DoubleCancellation` (A1b) with the *intrinsic
  spacing of both* `σⱼ₀` and `σₖ` (their `spaced` fields) to construct the
  diagonal step / `GridAdditiveSliceRep`. This is the step the sharpened finding
  isolates as the missing content beyond Thomsen.
  - **Effort: 1–2 weeks.** Risk: aligning the two auxiliary-coordinate reference
    exchanges so the grids share a calibration unit.

- **A2. Chain to `GridAdditiveSliceRep`** (plumbing, PARTLY DONE).
  `KGridEqualSpacing → DiagonalLayerPropagation` (`Hexagon:907`) →
  `concreteDiagonalStep` (`Hexagon:624`, base layer from `Hexagon:554`) →
  build `S` and apply `gridIndiff_iff_eqSum_of_rep`. The
  `KGridEqualSpacing → ConcreteDiagonalStep → equal-sum indifference` portion is
  proven in `RawAxiomDischargersThomsen.lean`. Order/monotonicity part: see
  Residual B.
  - **Effort: 2–4 days remaining.**

### Lower-risk de-risking lemmas (DONE — `RawAxiomDischargersThomsen.lean`)

- **A0.b `exists_third_coordinate`** (DONE) — from `3 ≤ Fintype.card ι` and any
  `j₀, k`, exhibit `l ≠ j₀ ∧ l ≠ k` (pure `Fintype`/`Finset` cardinality).
- **A2 assembly** (DONE) — `concreteDiagonalStep_of_kGridEqualSpacing_and_referenceLayer`
  and `concreteGrid_indiff_of_eqSum_of_kGridEqualSpacing`: once the keystone
  supplies `KGridEqualSpacing`, the diagonal step + equal-sum indifference follow
  from existing engine-C lemmas.
- **A1a bridge** (DONE) — `standardThomsen_of_doubleCancellation` (above).

All audit foundation-only (`[propext, Classical.choice, Quot.sound]`); no
`sorryAx`, no `_from_raw_axioms`.

---

## 3. Residual B — off-grid extension (grid rep → full slice rep)

`GridAdditiveSliceRep` pins `S` only on grid points `g n m`. The Step-4 cert
needs `Vⱼ₀, Vₖ` defined and order-calibrated on **all** of `X j₀ × X k`.

- **B1. `sliceUtility_extend`** — extend `Vⱼ₀` from `{σⱼ₀.α n}` to all of
  `X j₀` via `RestrictedSolvability` (bracket each `x` between consecutive grid
  points) + `Archimedean` (grid is cofinal, no point infinitely far) +
  continuity (topology bundle) for uniqueness.
  - Mathlib: `ConditionallyCompleteLattice`/`sSup`, `IsLUB`,
    `intermediate_value_univ₂`, `Continuous.ext_on`, `DenseRange`.
  - **Effort: 1–2 weeks.**

- **B2. `pairwiseSliceRepresentation_of_gridRep_and_extension`** — lift grid
  additivity to the full biconditional on the slice using monotonicity of the
  extension + density. Essentially a 1-D continuous monotone representation
  argument per coordinate, glued by grid additivity.
  - Mathlib: `Monotone`, `StrictMono`, `OrderIso`, `DenseRange`.
  - **Effort: 1–2 weeks.**

---

## 4. Gluing to the common `V₀`

- **C1.** Feed B1's per-slice continuous, grid-normalized `Vⱼ₀` to
  `sharedPivotGrid_global_agreement` to merge all per-slice pivot utilities into
  one `V₀`, yielding `SharedPivotGridAdditiveRepresentationFamily`. Then
  `sharedPivotStep4TradeoffFamilyOnDataCertificate_of_gridAdditiveRepresentationFamily`
  (`RawAxiomDischargers.lean:1699`) discharges the axiom.
  - The existing
    `sharedPivotGridAdditiveRepresentationFamily_of_step4Family_continuous_dense`
    (`:7260`) does the round-trip version; prefer merging the per-slice
    continuous `Vⱼ₀` directly to avoid a mild circularity.
  - **Effort: 2–4 days wiring.**

---

## 5. Recommended build order

1. **A0 de-risking lemmas** (this session) — `RawAxiomDischargersThomsen.lean`:
   base-layer packaging, third-coordinate existence, base-independence transfer.
2. **A1** keystone — `kGridEqualSpacing_of_thirdCoordinate`.
3. **A2** chain to `GridAdditiveSliceRep`.
4. **B1 / B2** off-grid extension.
5. **C1** glue to common `V₀`, discharge the axiom, rebuild `ClassicalLotteryInAction`,
   confirm `grep` shows no `^axiom .*_from_raw_axioms`.

---

## 6. Effort & risk summary

- Total: **~6–10 weeks** focused proof work (repo's 3–6 week estimate assumed
  more reuse than exists for Residual A).
- Highest-risk piece: **A1** (`kGridEqualSpacing_of_thirdCoordinate`) — the genuine
  conjoint-measurement content, no Mathlib analogue.
- Mathlib supplies the analysis layer (IVT, density/continuity uniqueness,
  conditionally-complete-order interpolation); the order-theoretic conjoint core
  is bespoke.
- **No new axioms** anywhere: every sub-lemma is provable from the structural
  axioms + topology bundle, so the end-to-end route stays foundation-only.

---

## 7. Pinned references (Lean source)

- Axiom: `WakkerDebreuKoopmans/RawAxiomDischargers.lean:5034`.
- Family def `SharedPivotStep4TradeoffFamilyOnDataCertificate`: `:1625`.
- Per-slice `PairwiseStep4TradeoffMachineryCertificate`: `Certificates.lean:379`.
- `PairwiseSliceRepresentationCertificate`: `Certificates.lean:83`;
  `PairwiseGridNormalizationWitness`: `Certificates.lean:214`.
- Engine-C grid algebra: `RawAxiomDischargersHexagon.lean` §8–§16
  (`concreteGrid` `:445`; `KGridEqualSpacing` `:876`; `StandardThomsen` `:925`;
  `GridAdditiveSliceRep` `:759`; `twoPivotSliceTransport` `:1010`).
- Common-`V₀` gluing: `RawAxiomDischargers.lean:7260`.
- Literature: Krantz–Luce–Suppes–Tversky, *Foundations of Measurement* Vol. 1,
  Ch. 6; Wakker, *Additive Representations of Preferences* (1989), Ch. IV.
