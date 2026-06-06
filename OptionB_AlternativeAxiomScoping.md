# Option B — scoping a different axiom set for the unconditional theorem

**Purpose.** The C1.a crux (the cross-pair Thomsen content) is machine-checked
irreducible from Wakker's *exact* axiom set `{IsWeakOrder, RestrictedSolvability,
Essential, Archimedean, WakkerCoordinateTopology}` — seven findings, three global
sessions (`OptionB_ConsolidationSummary` §3). The unconditional theorem
`Nonempty (AdditiveRep P)` from the structural axioms is therefore unreachable *in that
axiom set* without the multi-month §IV.5 standard-sequence construction.

This document scopes whether a **different** structural axiom set makes the crux free —
i.e. whether some alternative primitive/axiom *soundly* discharges
`KBlockWeakIndependent` (the hexagon) without trivially assuming the conclusion. It is
analysis + a probe protocol; no forward Lean is written until a candidate passes the
soundness gates.

> **The discipline (mandatory, the one that produced the seven findings).** For each
> candidate axiom `Ax`:
> 1. **State** `Ax` precisely in the repo's vocabulary.
> 2. **Soundness gate:** prove `Ax_of_additiveRep` — `Ax` is *necessary* under any
>    additive representation. If it is not (the model can have a rep yet violate `Ax`),
>    `Ax` is unsound as a structural axiom — discard.
> 3. **Triviality check:** does `Ax` (with the existing axioms) make the crux free —
>    AND is `Ax` genuinely *weaker* than "assume the hexagon"? If `Ax` is inter-derivable
>    with `KBlockWeakIndependent`/the hexagon, it is the §6 fallback in disguise — record
>    as such, no progress.
> 4. **Non-triviality check (the real bar):** does `Ax` hold in a model that the bare
>    structural axioms do NOT force the hexagon on? If `Ax` *adds* genuine structure
>    (not just renames the conclusion), it is a real alternative.
> Only a candidate passing (2) sound, (3) free, (4) non-trivial is worth a forward
> construction.

---

## 0. The precise bar (why most candidates fail (3)/(4))

By the permutation equivalence (`OptionB_C1aDiagonalEquivalence`) and
`kzTransfer_iff_crossPairTradeoffTransitivity` (`OptionB_C1aGridTransport` §Q), the crux
**is** cross-pair trade-off transitivity. Any axiom that *implies* the hexagon must
supply cross-pair content; any axiom *necessary under a rep* that supplies it is, by the
representation, equivalent to the hexagon on the represented cone. So the danger is
universal: **a sound axiom strong enough to give the crux tends to be the crux**. The
genuine alternatives are exactly those that add structure *outside* the `weakPref`
relation (a new primitive) or that change what "represented" means.

---

## 1. Candidate A — primitive preference-difference (KLST Ch. 4 / Wakker tradeoff)

**The idea.** Add a *primitive quaternary* relation `≽*` on pairs:
`(a, b) ≽* (c, d)` read "the preference difference from `b` to `a` is at least that from
`d` to `c`". KLST Ch. 4 builds the additive representation from `≽*`'s own axioms
(weak order on pairs, monotonicity, a Thomsen-like *solvability* on differences, and an
Archimedean axiom on differences). Cross-pair tradeoff transitivity is then an axiom of
`≽*` (its transitivity), not a derived condition on `weakPref`.

**State.** `DifferenceStructure P` = a relation `diffPref : (Profile X × Profile X) →
(Profile X × Profile X) → Prop` with: weak order, the *linking* axiom
`(a,b) ≽* (b,a)`-style reversal, monotone consistency with `weakPref`
(`a ≽ b ↔ (a,b) ≽* (b,b)`), difference-solvability, difference-Archimedean.

**Soundness gate (gate 2).** `differenceStructure_of_additiveRep`: under a rep
`R`, set `(a,b) ≽* (c,d) := ∑V a − ∑V b ≥ ∑V c − ∑V d`. All the `≽*` axioms hold (it is a
real difference comparison). **Necessary ⇒ sound.** ✓ (expected to pass — this is the
honest content.)

**Triviality / non-triviality (gates 3,4).** *This is the crux of the candidate.* The
`≽*` transitivity gives cross-pair transitivity **on the represented difference scale**.
The genuine question: does `DifferenceStructure P` (its axioms) hold in a model where the
bare structural axioms do *not* force the hexagon? 
* **If `≽*` is DEFINED from `weakPref`** (the only data available): then
  `(a,b) ≽* (c,d)` must be expressed via `weakPref`, and its transitivity becomes a
  `weakPref` condition — which is exactly `CrossPairTradeoffTransitivity`, the crux.
  **Fails (3): inter-derivable with the hexagon — the §6 fallback renamed.** ✗
* **If `≽*` is a GENUINELY NEW primitive** (extra data beyond `weakPref`): then
  `DifferenceStructure` adds structure, and KLST Ch. 4 derives the representation from it.
  **This passes (4) — but it changes the theorem:** the input is now "a preference
  *plus* a primitive difference relation satisfying the KLST difference axioms", not
  "a preference satisfying Wakker's axioms". That is a *different, weaker* theorem
  (more is assumed). **Honest verdict: a real alternative, but it assumes the cardinal
  difference structure the original theorem is supposed to *construct*.**

**Determination for Candidate A.** Sound (gate 2 ✓). Either trivial (if `≽*` is
`weakPref`-definable — the crux renamed) or non-trivial-but-assumes-more (if `≽*` is a
new primitive — the cardinal scale is now an input, not an output). **Not a free lunch:**
it relocates the cross-pair content into the primitive. Worth mechanizing *only* as an
explicitly-weaker companion theorem ("additive rep from a preference-difference
structure"), clearly distinguished from Wakker IV.2.7. **Recommended: defer; document as
the honest cardinal-input variant.**

---

## 2. Candidate B — comonotone / CPT structure (`Comonotonic.lean`)

**The idea.** Use the repo's `ComonotonicAdditiveRep`: a rank-ordering map +
per-cone utilities. The crux might be free within a single comonotone cone.

**Soundness gate (gate 2).** Already mechanized: `Comonotonic.lean` proves the
comonotone representation makes `P` a weak order, and the degenerate (constant
rank-order) case collapses to `AdditiveRep`. ✓

**Triviality (gate 3).** `comonotonic_wakker_representation` takes a **per-cone
`AdditiveRep`** (`perConeRep : Equiv.Perm ι → AdditiveRep P`) as a hypothesis. So the
crux (constructing each per-cone additive rep) **reappears per cone** — the comonotone
structure does *not* make it free; it relativizes it to cones. **Fails (3): the crux is
assumed per cone.** ✗

**Determination for Candidate B.** Sound but does not discharge the crux — it carries it
per cone. **Discard for the unconditional goal** (it is a generalization that assumes the
same content cone-wise). It remains valuable as the CPT/RDU skeleton (its actual purpose).

---

## 3. Candidate C — strengthened (unrestricted) solvability

**The idea.** Replace `RestrictedSolvability` with **unrestricted solvability** (every
single-coordinate equation `[·|background] ∼ target` is solvable, not just bracketed
ones) or **double-cancellation solvability** (the compensations in the measuring-stick
construction are *assumed* to coincide).

**Soundness gate (gate 2).** Unrestricted solvability: `unrestrictedSolvability_of_additiveRep`
holds iff each `R.V i` is *surjective* — which a representation does NOT guarantee in
general (bounded utilities). So unrestricted solvability is **NOT necessary under a rep**
unless surjectivity is separately assumed. **For ℝ-coordinates with continuous unbounded
`V`, it holds** (the project's `pivotUtilitySurjective_of_continuous_unbounded`, C2). So:
* bare "unrestricted solvability" — **fails gate 2** (not rep-necessary in general). ✗
* "unrestricted solvability *for ℝ-coords with the topology bundle*" — rep-necessary ✓
  but it is **derivable from the existing axioms** (C2, already proved), so it adds
  nothing toward the crux. ✗ (3).

**Double-cancellation solvability** (the compensations coincide): this is
*literally* the matching `OffCalCompensationMatch` / the hexagon — **fails (3),(4): it is
the crux assumed.** ✗

**Determination for Candidate C.** No sound, non-trivial strengthening of solvability
discharges the crux: either not rep-necessary, or already-derivable, or the crux renamed.
**Discard.**

---

## 4. Candidate D — finite / explicit-grid structure (the project's actual setting)

**The idea.** The companion papers work on the **rational grid** `ℚ^S` (see
`ClassicalLotteryLeanFormalization_MainPaper.tex`). On an explicit grid with explicit
spacing, the equal-spacing might be *constructive* (definitional) rather than derived.

**Soundness gate (gate 2).** A grid with definitionally-equal spacing
(`αⱼ n := n·δ_j` for explicit `δ_j`) trivially has equal steps. Under a rep this matches
iff the rep's `V_j` is *affine on the grid* — which is the standard-sequence calibration
(`spaced_j`), rep-necessary. ✓
**Triviality (gates 3,4).** If the grid spacing is *definitional* (the coordinate space
IS `ℕ` or `ℚ` with `V_j = id`), then the cross-pair equal-spacing is free — BUT this
*assumes a cardinal coordinate scale* (the grid points carry their own metric). That is
the same "cardinal input" issue as Candidate A: the theorem becomes "additive rep on a
pre-metrized grid", not "from ordinal preference". **Non-trivial only by assuming the
scale.** ✗ for the *ordinal* theorem; ✓ for an explicitly *cardinal/grid* companion.

**Determination for Candidate D.** This is the most *practically* relevant (the papers
use grids), and it is honest **if the claim is narrowed** to "additive representation on
a coordinate-metrized grid" — where the cross-pair content is carried by the grid metric.
Worth a **companion theorem** clearly scoped as cardinal-grid, NOT Wakker IV.2.7's
ordinal claim. **Recommended: this is the one genuinely-worth-building alternative**, as
an explicitly-scoped grid variant.

---

## 5. Summary table

| Candidate | Sound (gate 2) | Free (gate 3) | Non-trivial (gate 4) | Verdict |
|---|---|---|---|---|
| **A** primitive difference `≽*` | ✓ | only if new primitive | assumes cardinal scale | weaker companion theorem |
| **B** comonotone/CPT | ✓ | ✗ (crux per cone) | — | discard (carries crux) |
| **C** strengthened solvability | ✗ / derivable | ✗ | — | discard |
| **D** explicit grid / ℚ^S | ✓ | ✓ (grid metric) | assumes scale | **companion theorem (recommended)** |

**Overall determination.** No alternative axiom set discharges the crux *for free while
keeping Wakker's ordinal claim*. The cross-pair content is genuinely cardinal: every
sound axiom that makes it free does so by **assuming a cardinal scale** (a primitive
difference relation A, or a metrized grid D) — which is exactly the content the ordinal
theorem is meant to construct. This is not a defect of the mechanization; it is the
**mathematical essence** of why additive conjoint measurement is hard (KLST's point: the
representation *constructs* the cardinal scale from ordinal data, and that construction
is the §IV.5 standard-sequence argument with no shortcut).

**The honest, genuinely-new alternatives worth building** (both explicitly scoped as
*different, weaker* theorems, NOT Wakker IV.2.7):
* **Candidate D** — additive representation on a cardinal/rational grid (matches the
  companion papers' actual setting; the cross-pair content is carried by the grid
  metric, soundly). Lowest risk, highest practical relevance.
* **Candidate A** — additive representation from a primitive KLST difference structure
  (the cardinal scale is an explicit input). Standard KLST Ch. 4; clean but assumes more.

Both are companion results that *complement* the main contribution (the reduction + the
seven irreducibility findings), not replacements for the unconditional ordinal theorem —
which remains gated on the §IV.5 construction or the §6 fallback.

---

## 6. Next concrete action (if pursuing an alternative)

**Candidate D, soundness-gate-first:**
1. State `CardinalGridStructure P` — coordinate spaces with an explicit `ℕ`/`ℚ`-grid and
   definitional spacing (the standard-sequence grid IS the index).
2. Gate: `cardinalGridStructure_of_additiveRep` — the grid is affine under a rep
   (rep-necessary on the grid). 
3. Probe: prove `gridThomsenClosure` is FREE on the cardinal grid (the equal-spacing is
   `n·δ`, definitional) — the genuine test that D escapes the wall *by assuming the scale*.
4. If it passes: build the cardinal-grid additive representation as a clearly-scoped
   companion theorem `additiveRep_of_cardinalGridStructure`, distinguished in the audit
   and the write-up from the ordinal Wakker IV.2.7.

> **EXECUTED (steps 1–3).** `OptionB_CardinalGridCompanion.lean` (`sorry`-free, audited,
> baseline 2429 jobs).
> * **Step 1:** `CardinalGridSliceStructure P base j k` — the cardinal datum (explicit
>   grids + coordinate metrics `Vⱼ, Vₖ` whose index-sum score grid-additively represents
>   the preference, i.e. the grid order IS the metric index-sum order).
> * **Step 2 (gate 2 ✓):** `cardinalGridSliceStructure_of_additiveRep` — the datum is
>   necessary under a rep with a strict, equal-spaced, normalized grid (reuses G4.a's
>   `gridAdditiveSliceRep_of_additiveRep`).
> * **Step 3 (gate 3 ✓ — the probe PASSES):** `concreteDiagonalStep_free_of_cardinalGrid`
>   and `gridThomsenClosure_free_of_cardinalGrid` — the C1.a wall (the diagonal step /
>   grid Thomsen closure) is **FREE** given the cardinal datum, confirming the wall is
>   specific to the *ordinal* axiom set.
> All audit `[propext, Classical.choice, Quot.sound]`.
>
> **Honest determination (gate 4).** Candidate D is sound and the wall is free given the
> datum — but it **assumes the cardinal scale** (the grid metric), which is exactly what
> the ordinal theorem constructs. So it is a *different, weaker* companion theorem, not
> Wakker IV.2.7. Its genuine value: it **localizes the ordinal difficulty** — everything
> downstream of the scale is free, so the entire §IV.5 work is constructing the scale
> (`GridAdditiveSliceRep`) from ordinal data.
>
> **STEP 4 — EXECUTED.** `OptionB_CardinalGridCompanionEndToEnd.lean` (`sorry`-free,
> audited `[propext, Classical.choice, Quot.sound]`). Lifts the cardinal datum to the
> *family* level and runs it end-to-end through the Link-B endpoint:
> * `CardinalGridStructureFamily P j₀ hdata` — the family-level cardinal datum (common
>   pivot metric `V₀` + per-slice coordinate metrics `Vk`, grid-normalized, representing
>   the **full** `{j₀,k}`-slice; free in the cardinal setting, the ordinal C1.a crux
>   otherwise).
> * `perSliceRepresentationFamily_of_cardinalGridStructureFamily` — the bridge to
>   `PerSliceGridRepresentationFamily`.
> * `additiveRep_of_cardinalGridStructureFamily` — **the end-to-end cardinal companion**:
>   `Nonempty (AdditiveRep P)` from the family-level cardinal datum + the standard
>   analytic inputs (density, continuity) + the documented Stage-5 residuals
>   (`hcov`/`hesc`/`hcov19`), via `additiveRep_nonempty_of_perSliceRepresentationFamily`.
> * `cardinalGridStructureFamily_of_additiveRep` — the family-level soundness gate.
>
> This completes Candidate D to an end-to-end `Nonempty (AdditiveRep P)` statement,
> exhibiting the full cardinal route with the ordinal crux carried as the explicit
> cardinal metric. It is the **cardinal companion**, clearly scoped as a different/weaker
> theorem than ordinal Wakker IV.2.7. *(While wiring it, the §IV.5 Link-B endpoint
> `additiveRep_nonempty_of_perSliceRepresentationFamily` was updated to thread the
> Stage-5 coverage/reach residuals `hcov`/`hesc`/`hcov19` exposed by the axiom-16/17/19
> restates — keeping the non-umbrella Link-B route consistent with the main tree.)*
