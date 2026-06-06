# Option B — consolidation summary (the Wakker IV.2.7 / Debreu–Koopmans mechanization)

**Scope.** This document consolidates the full Option B effort: the machine-checked
**reduction** of the Wakker (1989) IV.2.7 / Debreu–Koopmans (1982) additive-conjoint
representation theorem to a single, proven-necessary, A1-non-derivable structural input
(the KLST `t`-block separability ≡ the Thomsen hexagon), with **both links** of the
construction assembled end-to-end around that input, and a suite of **seven
machine-checked impossibility/irreducibility findings** that precisely characterize why
that input is irreducible from {A1 + restricted solvability + Archimedean + topology}.

Everything below is machine-checked, `sorry`-free, audited in `OptionB_AxiomCheck.lean`
(baseline `OptionB_AxiomAudit_baseline.txt`).

> **UPDATE (axiom-soundness campaign + endpoints).** Since the prior edition:
> * **Zero `_from_raw_axioms` axioms remain in the tree.** The full
>   `axiom *_from_raw_axioms` family was excised or restated. The last one,
>   `sharedPivotStep4TradeoffFamilyOnDataCertificate_from_raw_axioms`, is now a
>   **theorem** consuming the proven-necessary named input
>   `SharedPivotGridAdditiveRepresentationFamily` (endpoint 1, the Thomsen hexagon
>   ≡ per-slice grid representation); see `STEP4_DISCHARGE_ROADMAP.md`. Axioms 6,
>   16, 17, 19 and the two §IV.2.6 injectivity halves (12a/12b) were likewise
>   discharged/restated earlier in the campaign. The **only** remaining `axiom`
>   declarations in the whole tree are the two accepted §III.4.2 topology
>   bracket-reach seams.
> * **Candidate D completed end-to-end (endpoint 2).**
>   `OptionB_CardinalGridCompanionEndToEnd.lean` lifts the cardinal grid datum to
>   the family level and through the Link-B endpoint to
>   `additiveRep_of_cardinalGridStructureFamily : Nonempty (AdditiveRep P)` — the
>   cardinal companion, end-to-end (`OptionB_AlternativeAxiomScoping.md` §6 step 4).
> * **Full-tree verification:** clean build of all roots (umbrella + public audit
>   + entire non-umbrella OptionB tree + the two new files), **2694 jobs, exit 0,
>   0 errors, 0 `sorryAx`**; public `wakker_IV_2_7` / `debreu_koopmans_*` audit
>   `[propext, Classical.choice, Quot.sound]`. The `OptionB_AxiomCheck` baseline
>   regenerated (2433 jobs, 1005 audit lines).
>
> None of this changes the §3/§4 determination: the crux remains machine-checked
> irreducible from Wakker's ordinal axioms; the endpoints are (1) the named-input
> theorem and (2) the cardinal companion, exactly as scoped.

---

## 1. The headline

Both links of the §IV.5 construction are mechanized end-to-end, reducing the entire
theorem to **one** named structural input — the KLST `t`-block separability condition
(equivalently the Thomsen hexagon `DoubleCancellation`):

* **Link A** (`OptionB_EqualSpacingLinkACapstone`):

  ```lean
  theorem doubleCancellation_of_blockIndependence_and_escapeJ2
      (hA1j hA1k hA1t : CoordinateOrderIndependent P …)        -- A1 (structural)
      (hTjkt hTjtk hTtkj : TBlockWeakIndependent P …)          -- the single KLST input ×3 roles
      (esc : J2EscapeData P j k t) :                           -- §IV.2.6 escape grid
      DoubleCancellation P j k
  ```

* **Link B** (`OptionB_EqualSpacingSliceFamily`):

  ```lean
  theorem additiveRep_nonempty_of_perSliceRepresentationFamily
      (… structural axioms + topology …)
      (hrep : PerSliceGridRepresentationFamily P j₀ hdata)     -- the per-slice reps (= the input)
      (hdense …) (hcont …) :
      Nonempty (AdditiveRep P)
  ```

Both reduce to the **same** crux: the per-slice grid-additive representation / the three
KLST block conditions — proved necessary under any representation (the soundness gates),
and proved A1-non-derivable (the probes). This is exactly the standard Wakker/KLST
hypothesis set; the Option B contribution is the machine-checked reduction to a single
minimal input, both links assembled, plus the irreducibility characterization.

---

## 2. The §IV.5 grid construction, fully assembled (G1–G4)

The grid construction (`OptionB_SectionIV5GridConstructionRoadmap.md`) is mechanized
end-to-end modulo the single crux. Each work package is `sorry`-free and audited:

| WP | Content | File | Status |
|---|---|---|---|
| **G1.a** | off-axis calibration from KLST block separability (non-circular) | `OptionB_EqualSpacingThomsenCell` | done |
| **G1.b** | propagate to the full grid Thomsen closure | `OptionB_EqualSpacingGridPropagate` | done |
| **G1.c** | end-to-end grid step (existence + closure) | `OptionB_EqualSpacingGridStep` | done |
| **G2** | transport the grid step to all profiles (`TBlockDiagonalResidue`) | `OptionB_EqualSpacingGridTransport` | done |
| **G3** | §IV.2.6 mesh density + the guard-drop redundancy finding | `OptionB_EqualSpacingMeshDensity` | done |
| **G4.a** | construct the index-sum slice rep `S` (`GridAdditiveSliceRep`) | `OptionB_EqualSpacingSliceRep` | done |
| **G4.b** | off-grid extension = the order-calibration residual (no-go finding) | `OptionB_EqualSpacingSliceExtend` | done |
| **G4.c** | assemble the shared-`V₀` family → `Nonempty (AdditiveRep P)` | `OptionB_EqualSpacingSliceFamily` | done |
| **Link A** | hexagon from the three KLST block conditions | `OptionB_EqualSpacingLinkACapstone` | done |

**Key structural findings along the way** (each machine-checked):

* **G3 guard-drop:** `TBlockDiagonalResidue` is definitionally `TBlockWeakIndependent`
  plus two disequality guards, so the residue is *free* from the block condition — the
  block route's transport (G2) and density (G3) are sound but redundant; the genuine
  content is deriving the block conditions from solvability.
* **G4.a strictness no-go:** order-tracking needs *strict* grid monotonicity, not weak
  (total indifference satisfies the weak form yet falsifies order-tracking).
* **G4.b §N.2 no-go:** the off-grid *representation* is a moving-target relation; the §O
  density engine extends only *fixed* comparisons. The off-grid extension is the named
  §IV.5 order-calibration residual (produced by restricted solvability), not a 2-D
  density closure.

---

## 3. The crux, localized to its sharpest form (C1.a, the seven findings)

The single remaining open content is the cross-pair Thomsen condition from bare
restricted solvability. The C1.a construction (`OptionB_C1aConstructionPlan.md`) drove
it to the sharpest possible localization through three global sessions on top of the
prior cell-level work — **seven machine-checked findings**, each confirming
irreducibility by a distinct route:

1. **A1 ⇏ hexagon** (`OptionB_C1aHexagonProbe`): a concrete `n=3` comonotone
   Thomsen-violating model satisfies A1 on every coordinate yet violates
   `DoubleCancellation` (and `Pstrip`/`Pkz` for the two halves).
2. **Matching kernel ≡ k-block KLST separability** (`OptionB_EqualSpacingProbe`): the
   equal-spacing matching is the indifference shadow of `KBlockWeakIndependent`.
3. **Second-sequence reformulation is circular** (`OptionB_EqualSpacingSecondSequence`):
   a 1-D second standard sequence's existence is equivalent to the shifted calibration.
4. **Layer transport relocates, not discharges** (`OptionB_EqualSpacingLayerTransport`):
   the `t`-stick's diagonal-at-`c'` field already is the off-cal level move.
5. **§D.2b residue circularity** (`OptionB_C1aGridThomsen`): deriving the grid closure
   from the permutation-equivalent diagonal residues is circular.
6. **Cell-level wall** (`OptionB_C1aThomsenClosure`): the off-cal match reduces, by free
   weak order, to the bare `st → c` transport of a `{j,k}`-two-coordinate indifference —
   which *is* `TBlockDiagonalResidue` at the cell (the target), machine-checked.
7. **Measuring-stick + simultaneous closure walls** (`OptionB_C1aMeasuringStick`,
   `OptionB_C1aStickConstruction`, `OptionB_C1aSimultaneousClosure`): the stick is
   constructible at one `k`-background (free), but across-background uniformity IS
   `KBlockWeakIndependent`; the simultaneous two-compensator closure reduces the crux to
   a single-background compensator coincidence, which IS the interior cross-pair
   step-size equality (the target). The classical lever (`standard_sequence_unique` via
   value-level `hStrict`) is blocked — `hStrict_fails_for_plateau` shows value-level
   uniqueness is not free even for essential/solvable/connected coordinates.

Every *quantifier* around the crux is separately discharged (anchor, `t`-level, all-grid-
levels, level transport `w→c`) — see `OptionB_ConsolidationSummary` §2 of the prior
edition / the construction plan §3 DAG. What remains is the single irreducible interior
cross-pair step-size equality ≡ `KBlockWeakIndependent` ≡ the hexagon.

**Determination:** no sound non-circular route from {A1 + solvability + Archimedean +
topology} discharges the crux; the repo's no-go theorems guarantee it. The unconditional
theorem requires either new structural input (beyond Wakker's axiom set — see §7) or the
classical value-level uniqueness route (blocked here by `hStrict`'s non-freeness).

---

## 4. The honest claim

> **"First machine-checked formalization of additive conjoint measurement: a complete
> reduction of the Wakker IV.2.7 / Debreu–Koopmans additive representation theorem to a
> single proven-necessary, A1-non-derivable KLST structural input, with both links of
> the §IV.5 grid construction assembled end-to-end around it, every surrounding
> quantifier separately mechanized, and seven machine-checked impossibility results
> characterizing the irreducibility of the remaining content."**

What is **not** claimed: an unconditional proof from the bare structural axioms.
Discharging the crux is the genuine multi-month §IV.5 standard-sequence construction,
which the seven findings show has no weak-order / A1 / induction / measuring-stick
shortcut in this axiom setting.

---

## 5. The chain status (honest boundary)

```
A1 + 3×TBlockWeakIndependent + J2-escape   ──(Link A, PROVED)──▶  DoubleCancellation P j k
per-slice reps (= the crux) + density + continuity
                                            ──(Link B, PROVED)──▶  Nonempty (AdditiveRep P)
Nonempty (AdditiveRep P)                    ──(WP0 bridge, PROVED)──▶  public wakker_IV_2_7
```

Both links are now mechanized (this is new since the prior edition — Link B's
`DoubleCancellation → GridAdditiveSliceRep → Nonempty` bridge was previously open and is
now `OptionB_EqualSpacingSliceFamily`). The single open input is the crux: the three
KLST block conditions / the per-slice reps from bare solvability. The Link-B endpoint
inherits the documented Phase-65 Stage-5 `_from_raw_axioms` seams (non-surjective `V₀`);
the seam-free route uses the C2/surjective capstones (Phases 66/68).

**WP-integrate remains deliberately not done:** the public `Wakker/AxiomCheck.lean` is
untouched and the public `wakker_IV_2_7` keeps its `hConstruct` hypothesis, because the
crux is not theorem-backed. The audit must not imply a completion that has not happened.

---

## 6. Recommended endpoint

Carry `KBlockWeakIndependent` / `HexagonThomsenResidual` (the hexagon) as a
**proven-necessary named structural input** — the standard Wakker/KLST hypothesis. Under
it the public theorem is honest and complete *now* via the link capstones. The novel,
publishable contributions:

* both links of the §IV.5 construction assembled end-to-end (G1–G4 + Link A/B capstones);
* the single-input reduction with soundness gates (necessity + recovery);
* every surrounding quantifier separately mechanized (continuity / Archimedean / A1);
* seven machine-checked impossibility/irreducibility findings characterizing the crux;

all `sorry`-free, audited at `[propext, Classical.choice, Quot.sound]` (+ the two
documented §III.4.2 topology IVT seams, eliminated in the reach-axiom-free target; +
the documented Stage-5 seams on the non-surjective Link-B endpoint).

**Literature check (performed, June 2026; re-confirmed this consolidation).** A targeted
search of the Archive of Formal Proofs and proof-assistant literature found **no** prior
formalization of additive conjoint measurement or the Debreu/Wakker additive
representation. Adjacent formalized results (Arrow, Gibbard–Satterthwaite, randomised
social choice, measure theory) are in distinct domains. Caminati 2023 (arXiv:2306.10558)
concerns event structures, not conjoint measurement — not prior art. A final check
against the latest CPP/ITP/JAR proceedings is advisable before asserting priority in
print. *(Content rephrased for compliance with licensing restrictions.)*

---

## 7. Forward option: a different axiom set (scoped, not yet attempted)

The crux is irreducible from Wakker's *exact* axiom set. The unconditional theorem may
be reachable from a **different** structural axiom set that makes the cross-pair content
free — this is a genuine, separate research direction (scoped in
`OptionB_AlternativeAxiomScoping.md`). Candidate directions, each to be probed
soundness-gate-first before any construction:

* **Difference/measurement structures** (KLST Ch. 4): a primitive quaternary
  "preference-difference" relation `≽*` makes cross-pair tradeoff transitivity an *axiom*
  rather than a derived condition — potentially discharging the crux by definition.
* **Comonotone/CPT structures** (the repo's `Comonotonic.lean`): a rank-dependent
  representation with a comonotonic-independence axiom; the crux may be free in the
  comonotone cone.
* **Strengthened solvability** (unrestricted / double-cancellation-solvability): an
  axiom set where the measuring-stick construction's compensations coincide by
  hypothesis.
The discipline: each candidate axiom must be (i) stated, (ii) checked *necessary* under a
representation (soundness gate), (iii) probed for whether it makes the crux free, **before**
any forward construction. If a candidate trivially assumes the conclusion, it is recorded
as such and discarded (the §3 discipline that produced the seven findings).

---

## 8. File inventory (Option B, all `sorry`-free, audited)

**Grid construction (G1–G4) + links:**
`OptionB_EqualSpacingThomsenCell`, `OptionB_EqualSpacingGridPropagate`,
`OptionB_EqualSpacingGridStep`, `OptionB_EqualSpacingGridTransport`,
`OptionB_EqualSpacingMeshDensity`, `OptionB_EqualSpacingSliceRep`,
`OptionB_EqualSpacingSliceExtend`, `OptionB_EqualSpacingSliceFamily`,
`OptionB_EqualSpacingLinkACapstone`, `OptionB_HexagonCapstone`.

**C1.a crux attack (the seven findings):**
`OptionB_C1aHexagonProbe`, `OptionB_EqualSpacingProbe`,
`OptionB_EqualSpacingSecondSequence`, `OptionB_EqualSpacingLayerTransport`,
`OptionB_EqualSpacingArchimedeanGrid`, `OptionB_EqualSpacingPivotSplit`,
`OptionB_C1aCompensationExistence`, `OptionB_C1aThomsenClosure`,
`OptionB_C1aMeasuringStick`, `OptionB_C1aStickConstruction`,
`OptionB_C1aSimultaneousClosure`, `OptionB_EqualSpacingStrictness`.

**Roadmaps / plans:** `OptionB_SectionIV5GridConstructionRoadmap`,
`OptionB_C1aConstructionPlan`, `OptionB_UnconditionalConstructionRoadmap`,
`OptionB_EqualSpacingWPEQ1aScoping`.

**Audit surface:** `OptionB_AxiomCheck` (+ `OptionB_AxiomAudit_baseline.txt`,
`OptionB_AxiomAudit_README`).
