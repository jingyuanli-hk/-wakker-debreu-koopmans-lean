/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — C1.a-3 named-input closure capstone (Route D of the crux roadmap)

> **STATUS: `sorry`-free.**  Executes Route D of `OptionB_C1aCruxAttackRoadmap.md`
> in its **sharpest, post-Route-C form**: assembles the *entire* C1.a-3 crux
> closure from a single bundle of **named, proven-necessary KLST inputs**, with
> every other arrow free.  After Route C (`OptionB_C1aSolvabilitySeed.lean`)
> discharged the EXISTENCE of the interior compensators from `RestrictedSolvability`,
> the only carried content is:
>
> * **A1** single-coordinate order independence on `j`, `k`, `t`
>   (`CoordinateOrderIndependent`, proven necessary `coordinateOrderIndependent_of_additiveRep`);
> * the two **§IV.5 measuring-stick Thomsen residues**
>   `KBlockDiagonalResidue ∧ JBlockDiagonalResidue` (each proven necessary,
>   `kBlockDiagonalResidue_of_additiveRep` / `jBlockDiagonalResidue_of_additiveRep`);
> * the interior compensators `p`, `p'` with their indifference witnesses
>   (the EXISTENCE half — supplied free by Route C from `RestrictedSolvability`).
>
> NOT in the umbrella import, NOT merged into `OptionB_AxiomCheck.lean` (it carries
> the §IV.5 Thomsen residues as named inputs rather than discharging them).
>
> ## The bundle
>
> `C1a3NamedInputs P j k t` packs A1 on all three coordinates plus the two diagonal
> residues.  This is *exactly* the §6 fallback bundle, now minimized: the `KBlock`
> and `JBlock` separability conditions are NOT carried directly — they are *built*
> from A1 + the diagonal residues via the R1.1 decomposition
> (`kBlockWeakIndependent_of_decomposition` / `jBlockWeakIndependent_of_decomposition`),
> so the only genuinely non-free content is the pair of two-coordinate-difference
> Thomsen residues.
>
> ## Results
>
> 1. **`diagonalOffCalAtSt_of_namedInputs`** (PROVED, end-to-end): from
>    `C1a3NamedInputs` plus the interior compensators `p`, `p'` (Route C existence),
>    the off-cal diagonal step closes.  Chain:
>    `C1a3NamedInputs ──decomposition──▶ KBlock ∧ JBlock
>       ──interiorCalibration_of_kBlock_jBlock──▶ InteriorCalibration
>       ──diagonalOffCalAtSt_of_interiorCalibration──▶ off-cal diagonal step`.
>    Audit `[propext, Classical.choice, Quot.sound]`.
> 2. **`namedInputs_of_additiveRep`** (soundness gate): every additive
>    representation supplies the whole bundle (all five fields via their necessity
>    gates).  Confirms the carried bundle hides nothing false.  Audit
>    `[propext, Classical.choice, Quot.sound]`.
>
> ## Honest determination (Route D verdict)
>
> Route D is the **honest endpoint** of the C1.a-3 attack.  Routes A/B relocated the
> crux to canonical KLST block separability; Route C discharged the existence half
> via `RestrictedSolvability`; Route D now carries the *residual* — the two §IV.5
> Thomsen residues — as a NAMED, soundness-gated, proven-necessary KLST input, NOT a
> hidden axiom.  The end-to-end theorem shows that, modulo this one declared bundle
> (and Route C's solvability), the crux closes by pure weak order alone.  This is the
> standard Krantz–Luce–Suppes–Tversky / Wakker additive-representation result stated
> at its sharpest: the open content is precisely the §IV.5 measuring-stick step, and
> nothing more.

Imports `OptionB_C1aInteriorCalibration` (Route B chain) and
`OptionB_C1aDiagonalResidue` (decomposition + necessity gates).
-/

import WakkerDebreuKoopmans.OptionB_C1aInteriorCalibration
import WakkerDebreuKoopmans.OptionB_C1aDiagonalResidue

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

/-! ## §A.  The named-input bundle (the §6 fallback, minimized) -/

/-- **`C1a3NamedInputs`** — the minimal carried KLST bundle for the C1.a-3 crux.

A1 single-coordinate order independence on `j`, `k`, `t` (free / proven necessary)
plus the two **§IV.5 measuring-stick Thomsen residues**
`KBlockDiagonalResidue ∧ JBlockDiagonalResidue` (the genuine two-coordinate-difference
content, each proven necessary).  The full `KBlock`/`JBlock` separability conditions
are NOT carried directly — they are derived from this bundle via the R1.1
decomposition. -/
structure C1a3NamedInputs (P : ProductPref X) (j k t : ι) : Prop where
  a1j   : CoordinateOrderIndependent P j
  a1k   : CoordinateOrderIndependent P k
  a1t   : CoordinateOrderIndependent P t
  kdiag : KBlockDiagonalResidue P j k t
  jdiag : JBlockDiagonalResidue P j k t

/-! ## §B.  End-to-end closure from the named bundle (+ Route C compensators) -/

/-- **End-to-end C1.a-3 closure (PROVED) from the named bundle.**

From `C1a3NamedInputs` (A1 + the two §IV.5 Thomsen residues) plus the interior
compensators `p`, `p'` and their indifference witnesses (the existence half,
supplied free by Route C from `RestrictedSolvability`), the off-cal diagonal step
closes.  The chain is: decomposition builds `KBlock ∧ JBlock`, Route B's
`interiorCalibration_of_kBlock_jBlock` builds the interior calibration, and Route
B's `diagonalOffCalAtSt_of_interiorCalibration` discharges the diagonal step.  Every
arrow except the named bundle (and the compensator existence) is free.  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem diagonalOffCalAtSt_of_namedInputs
    [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (H : C1a3NamedInputs P j k t)
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (p p' : X t)
    (hp  : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                    (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st))
    (hp' : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p')
                    (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st)) :
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st) := by
  -- Build the block-separability conditions from A1 + the diagonal residues.
  have hKB : KBlockWeakIndependent P j k t :=
    kBlockWeakIndependent_of_decomposition hjk hjt hkt H.a1j H.a1t H.kdiag
  have hJB : JBlockWeakIndependent P j k t :=
    jBlockWeakIndependent_of_decomposition hjk hjt hkt H.a1k H.a1t H.jdiag
  -- Route B: interior calibration, then the diagonal step.
  have hcal : InteriorCalibration P j k t G m n :=
    interiorCalibration_of_kBlock_jBlock hKB hJB G m n
  exact diagonalOffCalAtSt_of_interiorCalibration G m n p p' hcal hp hp'

/-! ## §C.  Soundness gate: the bundle holds under a representation -/

/-- **Soundness gate (PROVED): the named bundle holds under a rep.**

Every additive representation supplies all five fields of `C1a3NamedInputs` via
their individual necessity gates (`coordinateOrderIndependent_of_additiveRep` for
A1; `kBlockDiagonalResidue_of_additiveRep` / `jBlockDiagonalResidue_of_additiveRep`
for the two §IV.5 Thomsen residues).  Confirms the carried bundle hides nothing
false.  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem namedInputs_of_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    C1a3NamedInputs P j k t where
  a1j   := coordinateOrderIndependent_of_additiveRep R j
  a1k   := coordinateOrderIndependent_of_additiveRep R k
  a1t   := coordinateOrderIndependent_of_additiveRep R t
  kdiag := kBlockDiagonalResidue_of_additiveRep R hjk hjt hkt
  jdiag := jBlockDiagonalResidue_of_additiveRep R hjk hjt hkt

end ProductPref
end WakkerInfra

/-! ## C1.a-3 named-input closure (Route D) audit

* `diagonalOffCalAtSt_of_namedInputs` (end-to-end) — the crux closes from the named
  bundle `C1a3NamedInputs` (A1 + the two §IV.5 Thomsen residues) plus the Route C
  compensators, with every other arrow free.  Audit `[propext, Classical.choice, Quot.sound]`.
* `namedInputs_of_additiveRep` (soundness gate) — the bundle holds under any rep.

**Honest determination.**  Route D is the honest endpoint of the C1.a-3 attack: it
carries the residual §IV.5 measuring-stick content (the two diagonal Thomsen
residues) as a NAMED, proven-necessary, soundness-gated KLST input — not a hidden
axiom.  Modulo this one declared bundle (and Route C's `RestrictedSolvability`), the
crux closes by pure weak order.  NOT merged into `OptionB_AxiomCheck.lean` (it
carries rather than discharges the residues). -/

#print axioms WakkerInfra.ProductPref.diagonalOffCalAtSt_of_namedInputs
#print axioms WakkerInfra.ProductPref.namedInputs_of_additiveRep
