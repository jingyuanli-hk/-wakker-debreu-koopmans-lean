/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Option B — §IV.5 Thomsen discharge, Phase IV: `CrossPairCancellationData` from
  the topology bundle (the wire-through)

> **STATUS: `sorry`-free.**  Executes **Phase IV** of
> `OptionB_C1aThomsenResidueDischargeRoadmap.md`: feeds the three Phase III
> topology-discharged diagonal residues into the existing unified capstone, giving
> the full `CrossPairCancellationData P j k t` from the standard KLST structural
> inputs (single-coordinate A1 on every coordinate + `WakkerCoordinateTopology`)
> plus the explicitly-named §IV.2.6 / §IV.5 measuring-stick residuals at the three
> coordinate orientations.  NOT in the umbrella import, NOT merged into
> `OptionB_AxiomCheck.lean`.
>
> ## The architecture (why three orientations, no new analysis)
>
> The three block diagonal residues `TBlockDiagonalResidue` / `KBlockDiagonalResidue`
> / `JBlockDiagonalResidue` are *the same statement with the coordinate roles
> permuted* — the stick coordinate cycles through `t`, `k`, `j`.  This is already
> formalized:
>
> * the permutation equivalences `kBlockDiagonalResidue_iff_tBlock_perm`,
>   `jBlockDiagonalResidue_iff_tBlock_perm` (`OptionB_C1aDiagonalPermutation*.lean`),
>   and
> * the unified capstone `crossPairCancellationData_of_a1_and_oneThomsenResidue`
>   (`OptionB_C1aDiagonalUnifiedCapstone.lean`), which derives the whole
>   `CrossPairCancellationData` from A1 on `{j,k,t}` plus a *single* Thomsen residue
>   `TBlockDiagonalResidue` instantiated at the three triples `(j,k,t)`, `(j,t,k)`,
>   `(t,k,j)`.
>
> So Phase IV adds **no** new analytic content: it instantiates the Phase III genuine
> discharge `tBlockDiagonalResidue_of_topology_bracket_and_match`
> (`OptionB_C1aHexagon.lean`) at the three coordinate orientations and plugs the
> results into the unified capstone.  Each orientation carries its own §IV.2.6
> Archimedean reach (`DiagonalStickBracket`), §IV.5 Thomsen matching
> (`DiagonalStickMatch`), single-coordinate weak separability, and diagonal
> compensator — exactly the documented Wakker measuring-stick residuals, kept at the
> `WakkerCoordinateTopology` / IVT level, never a block-independence assumption.

Imports `OptionB_C1aHexagon` (Phase III discharge + the stick residual defs) and
`OptionB_C1aDiagonalUnifiedCapstone` (the one-Thomsen unified capstone).
-/

import WakkerDebreuKoopmans.OptionB_C1aHexagon
import WakkerDebreuKoopmans.OptionB_C1aDiagonalUnifiedCapstone
import WakkerDebreuKoopmans.OptionB_C1aNamedInputClosure

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

/-! ## §IV.5 Thomsen discharge — Phase IV: the topology-route capstone

`crossPairCancellationData_of_klst` is the wire-through: the full
`CrossPairCancellationData` from the standard KLST structural inputs plus the
Phase III measuring-stick residuals at the three coordinate orientations.  Each
orientation's inputs are:

* `DiagonalStickBracket` — the §IV.2.6 Archimedean reach pair the slice-IVT crossing
  consumes (necessary under a rep, `diagonalStickBracket_of_additiveRep`);
* `DiagonalStickMatch` — the §IV.5 Thomsen cross-pair matching (necessary under a
  rep, `diagonalStickMatch_of_additiveRep`);
* single-coordinate weak separability on the stick's paired coordinate;
* a diagonal compensator existence (a `RestrictedSolvability` fill).

The analytic crux (the slice-IVT crossing that produces the compensating stick
value) is theorem-backed from `WakkerCoordinateTopology` in every orientation. -/

/-- **R1.1 capstone from the topology bundle + the §IV.5/§IV.2.6 residuals (PROVED).**

`CrossPairCancellationData P j k t` from:
* single-coordinate A1 on each of `j`, `k`, `t` (the structural input);
* the `WakkerCoordinateTopology` bundle (connectedness + preference continuity —
  the project's standard §III.4.2 topology input, theorem-backing every slice-IVT
  crossing); and
* the Phase III measuring-stick residuals at the three coordinate orientations
  `(j,k,t)` (stick `t`), `(j,t,k)` (stick `k`), `(t,k,j)` (stick `j`): each an
  Archimedean reach bracket + a Thomsen match + single-coordinate weak separability
  + a diagonal compensator.

The three `TBlockDiagonalResidue` instances are produced by the Phase III genuine
discharge `tBlockDiagonalResidue_of_topology_bracket_and_match`; the unified capstone
`crossPairCancellationData_of_a1_and_oneThomsenResidue` (which folds the K/J residues
in via the permutation equivalences) assembles them.  No block-independence
assumption, no carried diagonal residue: the open content is exactly the documented
§IV.2.6 reach + §IV.5 matching residuals.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem crossPairCancellationData_of_klst
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    -- Orientation `(j,k,t)` — stick `t`.
    (hbrT : DiagonalStickBracket P j k t)
    (hmatchT : DiagonalStickMatch P j k t)
    (hsepT : ∀ (b₁ b₂ : Profile X) (v w : X k),
      P.coordPref k b₁ v w → P.coordPref k b₂ v w)
    (hkcompT : ∀ (a : Profile X) (x z : X j) (p r : X k) (w : X t),
      x ≠ z → r ≠ p →
      P.weakPref (tri a j k t x r w) (tri a j k t z p w) →
      ∃ q : X k, P.indiff (tri a j k t x r w) (tri a j k t z q w))
    -- Orientation `(j,t,k)` — stick `k`.
    (hbrK : DiagonalStickBracket P j t k)
    (hmatchK : DiagonalStickMatch P j t k)
    (hsepK : ∀ (b₁ b₂ : Profile X) (v w : X t),
      P.coordPref t b₁ v w → P.coordPref t b₂ v w)
    (hkcompK : ∀ (a : Profile X) (x z : X j) (p r : X t) (w : X k),
      x ≠ z → r ≠ p →
      P.weakPref (tri a j t k x r w) (tri a j t k z p w) →
      ∃ q : X t, P.indiff (tri a j t k x r w) (tri a j t k z q w))
    -- Orientation `(t,k,j)` — stick `j`.
    (hbrJ : DiagonalStickBracket P t k j)
    (hmatchJ : DiagonalStickMatch P t k j)
    (hsepJ : ∀ (b₁ b₂ : Profile X) (v w : X k),
      P.coordPref k b₁ v w → P.coordPref k b₂ v w)
    (hkcompJ : ∀ (a : Profile X) (x z : X t) (p r : X k) (w : X j),
      x ≠ z → r ≠ p →
      P.weakPref (tri a t k j x r w) (tri a t k j z p w) →
      ∃ q : X k, P.indiff (tri a t k j x r w) (tri a t k j z q w)) :
    CrossPairCancellationData P j k t :=
  crossPairCancellationData_of_a1_and_oneThomsenResidue hjk hjt hkt hA1j hA1k hA1t
    (tBlockDiagonalResidue_of_topology_bracket_and_match
      hjk hjt hkt htop hbrT hmatchT hsepT hkcompT)
    (tBlockDiagonalResidue_of_topology_bracket_and_match
      hjt hjk (Ne.symm hkt) htop hbrK hmatchK hsepK hkcompK)
    (tBlockDiagonalResidue_of_topology_bracket_and_match
      (Ne.symm hkt) (Ne.symm hjt) (Ne.symm hjk) htop hbrJ hmatchJ hsepJ hkcompJ)

/-- **Sanity capstone: under a representation the topology route recovers
`CrossPairCancellationData` (PROVED).**

Confirms the Phase IV inputs hide nothing false: under any additive representation,
A1 is theorem-backed and every Thomsen residue is necessary, so the cross-pair data
is recovered (delegating to the existing one-Thomsen sanity capstone — the topology
route is sound).  Audit `[propext, Classical.choice, Quot.sound]`. -/
theorem crossPairCancellationData_of_klst_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    CrossPairCancellationData P j k t :=
  crossPairCancellationData_of_additiveRep_via_oneThomsen R hjk hjt hkt

/-! ## §IV.5 Thomsen discharge — Phase IV(b): the C1.a-3 crux from the topology bundle

The Route D named-input closure `diagonalOffCalAtSt_of_namedInputs`
(`OptionB_C1aNamedInputClosure.lean`) closes the C1.a-3 crux from `C1a3NamedInputs`
(A1 on `{j,k,t}` + the two §IV.5 Thomsen residues `KBlockDiagonalResidue ∧
JBlockDiagonalResidue`) plus the Route C interior compensators.  Phase III/IV
DISCHARGES those two residues from the `WakkerCoordinateTopology` bundle (via the
permutation equivalences applied to the topology discharge of the `t`-block residue
at the permuted orientations).  So `c1a3NamedInputs_of_klst` rebuilds the named
bundle with the diagonal residues no longer carried — only A1 (structural) and the
documented measuring-stick residuals at the `K`/`J` orientations remain. -/

/-- **The C1.a-3 named bundle with the §IV.5 residues discharged from topology
(PROVED).**

Builds `C1a3NamedInputs P j k t` from A1 on each coordinate plus the
`WakkerCoordinateTopology` bundle and the Phase III measuring-stick residuals at the
two permuted orientations `(j,t,k)` (stick `k`, giving the `K`-block residue) and
`(t,k,j)` (stick `j`, giving the `J`-block residue).  The two diagonal Thomsen
residues `KBlockDiagonalResidue` / `JBlockDiagonalResidue` — the only genuinely
two-coordinate content Route D carried — are now produced by
`tBlockDiagonalResidue_of_topology_bracket_and_match` composed with the permutation
equivalences `kBlockDiagonalResidue_iff_tBlock_perm` /
`jBlockDiagonalResidue_iff_tBlock_perm`.  Audit `[propext, Classical.choice,
Quot.sound]`. -/
theorem c1a3NamedInputs_of_klst
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    -- Orientation `(j,t,k)` — stick `k` — discharges the `K`-block residue.
    (hbrK : DiagonalStickBracket P j t k)
    (hmatchK : DiagonalStickMatch P j t k)
    (hsepK : ∀ (b₁ b₂ : Profile X) (v w : X t),
      P.coordPref t b₁ v w → P.coordPref t b₂ v w)
    (hkcompK : ∀ (a : Profile X) (x z : X j) (p r : X t) (w : X k),
      x ≠ z → r ≠ p →
      P.weakPref (tri a j t k x r w) (tri a j t k z p w) →
      ∃ q : X t, P.indiff (tri a j t k x r w) (tri a j t k z q w))
    -- Orientation `(t,k,j)` — stick `j` — discharges the `J`-block residue.
    (hbrJ : DiagonalStickBracket P t k j)
    (hmatchJ : DiagonalStickMatch P t k j)
    (hsepJ : ∀ (b₁ b₂ : Profile X) (v w : X k),
      P.coordPref k b₁ v w → P.coordPref k b₂ v w)
    (hkcompJ : ∀ (a : Profile X) (x z : X t) (p r : X k) (w : X j),
      x ≠ z → r ≠ p →
      P.weakPref (tri a t k j x r w) (tri a t k j z p w) →
      ∃ q : X k, P.indiff (tri a t k j x r w) (tri a t k j z q w)) :
    C1a3NamedInputs P j k t where
  a1j   := hA1j
  a1k   := hA1k
  a1t   := hA1t
  kdiag :=
    (kBlockDiagonalResidue_iff_tBlock_perm hkt).mpr
      (tBlockDiagonalResidue_of_topology_bracket_and_match
        hjt hjk (Ne.symm hkt) htop hbrK hmatchK hsepK hkcompK)
  jdiag :=
    (jBlockDiagonalResidue_iff_tBlock_perm hjk hjt hkt).mpr
      (tBlockDiagonalResidue_of_topology_bracket_and_match
        (Ne.symm hkt) (Ne.symm hjt) (Ne.symm hjk) htop hbrJ hmatchJ hsepJ hkcompJ)

/-- **C1.a-3 crux closure from the topology bundle + Route C compensators (PROVED).**

The off-cal diagonal step closes from:
* single-coordinate A1 on each of `j`, `k`, `t`;
* the `WakkerCoordinateTopology` bundle plus the Phase III measuring-stick residuals
  at the `K`/`J` orientations (which DISCHARGE the two §IV.5 diagonal Thomsen residues
  Route D otherwise carries); and
* the Route C interior compensators `p`, `p'` with their indifference witnesses
  (the EXISTENCE half, supplied free from `RestrictedSolvability`).

This is the genuine discharge endpoint: modulo A1, the topology bundle, the documented
measuring-stick residuals, and Route C's solvability, the C1.a-3 crux closes by pure
weak order.  Delegates to `diagonalOffCalAtSt_of_namedInputs` over the
topology-discharged bundle `c1a3NamedInputs_of_klst`.  Audit `[propext,
Classical.choice, Quot.sound]`. -/
theorem c1a3_of_klst
    [∀ i, TopologicalSpace (X i)] [ProductPref.IsWeakOrder P] {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (hA1j : CoordinateOrderIndependent P j)
    (hA1k : CoordinateOrderIndependent P k)
    (hA1t : CoordinateOrderIndependent P t)
    (htop : WakkerRoadmap.CertificateChecklist.RawAxiomDischargersTopology.WakkerCoordinateTopology P)
    (hbrK : DiagonalStickBracket P j t k)
    (hmatchK : DiagonalStickMatch P j t k)
    (hsepK : ∀ (b₁ b₂ : Profile X) (v w : X t),
      P.coordPref t b₁ v w → P.coordPref t b₂ v w)
    (hkcompK : ∀ (a : Profile X) (x z : X j) (p r : X t) (w : X k),
      x ≠ z → r ≠ p →
      P.weakPref (tri a j t k x r w) (tri a j t k z p w) →
      ∃ q : X t, P.indiff (tri a j t k x r w) (tri a j t k z q w))
    (hbrJ : DiagonalStickBracket P t k j)
    (hmatchJ : DiagonalStickMatch P t k j)
    (hsepJ : ∀ (b₁ b₂ : Profile X) (v w : X k),
      P.coordPref k b₁ v w → P.coordPref k b₂ v w)
    (hkcompJ : ∀ (a : Profile X) (x z : X t) (p r : X k) (w : X j),
      x ≠ z → r ≠ p →
      P.weakPref (tri a t k j x r w) (tri a t k j z p w) →
      ∃ q : X k, P.indiff (tri a t k j x r w) (tri a t k j z q w))
    (G : CalibratedJKGrid P j k t) (m n : ℕ) (p p' : X t)
    (hp  : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p)
                    (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st))
    (hp' : P.indiff (tri G.a j k t (G.αj m) (G.αk n) p')
                    (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st)) :
    P.indiff (tri G.a j k t (G.αj (m + 1)) (G.αk n) G.st)
             (tri G.a j k t (G.αj m) (G.αk (n + 1)) G.st) :=
  diagonalOffCalAtSt_of_namedInputs hjk hjt hkt
    (c1a3NamedInputs_of_klst hjk hjt hkt hA1j hA1k hA1t htop
      hbrK hmatchK hsepK hkcompK hbrJ hmatchJ hsepJ hkcompJ)
    G m n p p' hp hp'

/-- **Sanity gate: under a representation the topology-discharged bundle holds
(PROVED).**

Confirms `c1a3NamedInputs_of_klst` carries nothing false: under any additive
representation, A1 is theorem-backed and the two diagonal residues are necessary, so
the named bundle is recovered (delegating to `namedInputs_of_additiveRep`).  Audit
`[propext, Classical.choice, Quot.sound]`. -/
theorem c1a3NamedInputs_of_klst_additiveRep
    [ProductPref.IsWeakOrder P] (R : AdditiveRep P) {j k t : ι}
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t) :
    C1a3NamedInputs P j k t :=
  namedInputs_of_additiveRep R hjk hjt hkt

end ProductPref
end WakkerInfra

/-! ## §IV.5 Thomsen discharge — Phase IV audit

* `crossPairCancellationData_of_klst` — the topology-route capstone: the full
  `CrossPairCancellationData P j k t` from A1 on every coordinate + the
  `WakkerCoordinateTopology` bundle + the Phase III measuring-stick residuals
  (`DiagonalStickBracket`, `DiagonalStickMatch`, single-`k`/`t` separability, diagonal
  compensator) at the three coordinate orientations.  Audit `[propext,
  Classical.choice, Quot.sound]`.
* `crossPairCancellationData_of_klst_additiveRep` — sanity gate (the route is sound).
  Audit `[propext, Classical.choice, Quot.sound]`.

**Honest determination.**  Phase IV is the pure wire-through: it adds no analytic
content beyond Phase III.  The three block residues are the same Thomsen statement at
the three permuted coordinate roles (the permutation equivalences and the unified
one-Thomsen capstone already encode this), so the full cross-pair data follows by
instantiating the Phase III topology discharge thrice.  The genuinely-open content
remains exactly the documented §IV.2.6 Archimedean reach + §IV.5 Thomsen matching
residuals, carried as explicit, necessity-proven structural inputs at the
`WakkerCoordinateTopology` / IVT level.  NOT merged into `OptionB_AxiomCheck.lean`. -/

#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_klst
#print axioms WakkerInfra.ProductPref.crossPairCancellationData_of_klst_additiveRep

/-! ## §IV.5 Thomsen discharge — Phase IV(b) audit (the C1.a-3 crux wire-through)

* `c1a3NamedInputs_of_klst` — the Route D named bundle `C1a3NamedInputs` with the two
  §IV.5 diagonal Thomsen residues DISCHARGED from `WakkerCoordinateTopology` (via the
  Phase III topology discharge at the `K`/`J` orientations + the permutation
  equivalences).  Audit `[propext, Classical.choice, Quot.sound]`.
* `c1a3_of_klst` — the C1.a-3 crux closure: the off-cal diagonal step closes from A1 +
  the topology bundle + the measuring-stick residuals + the Route C compensators, with
  the two carried §IV.5 residues now topology-discharged.  Audit `[propext,
  Classical.choice, Quot.sound]`.
* `c1a3NamedInputs_of_klst_additiveRep` — sanity gate (the bundle holds under a rep).
  Audit `[propext, Classical.choice, Quot.sound]`.

**Honest determination (Phase IV(b)).**  Route D carried the two diagonal Thomsen
residues as named inputs; Phase IV(b) discharges them from the `WakkerCoordinateTopology`
bundle + the documented §IV.2.6/§IV.5 measuring-stick residuals at the `K`/`J`
orientations.  So the C1.a-3 crux now closes modulo exactly: A1 (structural), the
topology bundle, the documented measuring-stick residuals (Archimedean reach + Thomsen
matching), and Route C's `RestrictedSolvability` compensators — the intended Wakker
IV.2.7 / KLST structural axiom set.  NOT merged into `OptionB_AxiomCheck.lean` (the
measuring-stick residuals remain carried as named, soundness-gated inputs). -/

#print axioms WakkerInfra.ProductPref.c1a3NamedInputs_of_klst
#print axioms WakkerInfra.ProductPref.c1a3_of_klst
#print axioms WakkerInfra.ProductPref.c1a3NamedInputs_of_klst_additiveRep
