import Lake
open Lake DSL

package «WakkerDebreuKoopmansLean»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5bad60a0ca3c2a0db665304e78153ccdeb6d80b9"

/-- The Wakker / Debreu--Koopmans additive-representation mechanization (spin-out).

`roots` are the spin-out's three entry points; their transitive imports are the
full development (split modules + the Option~B reduction + the RawAxiomDischargers
layer).  `OptionB_AxiomCheck` is the sorry-free audit aggregator. -/
@[default_target]
lean_lib WakkerDebreuKoopmansLean where
  roots := #[`WakkerDebreuKoopmans.OptionB_AxiomCheck,
    `WakkerDebreuKoopmans.RawAxiomDischargersThomsen,
    `WakkerDebreuKoopmans.OptionB_CardinalGridCompanionEndToEnd]
