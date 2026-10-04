import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.VanishingData

/-!
Adapted from Mapher `PoincareMT/Statements/M42VanishingContinuation.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M42 repaired vanishing-terminal continuation statement

For a fixed M33 continuation with empty controlled core, select the vanishing
operation with its constructor equality, empty terminal carrier,
post-terminal interval, admissibility and pinching, and an infinite terminal
time. The operation retains strict no-later-surgery control on that continued
time domain. This is a
logical projection from supplied M33 data, not a new continuation theorem.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedVanishingContinuationTheory : Prop where
  continuation : ∀ {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T) (branch : RepairedBranchContinuationData I),
    I.controlled_core = ∅ → Nonempty (RepairedVanishingContinuationData I branch)

end PoincareMT
