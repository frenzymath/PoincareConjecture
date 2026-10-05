import PoincareLib.Geometry.RicciFlow.Surgery.Induction.NoncollapseData

/-!
Adapted from Mapher `PoincareMT/Statements/M46NoncollapseInduction.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators intervalIntegral

universe u

namespace PoincareMT

structure RepairedNoncollapseInductionTheory : Prop where
  induction : ∀ S : RepairedControlledSchedulesData.{u},
      Nonempty (RepairedNoncollapseInductionData.{u} S)

end PoincareMT
