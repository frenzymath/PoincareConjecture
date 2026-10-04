import PoincareLib.Geometry.RicciFlow.Surgery.Metric.OperationData

/-!
Adapted from Mapher `PoincareMT/Statements/M36MetricSurgery.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M36 repaired metric-surgery statement

Every standard initial metric receives uniform surgery constants and an
operation certificate for each admissible neck.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/- The source contract is Claim 13.1, Theorem 13.2, Definition 13.3, and
   Lemma 13.4 (Morgan--Tian, printed pp. 331--334), specialized to the
   standard initial metric and every admissible epsilon-neck. -/
structure RepairedMetricSurgeryTheory : Prop where
  surgery : ∀ g₀ : StandardInitialMetric,
    Nonempty (RepairedMetricSurgeryData.{u} g₀)

end PoincareMT
