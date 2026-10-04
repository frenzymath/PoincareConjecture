import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.ExistenceData
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.UniquenessData
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.OperationData

/-!
Adapted from Mapher `PoincareMT/Definitions/M44CapPersistence.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M44 repaired surgery-cap persistence data

This wrapper keeps the exact Proposition 16.5 alternative: a cap either has a
standard-flow comparison cylinder on its assigned interval or disappears at a
later surgery. The standard-cap and metric-surgery certificates are retained
alongside the universal persistence operation.
The forward estimates on the tracked cap region are part of M44's conclusion
construction; callers supply canonicality, pinching and fixed scales.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedCapPersistenceData (g₀ : StandardInitialMetric) where
  standard_cap : RepairedStandardCapExistenceData g₀
  /-- M35 supplies the uniqueness and canonical comparison package for the
      selected standard-cap flow used by Proposition 16.5. -/
  standard_cap_uniqueness :
    Nonempty (RepairedStandardCapUniquenessData g₀ standard_cap)
  metric_surgery : RepairedMetricSurgeryData.{u} g₀
  proposition_16_5 : ∀ (p : SurgeryParameterPrefix metric_surgery.constants)
    (rNext : ℝ),
    p.setup.standard_initial = g₀ →
    0 < rNext → rNext ≤ p.r ⟨p.i, Nat.lt_succ_self _⟩ →
    ∀ A eta theta : ℝ, 0 < A → 0 < eta → 0 < theta → theta < 1 →
      ∃ deltaBar : ℝ, 0 < deltaBar ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          HEq O.standard_flow p.setup.standard_flow →
          SurgeryFixedScalesOn p.setup F O
            (surgeryEpochStart (p.i - 1)) rNext deltaBar →
          SurgeryFlowAdmissible F →
          SurgeryFlowPinched F →
          SurgeryCanonicalOn F (surgeryObservationInterval O) rNext →
          ∀ (t : ℝ) (hT : t ∈ F.surgery_times)
            [Nonempty (F.slice t).carrier],
            t ∈ surgeryObservationInterval O →
            surgeryEpochStart (p.i - 1) ≤ t →
            F.parameters.delta t ≤ deltaBar →
            ∀ i : Fin (F.event t hT).cap_count,
              SurgeryCapPersistenceAlternative F O t hT i A eta theta

end PoincareMT
