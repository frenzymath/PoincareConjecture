import PoincareConjecture.Definitions.Ch16.CapPersistence
import PoincareConjecture.Definitions.M34StandardCapExistence
import PoincareConjecture.Definitions.M35StandardCapUniqueness
import PoincareConjecture.Definitions.M36MetricSurgery












set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedCapPersistenceData (g₀ : StandardInitialMetric) where
  standard_cap : RepairedStandardCapExistenceData g₀


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

end PoincareConjecture
