import PoincareConjecture.Definitions.Ch15.SurgeryFlow









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture




def M45InitialSurgeryControl (epsilon kappa0 : ℝ) : Prop :=
  ∀ F : SurgeryFlowData.{u},
    Disjoint F.surgery_times (Set.Icc 0 (1 / 16 : ℝ)) ∧
      ∀ t ∈ F.time_domain, t ≤ 1 / 16 → ∀ x : (F.slice t).carrier,
        (F.connection t).curvatureTensorNorm x ≤ 2 ∧
        |(F.connection t).scalarCurvature x| ≤ 18 ∧
        ∀ r : ℝ, 0 < r → r ≤ epsilon →
          ENNReal.ofReal (kappa0 * r ^ 3) ≤
            calibratedMetricVolume (F.metric t) ((F.metric t).ball x r)

end PoincareConjecture
