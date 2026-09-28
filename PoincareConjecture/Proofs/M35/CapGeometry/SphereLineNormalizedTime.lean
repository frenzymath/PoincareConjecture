import PoincareConjecture.Proofs.M35.CapGeometry.SphereLineTimeAffine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem sphereLine_normalized_family_affine (N : M27SphereLineFlowCertificate K)
    (coordinate : RoundCylinderSpace → M) (Q : ℝ) (hQ : 0 < Q)
    (u : ℝ) (hu : u ≤ 0) (z : RoundCylinderSpace) (v w : RoundCylinderTangent z) :
    Q * roundCylinderPullback (K.flow.metric (u / Q)) coordinate z v w =
      (1 + 2 * u) * (Q * roundCylinderPullback (K.flow.metric (0 / Q)) coordinate z v w) -
        2 * u * (Q * roundCylinderPullback (K.flow.metric ((-1 / 2) / Q))
          coordinate z v w) := by
  have hclock : (u / Q) / (1 / (2 * Q)) = 2 * u := by
    field_simp [hQ.ne']
  have hhalf : -(1 / (2 * Q)) = (-1 / 2) / Q := by ring
  have h := sphereLine_metric_two_times N (u / Q)
    (div_nonpos_of_nonpos_of_nonneg hu hQ.le) (1 / (2 * Q)) (by positivity)
    (coordinate z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z w)
  rw [hclock, hhalf] at h
  unfold roundCylinderPullback
  rw [h, zero_div]
  ring

end PoincareConjecture.M35
