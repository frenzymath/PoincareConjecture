import PoincareConjecture.Proofs.M13.OperatorTransport
import PoincareConjecture.Proofs.M13.Completeness
import PoincareConjecture.Proofs.M13.Volume
import PoincareConjecture.Statements.M13MetricHomothety

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M13

variable {n : ℕ} {M : Type*} {N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]

theorem metricHomothetyCalculus
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) : MetricHomothetyCalculus g h f Q where
  tangent_norm := homothety_tangentNorm g h f Q hQ hf
  tangent_norm_sq := homothety_tangentNorm_sq g h f Q hQ hf
  path_length a b _ γ hγ := homothety_pathELength g h f Q hQ hf γ a b hγ
  edist_eq := homothety_edist g h f Q hQ hf
  ball_image := homothety_ball_image g h f Q hQ hf
  complete_iff := homothety_complete_iff g h f Q hQ hf
  compact_image_iff _ := f.toHomeomorph.isCompact_image
  volume_map := homothety_volume_map g h f Q hQ hf
  volume_image := homothety_volume_image g h f Q hQ hf
  connection_eq := homothety_connection_eq g h f Q hf
  curvature_eq := homothety_curvature_eq g h f Q hf
  riemann_eq := homothety_curvatureTensor_eq g h f Q hf
  ricci_eq := homothety_ricci_eq g h f Q hQ hf
  scalar_eq := homothety_scalarCurvature_eq g h f Q hQ hf
  sectional_eq := homothety_sectionalCurvature_eq g h f Q hQ hf
  curvature_norm_eq := homothety_curvatureTensorNorm_eq g h f Q hQ hf
  curvature_norm_sq_eq := homothety_curvatureTensorNorm_sq_eq g h f Q hQ hf
  curvature_bound_iff := homothety_curvature_bound_iff g h f Q hQ hf
  nonnegative_operator_iff := homothety_nonnegative_operator_iff g h f Q hQ hf
  operator_bound_iff := homothety_operator_bound_iff g h f Q hQ hf
  nonflat_iff := homothety_nonflat_iff g h f Q hQ hf

end PoincareConjecture.M13
