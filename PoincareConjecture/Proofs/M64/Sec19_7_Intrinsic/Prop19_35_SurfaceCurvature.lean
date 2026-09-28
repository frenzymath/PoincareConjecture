import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Curvature
import PoincareConjecture.Statements.M64Comparison












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture




theorem m64Intrinsic_sectionalCurvature_le_of_gaussian
    (N : IntrinsicAnnulus) (K : ℝ)
    (hK : N.GaussianCurvatureBound K)
    (p : AnnulusCoordinates) (hp : p ∈ standardAnnulusDomain)
    (u v : TangentSpace (𝓡 2) p)
    (hgram : N.metric.inner p u u * N.metric.inner p v v -
      (N.metric.inner p u v) ^ 2 ≠ 0) :
    N.connection.sectionalCurvature p u v ≤ K := by
  rw [N.connection.sectionalCurvature_eq_half_scalarCurvature p u v hgram]
  exact hK p hp




theorem m64Intrinsic_curvatureTensor_quadratic_le_of_gaussian
    (N : IntrinsicAnnulus) (K : ℝ)
    (hK : N.GaussianCurvatureBound K)
    (p : AnnulusCoordinates) (hp : p ∈ standardAnnulusDomain)
    (u v : TangentSpace (𝓡 2) p) :
    N.connection.curvatureTensor p u v u v ≤
      K * (N.metric.inner p u u * N.metric.inner p v v -
        (N.metric.inner p u v) ^ 2) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
    ⟨N.metric.toRiemannianMetric⟩
  have hgram : 0 ≤ N.metric.inner p u u * N.metric.inner p v v -
      (N.metric.inner p u v) ^ 2 := by
    change 0 ≤ inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2
    have hcs := real_inner_mul_inner_self_le u v
    nlinarith
  rw [N.connection.curvatureTensor_eq_half_scalarCurvature p]
  rw [N.metric.symm p v u, ← pow_two]
  have hscalar : N.connection.scalarCurvature p / 2 ≤ K := hK p hp
  exact mul_le_mul_of_nonneg_right hscalar hgram

end PoincareConjecture
