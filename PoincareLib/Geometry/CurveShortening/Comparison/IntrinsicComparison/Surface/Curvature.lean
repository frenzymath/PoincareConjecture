import PoincareLib.Geometry.Riemannian.Surface.Curvature
import PoincareLib.Geometry.CurveShortening.Comparison.Theory

/-!
# Surface curvature input for Proposition 19.35

The intrinsic hypothesis is a one-sided Gaussian bound.  On a surface the
retained curvature tensor identities convert it into one-sided sectional and
quadratic bounds.  No absolute curvature-tensor estimate is inferred here.

Context: Morgan--Tian Proposition 19.35, printed pp. 467-481; actual intrinsic
boundary, scalar comparison or endpoint assembly.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT

/-- The Gaussian upper bound controls sectional curvature on independent tangent pairs of
the intrinsic surface. Source: MT Proposition 19.35, pp. 467-481;
`reports/2026-09-23-intrinsic-assembly.md`. -/
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

/-- The Gaussian upper bound gives the one-sided curvature contraction bound against the
nonnegative Gram determinant. Source: MT Proposition 19.35, pp. 467-481;
`reports/2026-09-23-intrinsic-assembly.md`. -/
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

end PoincareMT
