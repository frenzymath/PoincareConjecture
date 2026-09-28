import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderScalarReadout
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckLengthComparison










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.Proofs.M28.NeckAnalysis

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem cylinderScalarCoordinateEquiv_norm_sq (v : EuclideanSpace ℝ (Fin 3)) :
    ‖(cylinderScalarCoordinateEquiv v).1‖ ^ 2 +
        (cylinderScalarCoordinateEquiv v).2 ^ 2 = ‖v‖ ^ 2 := by
  simp [cylinderScalarCoordinateEquiv_apply, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_two, Fin.sum_univ_three]




theorem cylinderNeckCoefficients_quadratic_bounds (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    (1 - N.epsilon) * ‖v‖ ^ 2 ≤ cylinderNeckCoefficients N q s 0 v v ∧
      cylinderNeckCoefficients N q s 0 v v ≤ 2 * (1 + N.epsilon) * ‖v‖ ^ 2 := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let z : RoundCylinderSpace := (c.symm 0, s)
  let w : RoundCylinderCoordinates :=
    (mfderiv (𝓡 2) (𝓡 2) c.symm 0 (cylinderScalarCoordinateEquiv v).1,
      (cylinderScalarCoordinateEquiv v).2)
  have hcoef : cylinderNeckCoefficients N q s 0 v v =
      N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z w w := by
    change N.scale⁻¹ ^ 2 * g.inner _
        (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) 0 v)
        (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) 0 v) = _
    rw [cylinderNeckChart_mfderiv_apply N q s
      (zero_mem_cylinderNeckChartDomain N q hs)]
    dsimp only [cylinderNeckChart]
    erw [cylinderScalarCoordinates_zero]
    rfl
  have hgram := sphere_chart_inverse_inner q
    (cylinderScalarCoordinateEquiv v).1 (cylinderScalarCoordinateEquiv v).1
  dsimp only at hgram
  erw [sphere_chart_center] at hgram
  have hmodel : RoundCylinderMetric z w w =
      2 * ‖(cylinderScalarCoordinateEquiv v).1‖ ^ 2 +
        (cylinderScalarCoordinateEquiv v).2 ^ 2 := by
    dsimp only [RoundCylinderMetric, EvolvingRoundCylinderMetric, z, w, c]
    erw [hgram, real_inner_self_eq_norm_sq]
    ring
  have hN := N.normalized_metric_quadratic_bounds z hs w
  rw [← hcoef, hmodel] at hN
  have hnorm := cylinderScalarCoordinateEquiv_norm_sq v
  have hfirst := sq_nonneg ‖(cylinderScalarCoordinateEquiv v).1‖
  have hlast := sq_nonneg (cylinderScalarCoordinateEquiv v).2
  constructor
  · exact (mul_le_mul_of_nonneg_left (by nlinarith only [hnorm, hfirst])
      (by linarith [N.epsilon_lt_half] : 0 ≤ 1 - N.epsilon)).trans hN.1
  · calc
      _ ≤ (1 + N.epsilon) * (2 * ‖v‖ ^ 2) := hN.2.trans
        (mul_le_mul_of_nonneg_left (by nlinarith only [hnorm, hlast])
          (by linarith [N.epsilon_pos] : 0 ≤ 1 + N.epsilon))
      _ = _ := by ring




theorem scaleSmoothMetric_cylinderNeckCoefficients (N : EpsilonNeck g)
    (Q : ℝ) (hQ : 0 < Q) (q : UnitTwoSphere) (s : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric g Q hQ)
        (cylinderNeckChart N q s) x =
      (Q * N.scale ^ 2) • cylinderNeckCoefficients N q s x := by
  have hscale : N.scale ^ 2 * N.scale⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ N.scale_pos.ne', one_pow]
  ext v w
  change Q * g.pullbackCoefficients (cylinderNeckChart N q s) x v w =
    (Q * N.scale ^ 2) * (N.scale⁻¹ ^ 2 *
      g.pullbackCoefficients (cylinderNeckChart N q s) x v w)
  rw [mul_assoc Q (N.scale ^ 2), ← mul_assoc (N.scale ^ 2), hscale, one_mul]

end PoincareConjecture.M28.tube
