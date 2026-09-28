import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Intrinsic
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalization









set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M47



theorem terminalCurvature_neck_carrier_subset_ball
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {H : ℝ} (hH : 0 < H) (hscalar : H ≤ N.connection.scalarCurvature N.center) :
    N.carrier ⊆ g.ball N.center
      (H ^ (-1 / 2 : ℝ) * Real.sqrt (1 + N.epsilon) *
        (2 * N.epsilon⁻¹ + Real.sqrt 2 * (Real.pi + 1)) + 1) := by
  have hepsilon := N.epsilon_pos
  have hcenter := N.central_sphere_subset N.center_on_central_sphere
  have hscale : N.scale ≤ H ^ (-1 / 2 : ℝ) := by
    rw [N.scale_eq_scalar]
    exact Real.rpow_le_rpow_of_nonpos hH hscalar (by norm_num)
  have hheightCenter := (N.coordinate_inverse_mem N.center hcenter).2
  have hfactor : 0 ≤ 2 * N.epsilon⁻¹ + Real.sqrt 2 * (Real.pi + 1) := by
    positivity
  intro y hy
  have hheight := (N.coordinate_inverse_mem y hy).2
  have hdiff : |(N.coordinate_inverse y).2 - (N.coordinate_inverse N.center).2| ≤
      2 * N.epsilon⁻¹ := by
    apply abs_le.mpr
    constructor <;> linarith [hheight.1, hheight.2, hheightCenter.1, hheightCenter.2]
  have hbound := (N.intrinsicEDist_le_axial_add hcenter hy).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (add_le_add hdiff le_rfl) (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _))))
  have hscaleBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg (1 + N.epsilon))) hfactor
  apply ((edist_le_intrinsicEDist N.carrier N.center y).trans hbound).trans_lt
  apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
  linarith

end PoincareConjecture.M47
