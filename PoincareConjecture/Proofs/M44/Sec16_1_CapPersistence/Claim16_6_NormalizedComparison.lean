import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_InitialConfinement
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedCoefficients
import PoincareConjecture.Proofs.M01.NormalizationVolumeScaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryCapClose

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}

noncomputable def normalizedMetric (Q : SurgeryCapClose g₀ S g tip scale eta) :
    RiemannianMetric 3 S.carrier :=
  m01RescaledMetric g (scale⁻¹ ^ 2) (sq_pos_of_pos (inv_pos.mpr Q.scale_pos))

theorem normalizedMetric_ball (Q : SurgeryCapClose g₀ S g tip scale eta)
    (p : S.carrier) (r : ℝ) : Q.normalizedMetric.ball p r = g.ball p (scale * r) := by
  rw [normalizedMetric, m01RescaledMetric_ball,
    Real.sqrt_sq (inv_pos.mpr Q.scale_pos).le, div_inv_eq_mul, mul_comm r scale]

noncomputable def normalizedComparison (Q : SurgeryCapClose g₀ S g tip scale eta) :
    SurgeryCapClose g₀ S Q.normalizedMetric tip 1 eta where
  eta_pos := Q.eta_pos
  scale_pos := by norm_num
  map := Q.map
  inverse := Q.inverse
  map_tip := Q.map_tip
  map_smooth := Q.map_smooth
  inverse_smooth := Q.inverse_smooth
  image_contains := by
    rw [one_mul, Q.normalizedMetric_ball]
    exact Q.image_contains
  left_inverse := Q.left_inverse
  right_inverse := Q.right_inverse
  coefficient_smooth a b := by
    change ContDiffOn ℝ ∞ (fun x => scale⁻¹ ^ 2 * surgeryMetricCoefficient g Q.map a b x) _
    exact contDiffOn_const.mul (Q.coefficient_smooth a b)
  jets := by
    simpa only [inv_one, one_pow, one_mul, surgeryCapPullback, normalizedMetric,
      m01RescaledMetric_inner] using Q.jets

theorem normalizedComparison_coefficients (Q : SurgeryCapClose g₀ S g tip scale eta) :
    Q.normalizedComparison.normalizedCoefficients = Q.normalizedCoefficients := by
  funext x
  ext v w
  simp only [normalizedCoefficients_apply, normalizedComparison, normalizedMetric,
    m01RescaledMetric_inner, inv_one, one_pow, one_mul]

theorem isCompact_closure_normalized_ball
    (Q : SurgeryCapClose g₀ S g tip scale eta) (heta : eta < 1)
    {r : ℝ} (hr : 0 < r) (hrEta : r < eta⁻¹) :
    IsCompact (closure (Q.normalizedMetric.ball tip (Real.sqrt (1 - eta) * r))) := by
  simpa only [one_pow, one_mul] using
    Q.normalizedComparison.isCompact_closure_ball_of_buffer heta hr hrEta

end PoincareConjecture.SurgeryCapClose
