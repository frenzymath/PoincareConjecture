import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Normalization
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Initial.InitialConfinement
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Limit.Coordinates.NormalizedCoefficients
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Volume

/-!
# The actual comparison after height normalization

The supplied M36 comparison becomes a scale-one certificate for the
normalized physical metric. Its actual balls inherit the proved compact
confinement. Morgan--Tian, Claim 16.6, pp. 371-372; see
`derivations/18-actual-geodesic-transport.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.SurgeryCapClose

variable {g₀ : StandardInitialMetric} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {tip : S.carrier} {scale eta : ℝ}

/-- The physical local-result metric with its single height-squared
normalization, as in Claim 16.6, pp. 371-372. -/
noncomputable def normalizedMetric (Q : SurgeryCapClose g₀ S g tip scale eta) :
    RiemannianMetric 3 S.carrier :=
  m01RescaledMetric g (scale⁻¹ ^ 2) (sq_pos_of_pos (inv_pos.mpr Q.scale_pos))

/-- Every normalized physical ball is exactly the original ball at the
height-scaled radius; Claim 16.6, pp. 371-372. -/
theorem normalizedMetric_ball (Q : SurgeryCapClose g₀ S g tip scale eta)
    (p : S.carrier) (r : ℝ) : Q.normalizedMetric.ball p r = g.ball p (scale * r) := by
  rw [normalizedMetric, m01RescaledMetric_ball,
    Real.sqrt_sq (inv_pos.mpr Q.scale_pos).le, div_inv_eq_mul, mul_comm r scale]

/-- The actual supplied map and inverse give a scale-one comparison
after rescaling the physical metric. Its tolerance and jet bound are
unchanged. Source: Claim 16.6, pp. 371-372. -/
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

/-- Normalizing the certificate retains exactly the coefficient field
whose compact jets converge in Corollary 16.7, p. 372. -/
theorem normalizedComparison_coefficients (Q : SurgeryCapClose g₀ S g tip scale eta) :
    Q.normalizedComparison.normalizedCoefficients = Q.normalizedCoefficients := by
  funext x
  ext v w
  simp only [normalizedCoefficients_apply, normalizedComparison, normalizedMetric,
    m01RescaledMetric_inner, inv_one, one_pow, one_mul]

/-- The normalized physical ball has compact closure inside each
strict comparison buffer. This provides the actual exponential domain
in Claim 16.6, pp. 371-372. -/
theorem isCompact_closure_normalized_ball
    (Q : SurgeryCapClose g₀ S g tip scale eta) (heta : eta < 1)
    {r : ℝ} (hr : 0 < r) (hrEta : r < eta⁻¹) :
    IsCompact (closure (Q.normalizedMetric.ball tip (Real.sqrt (1 - eta) * r))) := by
  simpa only [one_pow, one_mul] using
    Q.normalizedComparison.isCompact_closure_ball_of_buffer heta hr hrEta

end PoincareMT.SurgeryCapClose
