import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Geometry.StrongNeckHalfFlow
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.OpenGeometry.OpenMetricBalls
import PoincareLib.Geometry.Riemannian.Homothety.Length

/-!
# Exact terminal balls of the chosen normalized strong-neck flow

Original small ambient balls stay inside the original neck. Their intrinsic
restriction therefore has the same balls, and the exact terminal homothety
identifies these with balls of the chosen half flow. Definition 9.78 and
Claims 10.10-10.11, Morgan--Tian pp. 232 and 254-255; M28 derivation 72.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28

/-- The terminal neck-normalized ball is exactly the lift of the original
ambient ball at the physical radius, throughout the captured radius range.
The rescaling is the supplied one (Definition 9.78; derivation 72). -/
theorem GeneralizedStrongNeck.rescaled_half_ball_eq_preimage
    {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
    (S : GeneralizedStrongNeck F t epsilon)
    (H : RescaledRawCylinderData (C := F.slice t)
      (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
      (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
    (hepsilon : epsilon < 1 / 2) {r : ℝ} (hr : r ≤ epsilon⁻¹ / 8) :
    ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).ball
        (strongNeckSourceCenter S) r =
      (Subtype.val : strongNeckOpen S → (F.slice t).carrier) ⁻¹'
        (F.metric t).ball S.center (S.scale * r) := by
  let N := strongNeck_top S hepsilon
  let g := intrinsicOpenMetric (F.metric t) (strongNeckOpen S)
  let h := (GeneralizedStrongNeck.rescaled_half_flow S H).metric 0
  have hball : (F.metric t).ball S.center (S.scale * r) ⊆
      (strongNeckOpen S : Set (F.slice t).carrier) := by
    intro x hx
    have hradius : S.scale * r ≤ N.scale * N.epsilon⁻¹ / 8 := by
      change S.scale * r ≤ S.scale * epsilon⁻¹ / 8
      nlinarith [mul_le_mul_of_nonneg_left hr S.scale_pos.le]
    exact (N.small_ball_subset_middle N.center_on_central_sphere
      (hx.trans_le (ENNReal.ofReal_le_ofReal hradius))).1
  have hq : 0 < S.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr S.scale_pos)
  have hhom : MetricHomothety g h (Diffeomorph.refl (𝓡 3) (strongNeckOpen S) ∞)
      (S.scale⁻¹ ^ 2) := by
    intro x v w
    simp only [Diffeomorph.coe_refl, mfderiv_id]
    exact GeneralizedStrongNeck.rescaled_metric_at_zero S H x v w
  have hscaled := M13.homothety_ball_image g h
    (Diffeomorph.refl (𝓡 3) (strongNeckOpen S) ∞) (S.scale⁻¹ ^ 2) hq hhom
    (strongNeckSourceCenter S) (S.scale * r)
  have hradius : Real.sqrt (S.scale⁻¹ ^ 2) * (S.scale * r) = r := by
    rw [Real.sqrt_sq (inv_nonneg.mpr S.scale_pos.le)]
    field_simp [S.scale_pos.ne']
  rw [hradius] at hscaled
  calc
    h.ball (strongNeckSourceCenter S) r =
        g.ball (strongNeckSourceCenter S) (S.scale * r) := by
      simpa using hscaled.symm
    _ = _ := intrinsicOpenMetric_ball_eq_preimage (F.metric t) (strongNeckOpen S)
      (strongNeckSourceCenter S) hball

end PoincareMT.M28
