import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_1_Constants
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_4_RegularRegion









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46




structure StableSource {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {D : NoncollapseTest F O} (H : HalfRadiusHistory D) (taubar l0 V : ℝ) where
  exponential : M14ExponentialFamily H.spacetime.geometry.toLGeometry D.time
    ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val
  tau : ℝ
  tau_pos : 0 < tau
  tau_le : tau ≤ taubar
  radius_sq_le : (D.radius / 2) ^ 2 ≤ tau
  terminal_mem : D.time - tau ∈ H.spacetime.history.generalized.interval
  stable : M14StableSet H.spacetime.geometry.toLGeometry D.time tau
    ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val exponential
  W : Set (H.spacetime.geometry.toLGeometry.Horizontal
    ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val)
  W_open : IsOpen W
  W_subset : W ⊆ stable.carrier
  reduced_length : ∀ Z ∈ W, exponential.reduced_length Z (Real.sqrt tau) ≤ l0
  image_volume : ENNReal.ofReal V ≤
    calibratedMetricVolume
      (H.spacetime.geometry.toLGeometry.slices (D.time - tau)).metricOnPoints
      (stable.endpoint_slice_map '' W)



noncomputable def StableSource.configuration
    (P : M46Predecessors.{u}) {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {D : NoncollapseTest F O} {H : HalfRadiusHistory D} {taubar l0 V : ℝ}
    (Q : StableSource H taubar l0 V) :
    M15Theorem81Configuration H.spacetime.geometry.toLGeometry D.time
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center)
      Q.exponential taubar l0 V (D.radius / 2) _ _
      (M15.rawActualBallCylinder H.spacetime.geometry P.m13 H.center
        (half_pos D.radius_pos) H.cylinder H.time_subset H.based H.curvature) where
  tau₀ := Q.tau
  tau₀_pos := Q.tau_pos
  tau₀_le := Q.tau_le
  radius_sq_le_tau₀ := Q.radius_sq_le
  terminal_mem := Q.terminal_mem
  terminal_ball_compact := H.terminal_ball_compact
  stable := Q.stable
  W := Q.W
  W_open := Q.W_open
  W_subset_stable := Q.W_subset
  normalized_reduced_length := Q.reduced_length
  terminal_image_volume := Q.image_volume



theorem StableSource.volume (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {taubar l0 V : ℝ} (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {D : NoncollapseTest F O} {H : HalfRadiusHistory D}
    (Q : StableSource H taubar l0 V) :
    ENNReal.ofReal (configurationKappa p U * D.radius ^ 3) ≤
      calibratedMetricVolume (F.metric D.time) ((F.metric D.time).ball D.center D.radius) := by
  have h := H.spacetime.configuration_half_radius U P H.time_mem H.center
    (half_pos D.radius_pos) H.cylinder H.time_subset H.based H.curvature
    Q.exponential (Q.configuration P) rfl
  rw [H.center_eq] at h
  exact (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (configurationKappa_le_uniform p U)
      (pow_nonneg D.radius_pos.le 3))).trans h

end PoincareConjecture.Proofs.M46
