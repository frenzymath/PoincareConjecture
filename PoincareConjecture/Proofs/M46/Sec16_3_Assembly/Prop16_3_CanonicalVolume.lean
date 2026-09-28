import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_RoundPositive
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_NeckVolume
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_CapVolume
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_TestScalar
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

noncomputable def canonicalVolumeConstant {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) : ℝ :=
  min canonicalNeckVolumeFloor (canonicalCapVolumeFloor (max 1 p.setup.C))

theorem canonicalVolumeConstant_pos {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) : 0 < canonicalVolumeConstant p :=
  lt_min canonicalNeckVolumeFloor_pos (canonicalCapVolumeFloor_pos (le_max_left _ _))

theorem canonical_test_volume (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {rNext cutoff : ℝ} (hrNext : 0 < rNext)
    (hrLast : rNext ≤ p.r ⟨p.i, Nat.lt_succ_self _⟩)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O) (D : NoncollapseTest F O)
    (hhigh : rNext⁻¹ ^ 2 ≤ (F.connection D.time).scalarCurvature D.center) :
    ENNReal.ofReal (canonicalVolumeConstant p * D.radius ^ 3) ≤
      calibratedMetricVolume (F.metric D.time) ((F.metric D.time).ball D.center D.radius) := by
  have hcanonical := inputs.canonical D.time D.time_mem D.time_domain D.center hhigh
  rcases canonical_neck_or_cap_of_not_positive hcanonical D.not_positive with
    ⟨N, hx⟩ | ⟨N, _, hC, hconnection, hx⟩
  · have hscalar : N.neck.connection.scalarCurvature N.neck.center ≤ 9 * D.radius⁻¹ ^ 2 := by
      rw [N.connection_eq, hx]
      exact D.center_scalar_le
    have hscale := canonicalNeck_scale_of_scalar_bound N.neck D.radius_pos hscalar
    have hvolume := canonicalNeck_test_ball_volume N.neck D.radius_pos hscale
    rw [hx] at hvolume
    rw [M15.calibratedMetricVolume_eq_volumeMeasure]
    apply le_trans (ENNReal.ofReal_le_ofReal _) hvolume
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg D.radius_pos.le 3)
  · have hB : N.cap_constant ≤ max 1 p.setup.C := by
      rw [inputs.old.C_eq] at hC
      exact hC.trans (le_max_right _ _)
    have hNhigh : rNext⁻¹ ^ 2 ≤ N.connection.scalarCurvature D.center := by
      rw [hconnection]
      exact hhigh
    have hsmall : N.core_radius D.center ≤ 1 / 200 :=
      (canonicalCap_core_radius_le N hx hrNext hNhigh).trans
        ((hrLast.trans (p.r_le_epsilon _)).trans
          (p.setup.epsilon_le.trans (min_le_left _ _)))
    have hpinch : SurgeryPinchedAt N.connection D.time := by
      rw [hconnection]
      exact inputs.pinched D.time D.time_domain
    have hscalar : N.connection.scalarCurvature D.center ≤ 9 * D.radius⁻¹ ^ 2 := by
      rw [hconnection]
      exact D.center_scalar_le
    have hvolume := canonicalCap_test_ball_volume P N hx (le_max_left 1 p.setup.C)
      hB D.radius_pos hpinch hsmall hscalar
    apply le_trans (ENNReal.ofReal_le_ofReal _) hvolume
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg D.radius_pos.le 3)

end PoincareConjecture.Proofs.M46
