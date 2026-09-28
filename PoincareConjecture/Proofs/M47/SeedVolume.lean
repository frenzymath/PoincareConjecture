import PoincareConjecture.Statements.M47CanonicalInduction
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_RoundPositive
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_NeckVolume
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_CapVolume
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_3_TestScalar












set_option autoImplicit false

open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture



theorem M47Predecessors.toM46 (P : M47Predecessors.{u}) : M46Predecessors.{u} :=
  { m04 := P.m04
    m11 := P.m11
    m12 := P.m12
    m13 := P.m13
    m14 := P.m14
    m15 := P.m15
    regular_history := P.regular_history }

namespace Proofs.M47



noncomputable def canonicalSeedDensity (C : ℝ) : ℝ :=
  min M46.canonicalNeckVolumeFloor (M46.canonicalCapVolumeFloor (max 1 C))



theorem canonicalSeedDensity_pos (C : ℝ) : 0 < canonicalSeedDensity C :=
  lt_min M46.canonicalNeckVolumeFloor_pos
    (M46.canonicalCapVolumeFloor_pos (le_max_left _ _))




theorem canonical_seed_volume (P : M47Predecessors.{u})
    {F : SurgeryFlowData.{u}} {t rho s : ℝ} {x : (F.slice t).carrier}
    (hcanonical : SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C)
    (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 200)
    (hhigh : rho⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x)
    (hpinch : SurgeryPinchedAt (F.connection t) t)
    (hs : 0 < s) (hscalar : (F.connection t).scalarCurvature x ≤ 9 * s⁻¹ ^ 2) :
    ENNReal.ofReal (canonicalSeedDensity F.parameters.C * s ^ 3) ≤
      calibratedMetricVolume (F.metric t) ((F.metric t).ball x s) := by
  rcases M46.canonical_neck_or_cap_of_not_positive hcanonical hpositive with
    ⟨N, hx⟩ | ⟨N, _, hC, hconnection, hx⟩
  · have hNscalar : N.neck.connection.scalarCurvature N.neck.center ≤ 9 * s⁻¹ ^ 2 := by
      rw [N.connection_eq, hx]
      exact hscalar
    have hscale := M46.canonicalNeck_scale_of_scalar_bound N.neck hs hNscalar
    have hvolume := M46.canonicalNeck_test_ball_volume N.neck hs hscale
    rw [hx] at hvolume
    rw [M15.calibratedMetricVolume_eq_volumeMeasure]
    apply (ENNReal.ofReal_le_ofReal ?_).trans hvolume
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hs.le 3)
  · have hNhigh : rho⁻¹ ^ 2 ≤ N.connection.scalarCurvature x := by
      rw [hconnection]
      exact hhigh
    have hsmall : N.core_radius x ≤ 1 / 200 :=
      (M46.canonicalCap_core_radius_le N hx hrho hNhigh).trans hrhoSmall
    have hNpinch : SurgeryPinchedAt N.connection t := by
      rw [hconnection]
      exact hpinch
    have hNscalar : N.connection.scalarCurvature x ≤ 9 * s⁻¹ ^ 2 := by
      rw [hconnection]
      exact hscalar
    have hvolume := M46.canonicalCap_test_ball_volume P.toM46 N hx
      (le_max_left 1 F.parameters.C) (hC.trans (le_max_right _ _)) hs
      hNpinch hsmall hNscalar
    apply (ENNReal.ofReal_le_ofReal ?_).trans hvolume
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hs.le 3)




theorem canonical_crossing_seed_volume (P : M47Predecessors.{u})
    {F : SurgeryFlowData.{u}} {t rho H : ℝ} {x : (F.slice t).carrier}
    (hcanonical : SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C)
    (hpositive : ¬ SurgeryPositiveComponentAt F t x)
    (hrho : 0 < rho) (hrhoSmall : rho ≤ 1 / 200)
    (hlevel : rho⁻¹ ^ 2 ≤ H) (hscalar : (F.connection t).scalarCurvature x = H)
    (hpinch : SurgeryPinchedAt (F.connection t) t) :
    0 < (Real.sqrt H)⁻¹ ∧
      ENNReal.ofReal (canonicalSeedDensity F.parameters.C * (Real.sqrt H)⁻¹ ^ 3) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball x (Real.sqrt H)⁻¹) := by
  have hH : 0 < H := (pow_pos (inv_pos.mpr hrho) 2).trans_le hlevel
  have hs : 0 < (Real.sqrt H)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hH)
  refine ⟨hs, canonical_seed_volume P hcanonical hpositive hrho hrhoSmall ?_ hpinch hs ?_⟩
  · simpa only [hscalar] using hlevel
  · rw [hscalar, inv_inv, Real.sq_sqrt hH.le]
    linarith

end Proofs.M47

end PoincareConjecture
