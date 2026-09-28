import PoincareConjecture.Proofs.M35.CapGeometry.RadialBallVolumeLower
import PoincareConjecture.Proofs.M35.CapGeometry.RadialCoreCurvatureBalls
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsTailFloor










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.Uniqueness



theorem exists_initial_radial_ball_volume_floor
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta Y B : ℝ}
    (htheta : theta ∈ Ico 0 E.flow.base.lifetime) (hY : 0 ≤ Y) (hB : 0 ≤ B) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ t ∈ Icc 0 theta, ∀ y : StandardCapSpace,
      radialArclength (E.flow.metric t) ‖y‖ ≤ Y → ∀ r : ℝ, 0 ≤ r → r ≤ B →
        ENNReal.ofReal (kappa * r ^ 3) ≤
          calibratedMetricVolume (E.flow.metric t) ((E.flow.metric t).ball y r) := by
  obtain ⟨c, hc, hfloor⟩ := raw_intrinsic_warping_tail_floor P.curvature
    E.flow.base E.rotation_invariant htheta.1 htheta.2
  let R := Y + B + 1
  let m := c / R
  have hR : 0 < R := by dsimp only [R]; positivity
  have hRone : 1 ≤ R := by dsimp only [R]; linarith only [hY, hB]
  have hm : 0 < m := div_pos hc hR
  refine ⟨m ^ 3 * (Real.pi * 4 / 3), by positivity, ?_⟩
  intro t ht y hy r hr hrB
  have htime : t ∈ Ico 0 E.flow.base.lifetime :=
    ⟨ht.1, ht.2.trans_lt htheta.2⟩
  have hf : c ≤ intrinsicWarpingRadius (E.flow.metric t)
      (E.rotation_invariant t htime) (E.complete t htime) R := by
    convert! hfloor t ht R hRone using 1
    exact congrFun
      (rawWarpingRadius_eq P.curvature E.flow.base E.rotation_invariant htime).symm R
  have hratio : m ≤ intrinsicWarpingRadius (E.flow.metric t)
      (E.rotation_invariant t htime) (E.complete t htime) R / R :=
    div_le_div_of_nonneg_right hf hR.le
  have hinside := closure_ball_subset_tip_ball P (E.flow.metric t)
    (E.rotation_invariant t htime) (E.complete t htime) y hr
    (show radialArclength (E.flow.metric t) ‖y‖ + r < R by
      dsimp only [R]
      linarith only [hy, hrB])
  exact radial_ambient_ball_volume_lower (E.flow.metric t) (E.flow.connection t)
    (E.rotation_invariant t htime) (E.complete t htime) (E.nonnegative_sectional t htime)
    P hR hm hr hratio y (subset_closure.trans hinside)



theorem exists_initial_radial_ball_strict_volume
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta Y B : ℝ}
    (htheta : theta ∈ Ico 0 E.flow.base.lifetime) (hY : 0 ≤ Y) (hB : 0 ≤ B) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C ≥ C₀, ∀ t ∈ Icc 0 theta, ∀ y : StandardCapSpace,
      radialArclength (E.flow.metric t) ‖y‖ ≤ Y → ∀ r : ℝ, 0 < r → r ≤ B →
        ENNReal.ofReal (C⁻¹ * r ^ 3) <
          calibratedMetricVolume (E.flow.metric t) ((E.flow.metric t).ball y r) := by
  obtain ⟨k, hk, hvolume⟩ := exists_initial_radial_ball_volume_floor P E htheta hY hB
  refine ⟨2 / k, by positivity, ?_⟩
  intro C hC t ht y hy r hr hrB
  have hCpos : 0 < C := (div_pos (by norm_num) hk).trans_le hC
  have hinv : C⁻¹ < k := by
    apply (inv_lt_iff_one_lt_mul₀ hCpos).mpr
    have hmul := (div_le_iff₀ hk).mp hC
    nlinarith only [hmul]
  have hstrict : ENNReal.ofReal (C⁻¹ * r ^ 3) < ENNReal.ofReal (k * r ^ 3) :=
    (ENNReal.ofReal_lt_ofReal_iff (mul_pos hk (pow_pos hr 3))).mpr
      (mul_lt_mul_of_pos_right hinv (pow_pos hr 3))
  exact hstrict.trans_le (hvolume t ht y hy r hr.le hrB)

end PoincareConjecture.M35.Uniqueness
