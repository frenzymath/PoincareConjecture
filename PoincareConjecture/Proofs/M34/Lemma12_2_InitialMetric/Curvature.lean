import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.RoundCurvature
import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.RadialDistance

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

set_option backward.isDefEq.respectTransparency false in

theorem capNonnegativeSectionalCurvature {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (D : LeviCivitaData (capRiemannianMetric a ha hapi)) :
    D.NonnegativeSectionalCurvature := by
  intro x u v
  by_cases hx : x = 0
  · subst x
    rw [capCurvatureTensor_round ha hapi D (by simpa only [norm_zero] using ha)]
    simp only [capMetricInner_zero]
    nlinarith only [real_inner_mul_inner_self_le u v]
  · have hf : 0 ≤ capProfile a ‖x‖ :=
      (capProfile_pos ha.le hapi (norm_pos_iff.mpr hx)).le
    have hq := capSlope_deriv_nonpos hapi (norm_nonneg x)
    have hp0 := capSlope_nonneg hapi (norm_nonneg x)
    have hp1 := capSlope_le_one a ‖x‖
    have hp : 0 ≤ 1 - capSlope a ‖x‖ ^ 2 := by
      nlinarith only [mul_self_le_mul_self hp0 hp1]
    rw [capCurvatureTensor_formula ha hapi D hx]
    exact add_nonneg
      (mul_nonneg (div_nonneg
        (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hf) hq) (by positivity))
        (sq_nonneg _))
      (mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hp) (by positivity))
        (Poincare.radial_gram_nonneg hx u v))

set_option backward.isDefEq.respectTransparency false in

theorem capTipSectionalCurvature {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (D : LeviCivitaData (capRiemannianMetric a ha hapi)) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ (capRiemannianMetric a ha hapi).ball 0 r,
      ∀ u v : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (capRiemannianMetric a ha hapi) x u v →
          D.sectionalCurvature x u v = (1 / 4 : ℝ) := by
  refine ⟨a / 2, half_pos ha, ?_⟩
  intro x hx u v huv
  rw [capRiemannianMetric_ball_zero ha hapi] at hx
  have hr : ‖x‖ < a := by
    have h := Metric.mem_ball.mp hx
    rw [dist_zero_right] at h
    linarith
  rcases huv with ⟨hu, hv, huv⟩
  change capMetricInner a x u u = 1 at hu
  change capMetricInner a x v v = 1 at hv
  change capMetricInner a x u v = 0 at huv
  change D.curvatureTensor x u v u v /
    (capMetricInner a x u u * capMetricInner a x v v - capMetricInner a x u v ^ 2) = _
  rw [capCurvatureTensor_round ha hapi D hr, hu, hv, huv]
  norm_num

end PoincareConjecture.M34
