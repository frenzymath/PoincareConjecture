import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.Metric










set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M34



theorem capRadialCoefficient_mul_sq (a r : ℝ) :
    capRadialCoefficient a r * r ^ 2 = 1 - capAngularCoefficient a r := by
  by_cases hr : r = 0
  · simp [hr, capAngularCoefficient]
  · rw [capRadialCoefficient, if_neg hr]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hr)



theorem capMetricInner_le_norm_sq {a : ℝ} (ha : 0 ≤ a)
    (hapi : a ≤ Real.pi / 2) (x v : StandardCapSpace) :
    capMetricInner a x v v ≤ ‖v‖ ^ 2 := by
  have hcs := real_inner_mul_inner_self_le x v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hscaled := mul_le_mul_of_nonneg_left hcs
    (capRadialCoefficient_nonneg ha hapi (norm_nonneg x))
  have hid := congrArg (fun q : ℝ => q * ‖v‖ ^ 2)
    (capRadialCoefficient_mul_sq a ‖x‖)
  rw [capMetricInner_apply, real_inner_self_eq_norm_sq]
  nlinarith only [hscaled, hid]



theorem capMetricInner_radial_lower {a : ℝ} (ha : 0 ≤ a)
    (hapi : a ≤ Real.pi / 2) (x v : StandardCapSpace) :
    (inner ℝ x v) ^ 2 ≤ ‖x‖ ^ 2 * capMetricInner a x v v := by
  have hcs := real_inner_mul_inner_self_le x v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hscaled := mul_le_mul_of_nonneg_left hcs
    (capAngularCoefficient_pos ha hapi (norm_nonneg x)).le
  have hid := congrArg (fun q : ℝ => q * (inner ℝ x v) ^ 2)
    (capRadialCoefficient_mul_sq a ‖x‖)
  rw [capMetricInner_apply, real_inner_self_eq_norm_sq]
  nlinarith only [hscaled, hid]



theorem capMetricInner_radial_line (a t : ℝ) (x : StandardCapSpace) :
    capMetricInner a (t • x) x x = ‖x‖ ^ 2 := by
  have hid := congrArg (fun q : ℝ => q * ‖x‖ ^ 2)
    (capRadialCoefficient_mul_sq a ‖t • x‖)
  rw [capMetricInner_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hid ⊢
  nlinarith only [hid]



theorem capRiemannianMetric_tangentNorm_le {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (x v : StandardCapSpace) :
    (capRiemannianMetric a ha hapi).tangentNorm x v ≤ ‖v‖ := by
  change Real.sqrt (capMetricInner a x v v) ≤ ‖v‖
  exact (Real.sqrt_le_left (norm_nonneg v)).mpr
    (capMetricInner_le_norm_sq ha.le hapi x v)



theorem capRiemannianMetric_tangentNorm_radial {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (t : ℝ) (x : StandardCapSpace) :
    (capRiemannianMetric a ha hapi).tangentNorm (t • x) x = ‖x‖ := by
  change Real.sqrt (capMetricInner a (t • x) x x) = ‖x‖
  rw [capMetricInner_radial_line, Real.sqrt_sq (norm_nonneg x)]

end PoincareConjecture.M34
