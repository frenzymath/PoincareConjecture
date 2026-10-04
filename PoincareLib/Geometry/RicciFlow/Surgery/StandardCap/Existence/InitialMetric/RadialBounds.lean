import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.Metric

/-!
# Radial and ambient speed bounds for the initial cap

Morgan-Tian Lemma 12.2, printed pp. 294-295. The Cartesian cap metric
preserves radial speeds and bounds the differential of the radius. These
algebraic inequalities are the input to the distance and completeness
proofs recorded in `proof-work/tasks/M34/derivations/radial-distance.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareMT.M34

/-- The radial correction identity holds even at the origin, with no
division by zero (Lemma 12.2, pp. 294-295). -/
theorem capRadialCoefficient_mul_sq (a r : ℝ) :
    capRadialCoefficient a r * r ^ 2 = 1 - capAngularCoefficient a r := by
  by_cases hr : r = 0
  · simp [hr, capAngularCoefficient]
  · rw [capRadialCoefficient, if_neg hr]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hr)

/-- The cap metric is bounded above by the Euclidean metric as a
quadratic form (Lemma 12.2, pp. 294-295). -/
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

/-- The differential of squared radius is controlled by the cap metric,
including at the origin (Lemma 12.2, pp. 294-295). -/
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

/-- Every radial line has its Euclidean speed, including where it passes
through the tip (Lemma 12.2, pp. 294-295). -/
theorem capMetricInner_radial_line (a t : ℝ) (x : StandardCapSpace) :
    capMetricInner a (t • x) x x = ‖x‖ ^ 2 := by
  have hid := congrArg (fun q : ℝ => q * ‖x‖ ^ 2)
    (capRadialCoefficient_mul_sq a ‖t • x‖)
  rw [capMetricInner_apply, real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hid ⊢
  nlinarith only [hid]

/-- A cap tangent vector has norm at most its Euclidean norm
(Lemma 12.2, pp. 294-295). -/
theorem capRiemannianMetric_tangentNorm_le {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (x v : StandardCapSpace) :
    (capRiemannianMetric a ha hapi).tangentNorm x v ≤ ‖v‖ := by
  change Real.sqrt (capMetricInner a x v v) ≤ ‖v‖
  exact (Real.sqrt_le_left (norm_nonneg v)).mpr
    (capMetricInner_le_norm_sq ha.le hapi x v)

/-- The radial segment has constant cap speed, which will give the upper
bound for distance from the tip (Lemma 12.2, pp. 294-295). -/
theorem capRiemannianMetric_tangentNorm_radial {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (t : ℝ) (x : StandardCapSpace) :
    (capRiemannianMetric a ha hapi).tangentNorm (t • x) x = ‖x‖ := by
  change Real.sqrt (capMetricInner a (t • x) x x) = ‖x‖
  rw [capMetricInner_radial_line, Real.sqrt_sq (norm_nonneg x)]

end PoincareMT.M34
