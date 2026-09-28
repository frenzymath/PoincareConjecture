import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.PolarDifferential

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M34

theorem capMetricInner_polar (a : ℝ) {r : ℝ} (hr : 0 < r)
    (u V W : StandardCapSpace) (hu : ‖u‖ = 1)
    (hV : inner ℝ u V = 0) (hW : inner ℝ u W = 0) (s t : ℝ) :
    capMetricInner a (r • u) (r • V + s • u) (r • W + t • u) =
      capProfile a r ^ 2 * inner ℝ V W + s * t := by
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hVu : inner ℝ V u = 0 := by rw [real_inner_comm, hV]
  have hnr : ‖r • u‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one]
  have hc : capAngularCoefficient a r * r ^ 2 = capProfile a r ^ 2 := by
    rw [capAngularCoefficient, if_neg hr.ne', div_pow]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hr.ne')
  have hb := capRadialCoefficient_mul_sq a r
  rw [capMetricInner_apply, hnr]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hV, hW, hVu, huu, mul_zero, mul_one, add_zero, zero_add]
  nlinarith only [congrArg (fun q : ℝ => q * inner ℝ V W) hc,
    congrArg (fun q : ℝ => q * (s * t)) hb]

set_option backward.isDefEq.respectTransparency false in

theorem capRiemannianMetric_cylinder_pullback {a : ℝ} (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (hn : capProfile a Real.pi = Real.sqrt 2)
    (R : ℝ) (z : StandardCylinderSpace) (hr : a + 1 / 2 ≤ R + z.2)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    (capRiemannianMetric a ha hapi).inner (capCylinderCoordinate R z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (capCylinderCoordinate R) z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (capCylinderCoordinate R) z w) =
        standardCylinderInner 0 z v w := by
  let V : StandardCapSpace := mvfderiv (𝓡 2) (fun q : UnitTwoSphere => q.1) z.1 v.1
  let W : StandardCapSpace := mvfderiv (𝓡 2) (fun q : UnitTwoSphere => q.1) z.1 w.1
  have hp : 0 < R + z.2 := by linarith
  have hV : inner ℝ (z.1 : StandardCapSpace) V = 0 := capSphere_tangent_orthogonal z.1 v.1
  have hW : inner ℝ (z.1 : StandardCapSpace) W = 0 := capSphere_tangent_orthogonal z.1 w.1
  change capMetricInner a (capCylinderCoordinate R z) _ _ = _
  rw [capCylinderCoordinate_mfderiv, capCylinderCoordinate_mfderiv]
  change capMetricInner a ((R + z.2) • (z.1 : StandardCapSpace))
    ((R + z.2) • V + v.2 • (z.1 : StandardCapSpace))
    ((R + z.2) • W + w.2 • (z.1 : StandardCapSpace)) = _
  rw [capMetricInner_polar a hp _ V W (norm_eq_of_mem_sphere z.1) hV hW,
    capProfile_eq_sqrt_two hapi hn hr, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  change 2 * inner ℝ V W + v.2 * w.2 = 2 * (1 - 0) * inner ℝ V W + v.2 * w.2
  ring

end PoincareConjecture.M34
