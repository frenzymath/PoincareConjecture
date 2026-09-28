import PoincareConjecture.Proofs.M62.Claim19_11_SlopeEvolution










set_option autoImplicit false

open Bundle Manifold Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem m65Slope_hasDerivAt (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    HasDerivAt (m62Slope P c t)
      (curveSpeed P.flow c t x * (P.flow.metric t).inner (c x t)
        (m62CurvatureVector P.flow c t x) (P.charts.circleUnit (c x t))) x := by
  let := P.charts.chartedSpace
  have hP := M62.circleProduct_identities P
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun y => c y t) x :=
    (hc.spatial_regular t ht x).mdifferentiableAt (by norm_num)
  have hfield : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent
      (T% P.charts.circleUnit) (c x t) :=
    (hP.circle_unit_smooth (c x t)).mdifferentiableAt (by simp)
  have hparallel : rampHorizontalCovariantDerivative (P.flow.connection t)
      (fun y => c y t) (fun y => P.charts.circleUnit (c y t)) x = 0 := by
    rw [M62.pullback_ambient_field (P.flow.connection t) hcurve
      P.charts.circleUnit hfield]
    exact hP.circle_parallel t (c x t) _
  have hp := M62.hasDerivAt_metric_pairing (P.flow.connection t) hcurve
    ((M62.unitTangent_contMDiff P.flow c hc ht x).mdifferentiableAt (by simp))
    (hfield.comp x hcurve)
  change HasDerivAt (m62Slope P c t) _ x at hp
  apply hp.congr_deriv
  rw [hparallel]
  simp only [map_zero, add_zero, m62CurvatureVector, m62SpatialDerivative,
    map_smul, smul_apply, smul_eq_mul]
  have hv := (M62.speed_pos P.flow c hc ht x).ne'
  field_simp



theorem m65Slope_deriv_abs_le (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    |deriv (m62Slope P c t) x| ≤
      curveSpeed P.flow c t x * m62Curvature P.flow c t x := by
  let := P.charts.chartedSpace
  let g := P.flow.metric t
  let p := c x t
  let H := m62CurvatureVector P.flow c t x
  let U := P.charts.circleUnit p
  let : RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hU : ‖U‖ = 1 := by
    rw [norm_eq_sqrt_real_inner]
    change Real.sqrt (g.inner p U U) = 1
    rw [(M62.circleProduct_identities P).circle_unit]
    norm_num
  have hH : ‖H‖ = m62Curvature P.flow c t x := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hpair : |g.inner p H U| ≤ m62Curvature P.flow c t x := by
    change |inner ℝ H U| ≤ _
    simpa only [hU, hH, mul_one] using abs_real_inner_le_norm H U
  rw [(m65Slope_hasDerivAt P c hc ht x).deriv, abs_mul,
    abs_of_pos (M62.speed_pos P.flow c hc ht x)]
  exact mul_le_mul_of_nonneg_left hpair (M62.speed_nonneg P.flow c t x)

end PoincareConjecture
