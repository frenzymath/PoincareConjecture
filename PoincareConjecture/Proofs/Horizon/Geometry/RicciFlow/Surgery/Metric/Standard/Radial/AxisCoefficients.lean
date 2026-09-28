import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Standard.Radial.AxisMetric

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.MetricSurgery

theorem axisBasis_ne_zero (i : Fin 3) : axisBasis i ≠ 0 := by
  simp [axisBasis]

theorem axisBasis_decomposition (v : StandardCapSpace) :
    v 0 • axisBasis 0 + v 1 • axisBasis 1 + v 2 • axisBasis 2 = v := by
  ext i
  fin_cases i <;> simp [axisBasis]

theorem axisPoint_eq_smul (r : ℝ) : axisPoint r = r • axisBasis 0 := by
  ext i
  fin_cases i <;> simp [axisPoint, axisBasis]

theorem axisPoint_contDiff : ContDiff ℝ ∞ axisPoint := by
  simp_rw [show axisPoint = fun r => r • axisBasis 0 from funext axisPoint_eq_smul]
  exact contDiff_id.smul contDiff_const

theorem metric_inner_contDiff (g : RiemannianMetric 3 StandardCapSpace)
    (v w : StandardCapSpace) :
    ContDiff ℝ ∞ (fun x : StandardCapSpace => g.inner x v w) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : StandardCapSpace → Type _) := ⟨g.toRiemannianMetric⟩
  have hv : ContMDiff (𝓡 3) (𝓡 3).tangent ∞
      (fun x : StandardCapSpace => (⟨x, v⟩ : TangentBundle (𝓡 3) StandardCapSpace)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hw : ContMDiff (𝓡 3) (𝓡 3).tangent ∞
      (fun x : StandardCapSpace => (⟨x, w⟩ : TangentBundle (𝓡 3) StandardCapSpace)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  exact (hv.inner_bundle hw).contDiff

noncomputable def axisRadialCoefficient (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  g₀.metric.inner (axisPoint r) (axisBasis 0) (axisBasis 0)

noncomputable def axisTangentialCoefficient (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  g₀.metric.inner (axisPoint r) (axisBasis 1) (axisBasis 1)

theorem axisRadialCoefficient_pos (g₀ : StandardInitialMetric) (r : ℝ) :
    0 < axisRadialCoefficient g₀ r :=
  g₀.metric.pos _ _ (axisBasis_ne_zero 0)

theorem axisTangentialCoefficient_pos (g₀ : StandardInitialMetric) (r : ℝ) :
    0 < axisTangentialCoefficient g₀ r :=
  g₀.metric.pos _ _ (axisBasis_ne_zero 1)

theorem axisRadialCoefficient_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (axisRadialCoefficient g₀) :=
  (metric_inner_contDiff g₀.metric (axisBasis 0) (axisBasis 0)).comp axisPoint_contDiff

theorem axisTangentialCoefficient_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (axisTangentialCoefficient g₀) :=
  (metric_inner_contDiff g₀.metric (axisBasis 1) (axisBasis 1)).comp axisPoint_contDiff

theorem axis_metric_formula (g₀ : StandardInitialMetric) (r : ℝ)
    (v w : StandardCapSpace) :
    g₀.metric.inner (axisPoint r) v w =
      axisRadialCoefficient g₀ r * v 0 * w 0 +
        axisTangentialCoefficient g₀ r * (v 1 * w 1 + v 2 * w 2) := by
  let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
    g₀.metric.inner (axisPoint r)
  have h01 : B (axisBasis 0) (axisBasis 1) = 0 := axis_metric_zero_one g₀ r
  have h02 : B (axisBasis 0) (axisBasis 2) = 0 := axis_metric_zero_two g₀ r
  have h12 : B (axisBasis 1) (axisBasis 2) = 0 := axis_metric_one_two g₀ r
  have h10 : B (axisBasis 1) (axisBasis 0) = 0 := by
    exact (g₀.metric.symm _ _ _).trans h01
  have h20 : B (axisBasis 2) (axisBasis 0) = 0 := by
    exact (g₀.metric.symm _ _ _).trans h02
  have h21 : B (axisBasis 2) (axisBasis 1) = 0 := by
    exact (g₀.metric.symm _ _ _).trans h12
  have h22 : B (axisBasis 2) (axisBasis 2) = B (axisBasis 1) (axisBasis 1) :=
    (axis_metric_tangential_eq g₀ r).symm
  change B v w = _
  calc
    B v w = B (v 0 • axisBasis 0 + v 1 • axisBasis 1 + v 2 • axisBasis 2)
        (w 0 • axisBasis 0 + w 1 • axisBasis 1 + w 2 • axisBasis 2) := by
      rw [axisBasis_decomposition, axisBasis_decomposition]
    _ = _ := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
        h01, h02, h10, h12, h20, h21, h22]
      change _ = B (axisBasis 0) (axisBasis 0) * v 0 * w 0 +
        B (axisBasis 1) (axisBasis 1) * (v 1 * w 1 + v 2 * w 2)
      ring

end PoincareConjecture.MetricSurgery
