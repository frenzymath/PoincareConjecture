import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Line
import PoincareConjecture.Proofs.Horizon.Analysis.Heat.GaussianSmooth










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal
open Poincare.Analysis.Heat

namespace PoincareConjecture.RiemannianMetric



theorem exists_heat_regularization_dim_one
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
    [IsManifold (𝓡 1) ∞ M] [PreconnectedSpace M] [NoncompactSpace M]
    (g : RiemannianMetric 1 M) (D : LeviCivitaData g) (hc : MetricComplete g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ f)
    (hgrad : ∀ x, g.tangentNorm x (D.gradient f x) ≤ 2) :
    ∃ F : ℝ × M → ℝ,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ) ∧
      (∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
        (D.laplacian (fun y ↦ F (t, y)) x) t) ∧
      TendstoUniformly (fun t x ↦ F (t, x)) f (𝓝[>] 0) ∧
      (∀ t, 0 < t → ∀ x,
        |F (t, x) - f x| ≤ 2 * Real.sqrt (2 * t) ∧
        g.tangentNorm x (D.gradient (fun y ↦ F (t, y)) x) ≤ 2) := by
  obtain ⟨e, he, hi, hmetric⟩ := g.exists_metric_line_coordinate hc
  have hed := g.edist_eq_of_metric_line_coordinate e (he.of_le (by simp))
    (hi.of_le (by simp)) hmetric
  let fR : ℝ → ℝ := f ∘ e.symm
  have hfR : ContDiff ℝ ∞ fR := (hf.comp hi).contDiff
  have hdfR : Differentiable ℝ fR := hfR.differentiable (by simp)
  have hLip : LipschitzWith 2 fR := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := g.abs_sub_le_mul_toReal_edist_of_derivative_bound
      (hf.of_le (by simp)) (K := (2 : ℝ≥0)) (by norm_num)
      (fun z ↦ (D.gradient_norm_le_iff f z (by norm_num)).mp (hgrad z))
      (e.symm x) (e.symm y)
    simpa [fR, Function.comp_def, ← hed, edist_dist, Real.dist_eq] using h
  have hunit (x : M) : g.inner x (D.gradient e x) (D.gradient e x) = 1 :=
    D.inner_gradient_eq_one_of_metric_coordinate (hmetric x)
  let F : ℝ × M → ℝ := fun p ↦ gaussianAverage fR p.1 (e p.2)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hG := (contDiffOn_gaussianAverage hLip hdfR).contDiffAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds
        (show (p.1, e p.2) ∈ {q : ℝ × ℝ | 0 < q.1} from hp.1))
    exact (hG.contMDiffAt.comp p (contMDiffAt_fst.prodMk_space
      ((he p.2).comp p contMDiffAt_snd))).contMDiffWithinAt
  · intro t ht x
    change HasDerivAt (fun s ↦ gaussianAverage fR s (e x))
      (D.laplacian (gaussianAverage fR t ∘ e) x) t
    rw [D.laplacian_comp he (contDiff_gaussianAverage hLip hdfR ht),
      D.laplacian_eq_zero_of_unit_gradient he hunit, hunit, mul_zero, mul_one, zero_add]
    exact gaussianAverage_heatEquation hLip hdfR ht (e x)
  · simpa [F, fR, Function.comp_def] using (tendstoUniformly_gaussianAverage hLip).comp e
  · intro t ht x
    constructor
    · simpa [F, fR, Function.comp_def] using abs_gaussianAverage_sub_le hLip t (e x)
    · change g.tangentNorm x (D.gradient (gaussianAverage fR t ∘ e) x) ≤ 2
      rw [D.gradient_comp ((he x).mdifferentiableAt (by simp))
        ((contDiff_gaussianAverage hLip hdfR ht).differentiable (by simp) (e x))]
      simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul, hunit, mul_one]
      rw [Real.sqrt_mul_self_eq_abs]
      exact abs_deriv_gaussianAverage_le hLip t (e x)



theorem exists_heat_regularization_unit_bounds_dim_one
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
    [IsManifold (𝓡 1) ∞ M] [PreconnectedSpace M] [NoncompactSpace M]
    (g : RiemannianMetric 1 M) (D : LeviCivitaData g) (hc : MetricComplete g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ f)
    (hgrad : ∀ x, g.tangentNorm x (D.gradient f x) ≤ 2) :
    ∃ F : ℝ × M → ℝ,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ) ∧
      (∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
        (D.laplacian (fun y ↦ F (t, y)) x) t) ∧
      TendstoUniformly (fun t x ↦ F (t, x)) f (𝓝[>] 0) ∧
      (∀ t ∈ Ioc 0 1, ∀ x,
        |F (t, x) - f x| ≤ 2 * Real.sqrt 2 ∧
        g.tangentNorm x (D.gradient (fun y ↦ F (t, y)) x) ≤ 2 * Real.sqrt 2) := by
  obtain ⟨F, hF, hheat, hlim, hbound⟩ := g.exists_heat_regularization_dim_one D hc hf hgrad
  refine ⟨F, hF, hheat, hlim, fun t ht x ↦ ⟨?_, ?_⟩⟩
  · exact (hbound t ht.1 x).1.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith [ht.2])) (by norm_num))
  · exact (hbound t ht.1 x).2.trans (by
      have := Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)
      linarith)

end PoincareConjecture.RiemannianMetric
