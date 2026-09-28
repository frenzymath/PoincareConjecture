import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ZeroDimensional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineArclength
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.GradientBound

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

theorem not_minimizing_line_dim_zero
    {M : Type*} [TopologicalSpace M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] [IsManifold (𝓡 0) ∞ M]
    (g : RiemannianMetric 0 M) (γ : ℝ → M) :
    ¬ ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| := by
  intro hγ
  let : Subsingleton M := Poincare.subsingleton_of_preconnected_euclidean_zero M
  have h01 := hγ 0 1
  have h11 := hγ 1 1
  have heq : γ 0 = γ 1 := Subsingleton.elim _ _
  rw [heq] at h01
  norm_num at h11
  rw [h11] at h01
  norm_num at h01

section AnyDimension

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem noncompactSpace_of_minimizing_line (g : RiemannianMetric n M) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    NoncompactSpace M := by
  constructor
  intro hcompact
  obtain ⟨R, hR⟩ := hcompact.bddAbove_image (g.continuous_busemann hγ).continuousOn
  have hbound := hR (mem_image_of_mem (g.busemann γ) (mem_univ (γ (R + 1))))
  rw [g.busemann_apply_line hγ] at hbound
  linarith

end AnyDimension

private theorem real_minimizing_line_affine {F : ℝ → ℝ}
    (hF : ∀ s t : ℝ, |F s - F t| = |s - t|) :
    ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ t, F t = F 0 + a * t := by
  have hsq (s t : ℝ) : (F s - F t) ^ 2 = (s - t) ^ 2 := by
    simpa only [sq_abs] using congrArg (fun r : ℝ => r ^ (2 : ℕ)) (hF s t)
  have ha : (F 1 - F 0) ^ 2 = 1 := by simpa using hsq 1 0
  rcases sq_eq_one_iff.mp ha with hplus | hminus
  · refine ⟨1, Or.inl rfl, fun t => ?_⟩
    have hzero := hsq t 0
    have hone := hsq t 1
    nlinarith
  · refine ⟨-1, Or.inr rfl, fun t => ?_⟩
    have hzero := hsq t 0
    have hone := hsq t 1
    nlinarith

section DimensionOne

variable {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]

theorem contMDiff_busemann_and_surjective_line_dim_one
    (g : RiemannianMetric 1 M) (hcomplete : MetricComplete g) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (g.busemann γ) ∧ Function.Surjective γ := by
  let : NoncompactSpace M := g.noncompactSpace_of_minimizing_line hγ
  obtain ⟨e, he, hi, hmetric⟩ := g.exists_metric_line_coordinate hcomplete
  have hedist := g.edist_eq_of_metric_line_coordinate e (he.of_le (by simp))
    (hi.of_le (by simp)) hmetric
  have hreal (x y : M) : (g.edist x y).toReal = |e x - e y| := by
    rw [← hedist, edist_dist, ENNReal.toReal_ofReal dist_nonneg, Real.dist_eq]
  have hline (s t : ℝ) : |e (γ s) - e (γ t)| = |s - t| := by
    rw [← hreal, hγ, ENNReal.toReal_ofReal (abs_nonneg _)]
  obtain ⟨a, ha, hcoord⟩ := real_minimizing_line_affine hline
  have hb : g.busemann γ = fun x => a * (e x - e (γ 0)) := by
    funext x
    apply tendsto_nhds_unique (g.tendsto_busemannApprox hγ x)
    apply tendsto_const_nhds.congr'
    rcases ha with rfl | rfl
    · filter_upwards [eventually_ge_atTop (e x - e (γ 0))] with t ht
      dsimp only [busemannApprox]
      rw [hreal, hcoord t]
      simp only [one_mul]
      rw [abs_of_nonneg (by linarith : 0 ≤ e (γ 0) + t - e x)]
      ring
    · filter_upwards [eventually_ge_atTop (e (γ 0) - e x)] with t ht
      dsimp only [busemannApprox]
      rw [hreal, hcoord t]
      simp only [neg_one_mul]
      rw [abs_of_nonpos (by linarith : e (γ 0) + -t - e x ≤ 0)]
      ring
  refine ⟨?_, ?_⟩
  · rw [hb]
    exact contMDiff_const.mul (he.sub contMDiff_const)
  · intro x
    refine ⟨a * (e x - e (γ 0)), e.injective ?_⟩
    rw [hcoord]
    rcases ha with rfl | rfl <;> ring

theorem busemann_properties_dim_one
    (g : RiemannianMetric 1 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ (g.busemann γ) ∧
      (∀ x, g.busemann (fun t => γ (-t)) x = -g.busemann γ x) ∧
      (∀ s, g.busemann γ (γ s) = s) ∧
      (∀ x, D.laplacian (g.busemann γ) x = 0) ∧
      (∀ x, g.inner x (D.gradient (g.busemann γ) x)
        (D.gradient (g.busemann γ) x) = 1) ∧
      (∀ x (v w : TangentSpace (𝓡 1) x), D.hessian (g.busemann γ) x v w = 0) := by
  obtain ⟨hf, hsurj⟩ := g.contMDiff_busemann_and_surjective_line_dim_one hcomplete hγ
  have hunit (x : M) : g.inner x (D.gradient (g.busemann γ) x)
      (D.gradient (g.busemann γ) x) = 1 := by
    apply D.gradient_normSq_eq_one_of_distance_lipschitz_of_calibrated_spheres
      hf (g.abs_busemann_sub_le hγ)
    intro r hr
    exact g.exists_busemann_calibrated_point hcomplete hγ x hr
  refine ⟨hf, ?_, g.busemann_apply_line hγ,
    D.laplacian_eq_zero_of_unit_gradient hf hunit, hunit,
    D.hessian_eq_zero_of_unit_gradient hf hunit⟩
  intro x
  obtain ⟨s, rfl⟩ := hsurj x
  rw [g.busemann_apply_line hγ]
  simpa only [neg_neg] using
    g.busemann_apply_line (g.minimizing_line_reverse hγ) (-s)

end DimensionOne

end PoincareConjecture.RiemannianMetric
