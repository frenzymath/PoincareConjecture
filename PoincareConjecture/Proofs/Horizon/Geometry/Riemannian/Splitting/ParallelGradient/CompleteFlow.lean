import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Flow
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Geodesic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem exists_global_gradientIntegralCurve
    {D : LeviCivitaData g} {f : M → ℝ} (hc : MetricComplete g)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hunit : HasUnitGradient D f)
    (hzero : HasZeroHessian D f) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ (D.gradient f) ∧
      g.IsGeodesicOn γ univ ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ := by
  obtain ⟨γ, hgeo, hγ0, hcoord⟩ := g.exists_global_geodesic hc x (D.gradient f x)
  have hs := contMDiff_global_geodesic hgeo
  have hinit : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 = D.gradient f (γ 0) := by
    have hx : γ 0 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
      rw [hγ0]
      exact mem_chart_source _ x
    have heq := congrArg (fun L => L 1) (mfderiv_comp 0
      ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hx).mdifferentiableAt (by simp))
      ((hs 0).mdifferentiableAt (by simp)))
    rw [mfderiv_eq_fderiv] at heq
    change deriv (fun t => extChartAt (𝓡 n) x (γ t)) 0 =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x) (γ 0)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) at heq
    rw [hcoord.deriv, hγ0, mfderiv_extChartAt_self] at heq
    change D.gradient f x = mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 at heq
    rw [← hγ0] at heq
    exact heq.symm
  refine ⟨γ, hγ0, ?_, hgeo, hs⟩
  intro t
  apply ((hs t).mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv
  ext
  rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
  exact geodesic_velocity_eq_gradient hf hunit hzero hgeo hinit t

theorem exists_complete_gradientFlow
    {D : LeviCivitaData g} {f : M → ℝ} (hc : MetricComplete g)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hunit : HasUnitGradient D f)
    (hzero : HasZeroHessian D f) :
    ∃ Φ : ℝ → M → M,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, IsMIntegralCurve (fun t => Φ t x) (D.gradient f)) ∧
      (∀ x, g.IsGeodesicOn (fun t => Φ t x) univ) ∧
      (∀ x, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun t => Φ t x)) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      (∀ t x, f (Φ t x) = f x + t) := by
  choose γ hγ0 hγ hgeo hs using exists_global_gradientIntegralCurve hc hf hunit hzero
  let Φ : ℝ → M → M := fun t x => γ x t
  refine ⟨Φ, hγ0, hγ, hgeo, hs, ?_, ?_⟩
  · intro s t x
    have hv : ContMDiff (𝓡 n) (𝓡 n).tangent 1
        (fun y => (⟨y, D.gradient f y⟩ : TangentBundle (𝓡 n) M)) :=
      fun y => (D.contMDiffAt_gradient (hf y)).of_le (by simp)
    have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      hv ((hγ x).comp_add t) (hγ (γ x t)) (t₀ := 0) (by simp [hγ0])
    exact congrFun heq s
  · intro t x
    exact integralCurve_value_eq_add hf hunit (hγ x) (hγ0 x) t

end PoincareConjecture.RiemannianMetric
