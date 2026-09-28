import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Bochner
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Constancy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.ClassicalEquation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle
open Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}


theorem exists_eq_const_of_laplacian_eq_zero_compact (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hΔ : ∀ x, D.laplacian f x = 0) : ∃ c : ℝ, ∀ x, f x = c := by
  have hn : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (D.gradient f x) (D.gradient f x)) := by
    intro x
    have hgrad := D.contMDiffAt_gradient (hf x)
    simpa using (contMDiffAt_totalSpace.mp
      (((g.contMDiff x).clm_bundle_apply hgrad).clm_bundle_apply hgrad)).2
  have hi := hn.continuous.integrable_of_hasCompactSupport
    (μ := g.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hnonneg (x : M) : 0 ≤ g.inner x (D.gradient f x) (D.gradient f x) := by
    by_cases h : D.gradient f x = 0
    · simp [h]
    · exact (g.pos _ _ h).le
  have hz : (∫ x, g.inner x (D.gradient f x) (D.gradient f x)
      ∂g.volumeMeasure) = 0 := by
    have hg := D.integral_mul_laplacian hf hf (HasCompactSupport.of_compactSpace _)
    simp only [hΔ, mul_zero, integral_zero] at hg
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hi).mp hz
  let : g.volumeMeasure.IsOpenPosMeasure := Dirichlet.volumeMeasure_isOpenPosMeasure
  have heq : (fun x => g.inner x (D.gradient f x) (D.gradient f x)) = fun _ => 0 :=
    g.volumeMeasure.eq_of_ae_eq hae hn.continuous continuous_const
  have hgrad (x : M) : D.gradient f x = 0 := by
    by_contra h
    have hp := g.pos x (D.gradient f x) h
    have hzero := congrFun heq x
    linarith
  exact Poincare.Manifold.exists_eq_const_of_mvfderiv_eq_zero
    (hf.mdifferentiable (by norm_num)) fun x v => by
      rw [← D.inner_gradient, hgrad]
      simp

end PoincareConjecture.LeviCivitaData
