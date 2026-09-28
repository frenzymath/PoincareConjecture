import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

set_option autoImplicit false

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem edist_le_mul_edist_of_derivative_bound (g : RiemannianMetric n M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) 1 f)
    {K : ℝ≥0} (hK : 0 < K)
    (hgrad : ∀ x v, |mvfderiv (𝓡 n) f x v| ≤ K * g.tangentNorm x v)
    (x y : M) : EDist.edist (f x) (f y) ≤ (K : ℝ≥0∞) * g.edist x y := by
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  change EDist.edist (f x) (f y) ≤ (K : ℝ≥0∞) * riemannianEDist (𝓡 n) x y
  simp only [riemannianEDist, ENNReal.mul_iInf_of_ne
    (by exact_mod_cast hK.ne' : (K : ℝ≥0∞) ≠ 0) ENNReal.coe_ne_top, le_iInf_iff]
  intro γ hγ
  let η : Path (f x) (f y) := γ.map hf.continuous
  have hη : ContMDiff (𝓡∂ 1) (𝓘(ℝ, ℝ)) 1 η := hf.comp hγ
  have hdist : EDist.edist (f x) (f y) ≤ ∫⁻ t, ‖mfderiv (𝓡∂ 1) (𝓘(ℝ, ℝ)) η t 1‖ₑ := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)), riemannianEDist]
    exact biInf_le _ hη
  apply hdist.trans
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono
  intro t
  dsimp only
  have hchain : mvfderiv (𝓡∂ 1) η t 1 =
      mvfderiv (𝓡 n) f (γ t) (mfderiv (𝓡∂ 1) (𝓡 n) γ t 1) := by
    change mvfderiv (𝓡∂ 1) (f ∘ γ) t 1 = _
    rw [mvfderiv_comp t (hf.mdifferentiable one_ne_zero (γ t))
      (hγ.mdifferentiable one_ne_zero t)]
    rfl
  have hnorm (z : M) (v : TangentSpace (𝓡 n) z) : ‖v‖ = g.tangentNorm z v := rfl
  have h := hgrad (γ t) (mfderiv (𝓡∂ 1) (𝓡 n) γ t 1)
  rw [← hnorm, ← hchain] at h
  have he := ENNReal.ofReal_le_ofReal h
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, ← Real.norm_eq_abs,
    ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal] at he
  rw [← ofReal_norm, ← ofReal_norm, norm_tangentSpace_vectorSpace]
  exact he

theorem abs_sub_le_mul_toReal_edist_of_derivative_bound [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric n M) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) 1 f) {K : ℝ≥0} (hK : 0 < K)
    (hgrad : ∀ x v, |mvfderiv (𝓡 n) f x v| ≤ K * g.tangentNorm x v)
    (x y : M) : |f x - f y| ≤ K * (g.edist x y).toReal := by
  have he := g.edist_le_mul_edist_of_derivative_bound hf hK hgrad x y
  have ht : (K : ℝ≥0∞) * g.edist x y ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (g.edist_ne_top x y)
  simpa [ENNReal.toReal_mul, edist_dist, Real.dist_eq] using
    ENNReal.toReal_mono ht he

end PoincareConjecture.RiemannianMetric
