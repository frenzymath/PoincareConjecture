import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Complete.Global
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Speed


noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem exists_complete_gradientFlow_of_bounded_hessian
    (D : LeviCivitaData g) (hc : MetricComplete g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hess : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      |D.hessian f x v v| ≤ C * g.inner x v v) :
    ∃ Φ : ℝ → M → M,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) (D.gradient f)) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ) := by
  exact Poincare.Manifold.exists_smooth_globalFlow_of_compact_confinement
    (D.contMDiff_gradient hf)
    (fun x A _ => D.exists_compact_confinement_of_bounded_hessian hc hf hC hess x A)

end PoincareConjecture.LeviCivitaData
