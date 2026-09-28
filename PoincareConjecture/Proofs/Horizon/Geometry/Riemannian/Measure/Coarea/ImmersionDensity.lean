import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Density
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Immersion








set_option autoImplicit false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {m n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓡 m) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]


noncomputable def parametrizedVolumeDensity (g : RiemannianMetric n N)
    (e : EuclideanSpace ℝ (Fin m) → N) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  Real.sqrt (Matrix.of (fun i j : Fin m => g.inner (e x)
    (mfderiv (𝓡 m) (𝓡 n) e x (EuclideanSpace.basisFun (Fin m) ℝ i))
    (mfderiv (𝓡 m) (𝓡 n) e x (EuclideanSpace.basisFun (Fin m) ℝ j)))).det


theorem parametrizedVolumeDensity_congr (g : RiemannianMetric n N)
    {e₁ e₂ : EuclideanSpace ℝ (Fin m) → N} {x : EuclideanSpace ℝ (Fin m)}
    (he : e₁ =ᶠ[𝓝 x] e₂) :
    g.parametrizedVolumeDensity e₁ x = g.parametrizedVolumeDensity e₂ x := by
  unfold parametrizedVolumeDensity
  rw [he.eq_of_nhds, he.mfderiv_eq]



theorem pullbackVolumeDensity_induced (g : RiemannianMetric n N)
    (F : M → N) (hF : ContMDiff (𝓡 m) (𝓡 n) ∞ F)
    (hi : ∀ p, Function.Injective (mfderiv (𝓡 m) (𝓡 n) F p))
    {e : EuclideanSpace ℝ (Fin m) → M} {x : EuclideanSpace ℝ (Fin m)}
    (he : MDifferentiableAt (𝓡 m) (𝓡 m) e x) :
    pullbackVolumeDensity (Induced.pullbackMetric g F hF hi) e x =
      g.parametrizedVolumeDensity (F ∘ e) x := by
  have hchain := mfderiv_comp x ((hF (e x)).mdifferentiableAt (by simp)) he
  unfold pullbackVolumeDensity parametrizedVolumeDensity
  congr 2
  ext i j
  change g.inner (F (e x))
    (mfderiv (𝓡 m) (𝓡 n) F (e x)
      (mfderiv (𝓡 m) (𝓡 m) e x (EuclideanSpace.basisFun (Fin m) ℝ i)))
    (mfderiv (𝓡 m) (𝓡 n) F (e x)
      (mfderiv (𝓡 m) (𝓡 m) e x (EuclideanSpace.basisFun (Fin m) ℝ j))) = _
  rw [hchain]
  rfl

end PoincareConjecture.RiemannianMetric
