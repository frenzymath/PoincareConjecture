import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Density
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Fubini
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.ImmersionDensity







set_option autoImplicit false

open Poincare.Coarea Poincare.EuclideanSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M] [IsManifold (𝓡 (n + 1)) ∞ M]

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold (𝓡 (n + 1)) ∞ M] in


lemma mfderiv_euclideanCons_basisFun
    {e : EuclideanSpace ℝ (Fin (n + 1)) → M} {t : ℝ}
    {y : EuclideanSpace ℝ (Fin n)}
    (he : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)) e (euclideanCons t y))
    (i : Fin n) :
    mfderiv (𝓡 n) (𝓡 (n + 1)) (e ∘ euclideanCons t) y
      (EuclideanSpace.basisFun (Fin n) ℝ i) =
    mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e (euclideanCons t y)
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i.succ) := by
  rw [mfderiv_comp y he
    (hasFDerivAt_euclideanCons t y).differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, fderiv_euclideanCons]
  change mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) e (euclideanCons t y)
    (euclideanTailCLM n (EuclideanSpace.basisFun (Fin n) ℝ i)) = _
  rw [euclideanTailCLM_basisFun]


theorem parametrizedVolumeDensity_slice (g : RiemannianMetric (n + 1) M)
    {e : EuclideanSpace ℝ (Fin (n + 1)) → M} {t : ℝ}
    {y : EuclideanSpace ℝ (Fin n)}
    (he : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)) e (euclideanCons t y)) :
    g.parametrizedVolumeDensity (e ∘ euclideanCons t) y =
      g.levelCoordinateDensity e (euclideanCons t y) := by
  unfold parametrizedVolumeDensity levelCoordinateDensity
  congr 2
  ext i j
  simp only [Matrix.of_apply, mfderiv_euclideanCons_basisFun he]
  rfl

end PoincareConjecture.RiemannianMetric
