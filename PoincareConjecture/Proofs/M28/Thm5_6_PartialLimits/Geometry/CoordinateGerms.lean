import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

theorem pullbackCoefficients_eq_of_eventuallyEq
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {e f : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (h : e =ᶠ[𝓝 x] f) :
    g.pullbackCoefficients e x = g.pullbackCoefficients f x := by
  ext v w
  change g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w) = _
  rw [h.self_of_nhds, h.mfderiv_eq]
  rfl

end PoincareConjecture.RiemannianMetric
