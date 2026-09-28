import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem pullbackCoefficients_congr_of_eventuallyEq
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    {a b : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (heq : a =ᶠ[𝓝 x] b) : g.pullbackCoefficients a x = g.pullbackCoefficients b x := by
  ext v w
  change g.inner (a x) (mfderiv (𝓡 n) (𝓡 n) a x v)
    (mfderiv (𝓡 n) (𝓡 n) a x w) = _
  rw [heq.mfderiv_eq, heq.self_of_nhds]
  rfl

theorem pullbackCoefficients_eq_of_metric_germ
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {a : EuclideanSpace ℝ (Fin n) → N} {f : M → N}
    {A : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f (A x))
    (hA : MDifferentiableAt (𝓡 n) (𝓡 n) A x)
    (heq : a =ᶠ[𝓝 x] f ∘ A)
    (hmetric : ∀ v w : TangentSpace (𝓡 n) (A x),
      h.inner (f (A x)) (mfderiv (𝓡 n) (𝓡 n) f (A x) v)
        (mfderiv (𝓡 n) (𝓡 n) f (A x) w) = g.inner (A x) v w) :
    h.pullbackCoefficients a x = g.pullbackCoefficients A x := by
  have hd := mfderiv_comp x hf hA
  ext v w
  change h.inner (a x) (mfderiv (𝓡 n) (𝓡 n) a x v)
    (mfderiv (𝓡 n) (𝓡 n) a x w) = _
  rw [heq.mfderiv_eq, hd]
  change h.inner (a x)
    (mfderiv (𝓡 n) (𝓡 n) f (A x) (mfderiv (𝓡 n) (𝓡 n) A x v))
    (mfderiv (𝓡 n) (𝓡 n) f (A x) (mfderiv (𝓡 n) (𝓡 n) A x w)) = _
  rw [heq.self_of_nhds]
  exact hmetric _ _

end PoincareConjecture.M44
