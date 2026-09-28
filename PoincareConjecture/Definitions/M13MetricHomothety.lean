import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.Diffeomorph










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture



def MetricHomothety {n : ℕ} {M : Type u} {N : Type v}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
    h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v) =
      Q * g.inner x u v

end PoincareConjecture
