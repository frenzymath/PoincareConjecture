import PoincareLib.Geometry.Riemannian.Connection
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Ported from Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/M13MetricHomothety.lean`,
revision `49331b7d7ecad38f53e4300c3b35d6a84b2cc648`.
Declaration bodies are unchanged; only imports and module placement differ. -/

/-!
# Metric homotheties through an actual diffeomorphism

Morgan-Tian Definition 1.1, pp. 3-4, and Definition 3.40, p. 61. This
predicate fixes both smooth metrics and the actual comparison map. The
positive-scale calculus and rescaled spacetime construction are separate
M13 theorem outputs.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareMT

/-- The target metric pulls back to the given constant multiple of the source
metric, using the actual differential of the supplied diffeomorphism. -/
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

end PoincareMT
