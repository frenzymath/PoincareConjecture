import PoincareLib.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-! Source: Mapher06/Poincare-MorganTian, `PoincareMT/Definitions/Ch01/RiemannianMetric.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Only imports and module placement are changed.
See `references/ricci-flow/mapher/shared-foundations.json`. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- A smooth torsion-free connection compatible with the specified metric.

This retains actual connection data and makes no existence or uniqueness claim.
Geometric uniqueness must be stated on sufficiently regular sections or germs.
-/
structure LeviCivitaData (g : RiemannianMetric n M) where
  /-- The covariant derivative, applied as `connection Y x (X x)` for ∇_X Y. -/
  connection : CovariantDerivative (𝓡 n) (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _)
  /-- The connection maps smooth sections to smooth covariant derivatives. -/
  smooth : CovariantDerivative.ContMDiffCovariantDerivative connection ∞
  /-- The torsion tensor vanishes. -/
  torsion_eq_zero : connection.torsion = 0
  /-- Differentiating the chosen metric obeys the metric-compatibility identity. -/
  metricCompatible :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    connection.IsMetricCompatible

end PoincareMT
