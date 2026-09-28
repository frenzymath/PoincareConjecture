import PoincareConjecture.Proofs.M01.NormalizationMetric
import PoincareConjecture.Definitions.Ch01.Curvature









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m01RescaledMetric_curvatureTensor
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c : ℝ) (hc : 0 < c) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    (m01RescaledMetric_connection g D c hc).curvatureTensor x u v w z =
      c * D.curvatureTensor x u v w z := by
  unfold LeviCivitaData.curvatureTensor
  rw [m01RescaledMetric_inner]
  rfl

end PoincareConjecture
