import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Connection.KoszulFunctional
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Connection.Riesz
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Normalization.Connection.Smoothness
import PoincareConjecture.Proofs.M01.ConnectionExistence

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

theorem normalization_exists_leviCivitaData {n : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : Nonempty (LeviCivitaData g) :=
  m01_exists_leviCivitaData g

end PoincareConjecture
