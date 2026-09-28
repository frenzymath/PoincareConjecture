import PoincareConjecture.Proofs.Ch01.Koszul
import PoincareConjecture.Proofs.M03.ConnectionConstruction











set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture


theorem exists_leviCivitaData {n : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : Nonempty (LeviCivitaData g) := by
  exact Proofs.M03.leviCivitaData_nonempty g

end PoincareConjecture
