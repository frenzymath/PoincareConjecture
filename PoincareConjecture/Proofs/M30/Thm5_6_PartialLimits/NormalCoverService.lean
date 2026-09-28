import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.IndexedCovering
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.M30

def UniformNormalCoverService : Prop :=
  ∀ (n : ℕ) {K δ v V : ℝ}, 1 ≤ n → 0 ≤ K → 0 < δ → 0 < v → 0 ≤ V →
    ∃ R ρ : ℝ, ∃ N : ℕ, 0 < ρ ∧ 2 * ρ < R ∧ R < δ ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [SecondCountableTopology M] [PreconnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
        (r S : ℝ), 0 < r → r + 2 * δ ≤ S →
        IsCompact (closure (g.ball p S)) →
        (∀ x ∈ g.ball p S, D.curvatureTensorNorm x ≤ K) →
        (∀ q ∈ g.ball p r, ENNReal.ofReal v ≤ g.volumeMeasure (g.ball q δ)) →
        g.volumeMeasure (g.ball p S) ≤ ENNReal.ofReal V →
        Nonempty (NormalChartCover (fun _ => g) p (-1) 1 r R ρ (1 / 4) (9 / 4) N)

end PoincareConjecture.M30
