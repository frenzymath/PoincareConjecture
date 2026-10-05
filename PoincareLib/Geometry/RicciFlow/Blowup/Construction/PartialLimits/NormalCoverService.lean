import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.IndexedCovering
import PoincareLib.Geometry.Riemannian.Measure.Basic

/-!
# The exact lower local normal-cover obligation

Morgan--Tian Theorem 5.6, pp. 85--87, and Theorem 5.9, pp. 88--89.
This proposition is the telescope of M28's settled
`exists_uniform_normalCover_of_local_noncollapse` in
`Thm5_6_PartialLimits/Geometry/UniformNormalCover.lean`, inspected at
commit `5fa290fccc1e42ab9dd9d04066295fcabc99a8ce`.
It has no local inhabitant before that library is promoted to main.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareMT.M30

/-- The precise universe-polymorphic local normal-cover factory of
Theorem 5.6, pp. 85--87. This is an explicit unfilled lower-library input,
not a change to the frozen M30 hypotheses. -/
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

end PoincareMT.M30
