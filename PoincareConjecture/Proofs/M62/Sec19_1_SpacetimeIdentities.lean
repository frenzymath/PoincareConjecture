import PoincareConjecture.Statements.M62Geometry
import PoincareConjecture.Proofs.M62.Sec19_1_SpacetimeMetric
import PoincareConjecture.Proofs.M62.Sec19_1_TimeSpatialPairing
import PoincareConjecture.Proofs.M62.Sec19_1_Gauss
import PoincareConjecture.Proofs.M62.Sec19_1_Codazzi










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



theorem SpacetimeData.identities {F : RicciFlow n M (Set.Icc a b)}
    (G : SpacetimeData F) : SpacetimeIdentities G where
  time_smooth := G.charts.timeVector_smooth
  time_unit := G.time_unit
  time_parallel_time := G.time_parallel_time
  spatial_connection := G.spatial_connection
  spatial_time_vertical := fun q V => G.time_covariant_vertical q (G.charts.horizontal q V)
  spatial_time_pairing := G.spatial_time_pairing
  time_spatial_vertical := G.time_spatial_vertical
  time_spatial_pairing := G.time_spatial_pairing
  gauss := G.gauss
  codazzi := G.codazzi



theorem exists_spacetimeData [T2Space M] [SecondCountableTopology M]
    (F : RicciFlow n M (Set.Icc a b)) :
    ∃ G : SpacetimeData F, SpacetimeIdentities G := by
  obtain ⟨C⟩ := nonempty_spacetimeCharts (n := n) (M := M) a b
  obtain ⟨G⟩ := nonempty_spacetimeData_of_charts F C
  exact ⟨G, G.identities⟩

end PoincareConjecture.M62
