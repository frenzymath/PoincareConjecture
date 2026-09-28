import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.FiniteSurface










set_option autoImplicit false
open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

open Classical in
theorem surfaceEulerCount_nonneg_of_isCyclic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hconn : IsConnected K.space)
    (x : K.space) [IsCyclic (FundamentalGroup K.space x)] :
    0 ≤ K.surfaceEulerCount := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  have hbound := K.incidence_rank_le_one_of_isCyclic hK hconn x
  have h0 := (vertexCoboundary A).finrank_range_add_finrank_ker
  rw [K.vertexAbstractComplex.finrank_ker_vertexCoboundary
    (K.connected_edgeGraph_of_isConnected hK hconn), Module.finrank_pi] at h0
  have h1 := (edgeCoboundary A).finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at h1
  have h2 := (edgeCoboundary A).dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range,
    Subspace.dual_finrank_eq, Module.finrank_pi] at h2
  rw [K.surfaceEulerCount_eq_vertex_counts]
  simp only [Nat.card_eq_fintype_card, A] at h0 h1 h2 hbound ⊢
  omega

end Geometry.SimplicialComplex
