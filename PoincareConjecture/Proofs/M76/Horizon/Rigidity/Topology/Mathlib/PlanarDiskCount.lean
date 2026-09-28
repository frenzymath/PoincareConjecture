import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.PlanarTriangleCycles
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceEulerValuation
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleIncidenceRanks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.CocycleExactnessOfContractions

set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem surfaceEulerCount_eq_one_of_planar_contractible
    (K : SimplicialComplex ℝ E) (hdim : Module.finrank ℝ E = 2)
    (hK : K.faces.Finite) [ContractibleSpace K.space] :
    K.surfaceEulerCount = 1 := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  have hconn : IsConnected K.space := isConnected_iff_connectedSpace.mpr inferInstance
  have hcount := K.vertexAbstractComplex.triangle_incidence_count_of_exact
    (K.connected_edgeGraph_of_isConnected hK hconn) K.edge_exact_of_contractible
  rw [K.boundary2_ker_eq_bot_of_planar hdim hK] at hcount
  simp only [finrank_bot, add_zero] at hcount
  rw [K.surfaceEulerCount_eq_vertex_counts]
  omega

end Geometry.SimplicialComplex
