import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PrimalDualSurfaceSphere
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PrimalDualTrees
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexTriangleIncidence
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceEulerValuation



set_option autoImplicit false
open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



theorem exists_sphere_model_of_surfaceEulerCount_eq_two
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (hconn : IsConnected K.space) (hcount : K.surfaceEulerCount = 2) :
    ∃ H : K.space ≃ₜ frontier (TriangularRoofModel.halfBall 1), H.IsFinitePL := by
  classical
  let : Fintype K.faces := hK.fintype
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  have htri := K.vertex_triangleGraph_connected
    (K.triangleGraph_connected_of_isConnected hK
      (fun s hs ↦ by
        obtain ⟨t, ht, htc, hst⟩ := hpure s hs
        exact ⟨t, ht, hst, htc⟩)
      hconn (fun p hp ↦ by simpa only [K.faceLink_singleton_eq_link] using hlinks p hp))
  have hcofaces' (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
      (triangleCofaces K.vertexAbstractComplex.toPreAbstractSimplicialComplex e).card = 2 := by
    rw [K.triangleCofaces_card_eq_original]
    exact hcofaces _ e.property.1 (by simpa only [Finset.card_map] using e.property.2)
  have hcount' : Nat.card K.vertices +
      Nat.card (Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex) =
      Nat.card (Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 := by
    rw [K.surfaceEulerCount_eq_vertex_counts] at hcount
    omega
  obtain ⟨T, hT, hprimal, hdual⟩ := K.vertexAbstractComplex.exists_primal_complementary_trees
    (K.connected_edgeGraph_of_isConnected hK hconn) hcofaces' htri hcount'
  exact K.exists_sphere_model_of_primal_complementary_trees hpure hcofaces hlinks
    T hT hprimal hdual

end Geometry.SimplicialComplex
