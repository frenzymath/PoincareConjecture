import PoincareConjecture.Proofs.M76.Dehn.Mathlib.CocycleExactnessOfContractions
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleIncidenceRanks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.CountTwoSphere
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteCarrierLocalPathConnected

set_option autoImplicit false
open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem surfaceEulerCount_eq_two_of_simplyConnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    [SimplyConnectedSpace K.space] :
    K.surfaceEulerCount = 2 := by
  classical
  let : LocallyPathConnectedSpace K.space := K.locallyPathConnectedSpace_of_finite hK
  let : Fintype K.faces := hK.fintype
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  have hconn : IsConnected K.space := isConnected_iff_connectedSpace.mpr inferInstance
  have htri := K.vertex_triangleGraph_connected
    (K.triangleGraph_connected_of_isConnected hK
      (fun s hs => by
        obtain ⟨t, ht, htc, hst⟩ := hpure s hs
        exact ⟨t, ht, hst, htc⟩)
      hconn (fun p hp => by simpa only [K.faceLink_singleton_eq_link] using hlinks p hp))
  have hcofaces' (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
      (triangleCofaces K.vertexAbstractComplex.toPreAbstractSimplicialComplex e).card = 2 := by
    rw [K.triangleCofaces_card_eq_original]
    exact hcofaces _ e.property.1 (by simpa only [Finset.card_map] using e.property.2)
  have hcount := K.vertexAbstractComplex.triangle_incidence_count_of_two_cofaces
    (K.connected_edgeGraph_of_isConnected hK hconn) K.edge_exact_of_simplyConnected
    hcofaces' htri
  rw [K.surfaceEulerCount_eq_vertex_counts]
  omega

theorem surfaceEulerCount_eq_one_of_simplyConnected_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard ≤ 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (hboundary : ∃ e ∈ K.faces, e.card = 2 ∧
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 1)
    [SimplyConnectedSpace K.space] :
    K.surfaceEulerCount = 1 := by
  classical
  let : LocallyPathConnectedSpace K.space := K.locallyPathConnectedSpace_of_finite hK
  let : Fintype K.faces := hK.fintype
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  have hconn : IsConnected K.space := isConnected_iff_connectedSpace.mpr inferInstance
  have htri := K.vertex_triangleGraph_connected
    (K.triangleGraph_connected_of_isConnected hK
      (fun s hs => by
        obtain ⟨t, ht, htc, hst⟩ := hpure s hs
        exact ⟨t, ht, hst, htc⟩)
      hconn (fun p hp => by simpa only [K.faceLink_singleton_eq_link] using hlinks p hp))
  have hcofaces' (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
      (triangleCofaces K.vertexAbstractComplex.toPreAbstractSimplicialComplex e).card ≤ 2 := by
    rw [K.triangleCofaces_card_eq_original]
    exact hcofaces _ e.property.1 (by simpa only [Finset.card_map] using e.property.2)
  have hboundary' : ∃ e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
      (triangleCofaces K.vertexAbstractComplex.toPreAbstractSimplicialComplex e).card = 1 := by
    obtain ⟨s, hs, hsc, hcount⟩ := hboundary
    refine ⟨(K.vertexFaceEquiv 2).symm ⟨s, hs, hsc⟩, ?_⟩
    rw [K.triangleCofaces_card_eq_original, K.vertexFaceEquiv_symm_map]
    exact hcount
  have hcount := K.vertexAbstractComplex.triangle_incidence_count_of_one_coface
    (K.connected_edgeGraph_of_isConnected hK hconn) K.edge_exact_of_simplyConnected
    hcofaces' htri.preconnected hboundary'
  rw [K.surfaceEulerCount_eq_vertex_counts]
  omega

end PoincareConjecture.M76.HamiltonIntervalTorus
