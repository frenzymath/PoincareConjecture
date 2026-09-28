import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.EulerParity
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.GeometricCofaceSigns
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.BoundaryEulerBound









set_option autoImplicit false
open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains
open AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
theorem even_surfaceEulerCount_of_geometric_signs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1) :
    Even K.surfaceEulerCount := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let KA := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let v : K.vertices ↪ E := Function.Embedding.subtype _
  let label : K.vertices ↪ ℕ :=
    ⟨fun x ↦ number x, fun x y h ↦ Subtype.ext (hnumber x.property y.property h)⟩
  let sigma : Triangle KA → ZMod 2 := fun t ↦ sign (t.val.map v)
  have hc (t u : Triangle KA) (htu : t ≠ u) (s : Edge KA)
      (hst : s.val ⊆ t.val) (hsu : s.val ⊆ u.val) :
      (sigma t + boundaryFaceParity label t.val s.val) +
        (sigma u + boundaryFaceParity label u.val s.val) = 1 := by
    have h := hcancel _ t.property.1 (by simpa using t.property.2)
      _ u.property.1 (by simpa using u.property.2)
      (fun h ↦ htu (Subtype.ext (Finset.map_injective v h)))
      (s.val.map v) (by simpa using s.property.2)
      (Finset.map_subset_map.mpr hst) (Finset.map_subset_map.mpr hsu)
    simp only [v, PoincareConjecture.M76.Dehn.boundaryFaceParity_map] at h
    convert! h
  have htwo (e : Edge KA) : (triangleCofaces KA e).card = 2 := by
    rw [K.triangleCofaces_card_eq_original]
    exact hcofaces _ e.property.1 (by simpa only [Finset.card_map] using e.property.2)
  have hl (x : K.vertices) :
      (K.faceLink {x.val}).vertexAbstractComplex.edgeGraph.Preconnected := by
    apply ((K.faceLink {x.val}).connected_edgeGraph_of_isConnected
      (K.finite_faceLink_faces hK _) ?_).preconnected
    simpa only [K.faceLink_singleton_eq_link] using hlinks x.val x.property
  obtain ⟨k, hk⟩ := K.even_euler_count_of_all_edge_signs
    (fun s hs ↦ by obtain ⟨t, ht, hc, hst⟩ := hpure s hs; exact ⟨t, ht, hst, hc⟩)
    (fun x ↦ by convert! hl x) label sigma
    (by intro t u htu s hst hsu; convert! hc t u htu s hst hsu) htwo
  rw [K.surfaceEulerCount_eq_vertex_counts]
  refine ⟨(k : ℤ) - Nat.card (Edge KA), ?_⟩
  simp only [Nat.card_eq_fintype_card, KA] at hk ⊢
  omega

open Classical in
theorem closed_surface_incidence_rank_identity
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) :
    letI : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
    let KA := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
    K.surfaceEulerCount + (Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary KA)) : ℤ) =
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary KA)) + 2 := by
  classical
  dsimp only
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let KA := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  have htri := K.vertex_triangleGraph_connected
    (K.triangleGraph_connected_of_isConnected hK
      (fun s hs ↦ by obtain ⟨t, ht, hc, hst⟩ := hpure s hs; exact ⟨t, ht, hst, hc⟩)
      hconn (fun v hv ↦ by simpa only [K.faceLink_singleton_eq_link] using hlinks v hv))
  have htwo (e : Edge KA) : (triangleCofaces KA e).card = 2 := by
    rw [K.triangleCofaces_card_eq_original]
    exact hcofaces _ e.property.1 (by simpa only [Finset.card_map] using e.property.2)
  have h0 := (vertexCoboundary KA).finrank_range_add_finrank_ker
  rw [K.vertexAbstractComplex.finrank_ker_vertexCoboundary
    (K.connected_edgeGraph_of_isConnected hK hconn), Module.finrank_pi] at h0
  have h1 := (edgeCoboundary KA).finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at h1
  have h2 := (edgeCoboundary KA).dualMap.finrank_range_add_finrank_ker
  rw [finrank_boundary2_ker_of_two_cofaces KA htwo htri,
    LinearMap.finrank_range_dualMap_eq_finrank_range,
    Subspace.dual_finrank_eq, Module.finrank_pi] at h2
  rw [K.surfaceEulerCount_eq_vertex_counts]
  simp only [Nat.card_eq_fintype_card, KA] at h0 h1 h2 ⊢
  omega

open Classical in
theorem closed_surface_rank_ge_two_of_geometric_signs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (hne : K.surfaceEulerCount ≠ 2) :
    letI : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
    let KA := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
    K.surfaceEulerCount ≤ 0 ∧
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary KA)) + 2 ≤
        Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary KA)) := by
  classical
  have hle := K.surfaceEulerCount_le_two_sub_boundary_circle_count hK hpure hconn hlinks
    (fun i : Empty ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim)
    (fun i ↦ i.elim) (fun i ↦ i.elim)
    (by intro s hs hc; simpa using hcofaces s hs hc)
  norm_num at hle
  obtain ⟨k, hk⟩ := K.even_surfaceEulerCount_of_geometric_signs hK hpure hlinks
    hcofaces number hnumber sign hcancel
  have hnonpos : K.surfaceEulerCount ≤ 0 := by omega
  have hrank := K.closed_surface_incidence_rank_identity hK hpure hconn hlinks hcofaces
  exact ⟨hnonpos, by dsimp only at hrank ⊢; omega⟩

end Geometry.SimplicialComplex
