import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.MarkedRestriction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.CyclicModelOrder
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.BoundaryBasics
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SubcomplexFaceInclusion









set_option autoImplicit false

universe u v w

open Set Geometry StdSimplexCore
open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

theorem subcomplexVertexEmbedding_faces {K L : SimplicialComplex ℝ E} (hLK : L ≤ K)
    (t : Finset L.vertices) (ht : t ∈ L.vertexAbstractComplex.faces) :
    t.map (K.subcomplexVertexEmbedding L hLK) ∈ K.vertexAbstractComplex.faces := by
  change (t.map (K.subcomplexVertexEmbedding L hLK)).map (Function.Embedding.subtype _) ∈ K.faces
  rw [Finset.map_map]
  exact hLK ht



theorem barycentric_mem_subcomplex_face {K L : SimplicialComplex ℝ E}
    [Fintype K.vertices] (hLK : L ≤ K) (x : K.space) (hx : (x : E) ∈ L.space) :
    ∃ t ∈ L.vertexAbstractComplex.faces,
      (K.finiteBarycentricHomeomorph.symm x).val ∈
        barycentricFace (t.map (K.subcomplexVertexEmbedding L hLK)) := by
  classical
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨t, ht, hts⟩ := L.faces_eq_vertexAbstractComplex_images ▸ hs
  let f := K.subcomplexVertexEmbedding L hLK
  have himage : Subtype.val '' (↑(t.map f) : Set K.vertices) = (s : Set E) := by
    rw [Finset.coe_map, image_image, hts]
    rfl
  rw [← himage, ← image_barycentricFace ((↑) : K.vertices → E) (t.map f)] at hxs
  obtain ⟨q, hq, hqx⟩ := hxs
  have hqc : q ∈ K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace :=
    mem_iUnion₂.mpr ⟨t.map f, subcomplexVertexEmbedding_faces hLK t ht, hq⟩
  have heq : (K.finiteBarycentricHomeomorph.symm x).val = q := by
    apply K.injOn_barycentricMap_vertexComplex
      (K.finiteBarycentricHomeomorph.symm x).property hqc
    exact (congrArg Subtype.val (K.finiteBarycentricHomeomorph.apply_symm_apply x)).trans hqx.symm
  exact ⟨t, ht, heq.symm ▸ hq⟩

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  {Z : Type w} [TopologicalSpace Z]



theorem finrank_closed_le_coboundaries_add_one_of_marked_polygon
    (K L : SimplicialComplex ℝ E) [Fintype K.vertices] [Fintype L.vertices]
    (hL : L.faces.Finite) (hLK : L ≤ K)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) (hPL : P.boundary ℝ = L.space)
    {N D : Set X} (hDN : D ⊆ N)
    {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r D)
    (hr : ∀ x, r x ∈ D) {s : C(N, N)}
    (F : (ContinuousMap.id N).HomotopyRel s (Subtype.val ⁻¹' D))
    (hs : ∀ y, (s y : X) ∈ D) (J : N ≃ₜ K.space)
    (γ : C(Z, X)) (hγ : ∀ z, γ z ∈ D)
    (hmark : ∀ z, (J ⟨γ z, hDN (hγ z)⟩ : E) ∈ L.space)
    (hterminal : ∀ (Y : Type (max u v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → X),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
      ∀ lift : C(Z, Y), (∀ z, p (lift z) = γ z) → False) :
    Module.finrank (ZMod 2)
        (LinearMap.ker (edgeCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) ≤
      Module.finrank (ZMod 2) (LinearMap.range
        (vertexCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) + 1 := by
  classical
  have hconn : IsConnected L.space := by
    rw [← hPL]
    exact Poincare.Manifold.Schoenflies.Plane.polygon_boundary_isConnected P (by omega)
  exact PreAbstractSimplicialComplex.ModTwoEdgeCocycle.finrank_closed_le_coboundaries_add_one_of_marked_terminal
    K.vertexAbstractComplex L.vertexAbstractComplex (K.subcomplexVertexEmbedding L hLK)
    (subcomplexVertexEmbedding_faces hLK)
    (L.connected_edgeGraph_of_isConnected hL hconn)
    (L.polygon_carrier_two_neighbors hL P hP hPi hPL)
    hDN H hr F hs (K.finiteBarycentricHomeomorph.trans J.symm) γ hγ
    (fun z => barycentric_mem_subcomplex_face hLK _ (hmark z)) hterminal

end Geometry.SimplicialComplex
