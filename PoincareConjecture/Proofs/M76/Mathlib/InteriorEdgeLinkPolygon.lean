import PoincareConjecture.Proofs.M76.Mathlib.InteriorFullCofaces
import PoincareConjecture.Proofs.M76.Mathlib.InteriorConnectedLinks
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension
import PoincareConjecture.Proofs.M76.Mathlib.PureEdgeComplexPolygon

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_polygon_faceLink_of_interior_edge
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (h3 : Module.finrank ℝ E = 3) {s : Finset E}
    (hs : s ∈ K.faces) (hscard : s.card = 2)
    (hmeet : (convexHull ℝ (s : Set E) ∩ interior K.space).Nonempty) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = (K.faceLink s).space := by
  classical
  let L := K.faceLink s
  have hL : L.faces.Finite := finite_faceLink_faces hK s
  have hcoface_meet {t : Finset E} (hst : s ⊆ t) :
      (convexHull ℝ (t : Set E) ∩ interior K.space).Nonempty := by
    obtain ⟨x, hxs, hxint⟩ := hmeet
    exact ⟨x, convexHull_mono hst hxs, hxint⟩
  have hpure : ∀ t ∈ L.faces, ∃ u ∈ L.faces, u.card = 2 ∧ t ⊆ u := by
    intro t ht
    obtain ⟨u, hu, hstu, hucard⟩ := K.exists_full_coface_of_hull_meets_interior
      hK ht.2.2 (hcoface_meet Finset.subset_union_left)
    have hsu : s ⊆ u := Finset.subset_union_left.trans hstu
    have hcard : (u \ s).card = 2 := by
      rw [Finset.card_sdiff_of_subset hsu, hucard, h3, hscard]
    have hne : (u \ s).Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨u \ s, ⟨K.down_closed hu Finset.sdiff_subset hne, ?_, ?_⟩, hcard, ?_⟩
    · exact Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx)
    · simpa only [Finset.union_sdiff_of_subset hsu] using hu
    · intro x hx
      exact Finset.mem_sdiff.mpr ⟨hstu (Finset.mem_union_right s hx),
        fun hxs => Finset.disjoint_left.mp ht.2.1 hxs hx⟩
  have hconn : IsConnected L.space := by
    apply K.isConnected_faceLink_of_hull_meets_interior hK hs _ hmeet
    rw [K.finrank_faceDirection_of_card hs (show s.card = 1 + 1 from hscard), h3]
    norm_num
  have hdegree (v : L.vertices) :
      (L.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2 := by
    rw [K.ncard_faceLink_edgeGraph_neighborSet s v]
    apply K.faceLink_ncard_eq_two_of_hull_meets_interior hK v.property.2.2 _
      (hcoface_meet Finset.subset_union_left)
    have hv : v.val ∉ s := (K.faceLink_vertices_subset s v.property).2
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hv, hscard, h3]
  exact L.exists_polygon_of_pure_edges hL hpure
    (L.connected_edgeGraph_of_isConnected hL hconn) hdegree

end Geometry.SimplicialComplex
