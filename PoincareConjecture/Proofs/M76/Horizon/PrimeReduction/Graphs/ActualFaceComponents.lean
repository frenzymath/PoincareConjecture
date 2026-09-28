import PoincareConjecture.Proofs.M76.PrimeReduction.ActualArcComponents
import PoincareConjecture.Proofs.M76.Mathlib.GeometricCyclePolygons
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Mathlib.SimplexExtremeFaces
import Mathlib.Topology.Connected.TotallyDisconnected










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]



theorem mem_vertices_of_finite_simplex_frontier_contact
    (G : SimplicialComplex ℝ E) (hdim : ∀ s ∈ G.faces, s.card ≤ 2)
    (t : Finset E) (ht : t.Nonempty)
    (hind : AffineIndependent ℝ ((↑) : t → E))
    (hsub : G.space ⊆ convexHull ℝ (t : Set E))
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))).Finite)
    {x : E} (hxG : x ∈ G.space)
    (hxf : x ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) : x ∈ G.vertices := by
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxG
  have hpos := Finset.card_pos.mpr (G.nonempty_of_mem_faces hs)
  have hle := hdim s hs
  by_cases hs1 : s.card = 1
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hs1
    have hxv : x = v := by simpa only [Finset.coe_singleton, convexHull_singleton,
      mem_singleton_iff] using hxs
    exact hxv.symm ▸ hs
  · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
    have huG : u ∈ G.vertices := G.face_subset_vertices hs (by simp)
    have hvG : v ∈ G.vertices := G.face_subset_vertices hs (by simp)
    by_cases hxu : x = u
    · exact hxu.symm ▸ huG
    by_cases hxv : x = v
    · exact hxv.symm ▸ hvG
    have hxseg : x ∈ openSegment ℝ u v := mem_openSegment_of_ne_left_right (Ne.symm hxu) (Ne.symm hxv)
      (by simpa only [Finset.coe_pair, convexHull_pair] using hxs)
    obtain ⟨i, hi, hxi⟩ := (hind.mem_intrinsicFrontier_convexHull_finset ht x).mp hxf
    have hext := hind.isExtreme_convexHull_finset_subset (Finset.erase_subset i t)
    have huC := hsub (G.vertices_subset_space huG)
    have hvC := hsub (G.vertices_subset_space hvG)
    have hui := hext.left_mem_of_mem_openSegment huC hvC hxi hxseg
    have hvi := hext.right_mem_of_mem_openSegment huC hvC hxi hxseg
    have hsegG : segment ℝ u v ⊆ G.space := by
      simpa only [Finset.coe_pair, convexHull_pair] using G.convexHull_subset_space hs
    have hsegf : segment ℝ u v ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) :=
      ((convex_convexHull ℝ _).segment_subset hui hvi).trans
        (hind.convexHull_subset_intrinsicFrontier (Finset.erase_ssubset hi))
    have hsegfin : (segment ℝ u v).Finite :=
      hfinite.subset (fun y hy => ⟨hsegG hy, hsegf hy⟩)
    have hsingle := (convex_segment u v).isPreconnected.isDiscrete_iff_subsingleton.mp
      hsegfin.isDiscrete
    exact (huv (hsingle (left_mem_segment ℝ u v) (right_mem_segment ℝ u v))).elim



theorem actual_component_frontier_eq_degree_one_vertices
    (G : SimplicialComplex ℝ E) (hdim : ∀ s ∈ G.faces, s.card ≤ 2)
    (t : Finset E) (ht : t.Nonempty)
    (hind : AffineIndependent ℝ ((↑) : t → E))
    (hsub : G.space ⊆ convexHull ℝ (t : Set E))
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))).Finite)
    (hinterior : ∀ v : G.vertices, (v : E) ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices, (v : E) ∉ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) =
      Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} := by
  classical
  let H := G.vertexAbstractComplex.edgeGraph
  have hdegree (v : G.vertices) : (H.neighborSet v).ncard = 1 ∨ (H.neighborSet v).ncard = 2 := by
    by_cases hv : (v : E) ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E))
    · exact Or.inr (hinterior v hv)
    · exact Or.inl (hexterior v hv)
  have hne (v : G.vertices) : (H.neighborSet v).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rcases hdegree v with h | h <;> omega)
  have hcarrier : H.segmentCarrier ((↑) : G.vertices → E) = G.space :=
    G.actual_edgeGraph_segmentCarrier_eq_space hdim hne
  have hcomp : C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ⊆ G.space := by
    rintro x ⟨v, w, hvw, hx⟩
    exact hcarrier.subset ⟨v.val, w.val, hvw, hx⟩
  have hfrontier (v : G.vertices) :
      (v : E) ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ↔
        (H.neighborSet v).ncard = 1 := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    constructor
    · intro hv
      exact hexterior v hv.2
    · intro hv
      refine ⟨subset_intrinsicClosure (hsub (G.vertices_subset_space v.property)), ?_⟩
      intro hi
      have htwo := hinterior v hi
      change (H.neighborSet v).ncard = 2 at htwo
      omega
  ext x
  constructor
  · rintro ⟨hxC, hxf⟩
    have hxv := G.mem_vertices_of_finite_simplex_frontier_contact hdim t ht hind hsub hfinite
      (hcomp hxC) hxf
    obtain ⟨v, w, hvw, hx⟩ := hxC
    have hs : ({(v.val : E), (w.val : E)} : Finset E) ∈ G.faces := by
      have h := hvw.2
      change ({v.val, w.val} : Finset G.vertices).map (Function.Embedding.subtype _) ∈ G.faces at h
      simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using h
    have hxm : x ∈ ({(v.val : E), (w.val : E)} : Finset E) :=
      (G.vertex_mem_convexHull_iff hxv hs).mp
        (by simpa only [Finset.coe_pair, convexHull_pair] using hx)
    have hxC' : (⟨x, hxv⟩ : G.vertices) ∈ C.supp := by
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hxm :
        x = (v.val : E) ∨ x = (w.val : E)) with hxv' | hxw'
      · have he : (⟨x, hxv⟩ : G.vertices) = v.val := Subtype.ext hxv'
        exact he.symm ▸ v.property
      · have he : (⟨x, hxv⟩ : G.vertices) = w.val := Subtype.ext hxw'
        exact he.symm ▸ w.property
    exact ⟨⟨x, hxv⟩, ⟨hxC', (hfrontier ⟨x, hxv⟩).mp hxf⟩, rfl⟩
  · rintro ⟨v, ⟨hvC, hvone⟩, rfl⟩
    obtain ⟨w, hvw⟩ := hne v
    have hwC := C.mem_supp_of_adj_mem_supp hvC hvw
    exact ⟨⟨⟨v, hvC⟩, ⟨w, hwC⟩, hvw, left_mem_segment ℝ _ _⟩,
      (hfrontier v).mpr hvone⟩





theorem exists_actual_face_components
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite)
    (hdim : ∀ s ∈ G.faces, s.card ≤ 2)
    (t : Finset E) (ht : t.Nonempty)
    (hind : AffineIndependent ℝ ((↑) : t → E))
    (hsub : G.space ⊆ convexHull ℝ (t : Set E))
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))).Finite)
    (hinterior : ∀ v : G.vertices, (v : E) ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices, (v : E) ∉ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) :
    G.space = ⋃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∧
    Pairwise (fun C D : G.vertexAbstractComplex.edgeGraph.ConnectedComponent =>
      Disjoint (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)))
        (D.toSimpleGraph.segmentCarrier (fun v => (v.val : E)))) ∧
    ∀ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∃ (n : ℕ) (e : Fin (n + 2) ≃ C),
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) =
          Polygon.pathCarrier (fun i => ((e i).val : E)) ∧
        IsFinitePLBallPair ℝ (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)))
          (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∩
            intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) ∧
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∩
            intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) =
          {((e 0).val : E), ((e (Fin.last (n + 1))).val : E)} ∧
        ∀ v w : C, C.toSimpleGraph.Adj v w ↔ ∃ i : Fin (n + 1),
          (e i.castSucc = v ∧ e i.succ = w) ∨
          (e i.castSucc = w ∧ e i.succ = v)) ∨
      (∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧ P.HasSimplicialEdges ∧
        P.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∧
        P.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (t : Set E))) := by
  classical
  let : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  let H := G.vertexAbstractComplex.edgeGraph
  have hdegree (v : G.vertices) : (H.neighborSet v).ncard = 1 ∨ (H.neighborSet v).ncard = 2 := by
    by_cases hv : (v : E) ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E))
    · exact Or.inr (hinterior v hv)
    · exact Or.inl (hexterior v hv)
  have hne (v : G.vertices) : (H.neighborSet v).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rcases hdegree v with h | h <;> omega)
  have hcarrier : H.segmentCarrier ((↑) : G.vertices → E) = G.space :=
    G.actual_edgeGraph_segmentCarrier_eq_space hdim hne
  have hcomp (C : H.ConnectedComponent) :
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ⊆ G.space := by
    rintro x ⟨v, w, hvw, hx⟩
    exact hcarrier.subset ⟨v.val, w.val, hvw, hx⟩
  have hboundary (C : H.ConnectedComponent) :
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) ∩
          intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) =
        Subtype.val '' {v : G.vertices | v ∈ C.supp ∧ (H.neighborSet v).ncard = 1} :=
    G.actual_component_frontier_eq_degree_one_vertices hdim t ht hind hsub hfinite
      hinterior hexterior C
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcarrier]
    exact H.segmentCarrier_eq_iUnion_components _
  · exact H.pairwise_disjoint_component_segmentCarrier ((↑) : G.vertices → E)
      Subtype.val_injective (fun {_ _ _ _} hvw hab => G.actual_edgeGraph_segment_intersection hvw hab)
  · intro C
    by_cases hleaf : ∃ v : C, (H.neighborSet v.val).ncard = 1
    · left
      obtain ⟨n, e, he, hball, hends, hlabels⟩ := G.exists_actual_component_interval hG
        (fun v => by
          change (H.neighborSet v).ncard ≤ 2
          rcases hdegree v with h | h <;> omega) C hleaf
      have hrim := (hboundary C).trans hends
      exact ⟨n, e, he, hrim.symm ▸ hball, hrim, hlabels⟩
    · right
      have htwo (v : C) : (C.toSimpleGraph.neighborSet v).ncard = 2 := by
        rw [C.ncard_neighborSet H]
        exact (hdegree v.val).resolve_left (fun hv => hleaf ⟨v, hv⟩)
      obtain ⟨n, P, hPi, hP, hPs⟩ := C.toSimpleGraph.exists_polygon_of_two_neighbors
        (fun v => (v.val : E)) C.connected_toSimpleGraph htwo
        (Subtype.val_injective.comp Subtype.val_injective)
        (fun {_ _ _ _} hvw hab => G.actual_edgeGraph_segment_intersection hvw hab)
      refine ⟨n, P, hPi, hP, hPs, ?_⟩
      intro x hx
      have hxC : x ∈ C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) := hPs.subset hx
      by_contra hxnot
      have hxf : x ∈ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) := by
        rw [← intrinsicClosure_sdiff_intrinsicInterior]
        exact ⟨subset_intrinsicClosure (hsub (hcomp C hxC)), hxnot⟩
      obtain ⟨v, ⟨hvC, hvone⟩, _⟩ := (hboundary C).subset ⟨hxC, hxf⟩
      exact hleaf ⟨⟨v, hvC⟩, hvone⟩

end Geometry.SimplicialComplex
