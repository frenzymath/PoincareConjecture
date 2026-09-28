import PoincareConjecture.Proofs.M76.Mathlib.GenericAffineHeightExtrema
import PoincareConjecture.Proofs.M76.Mathlib.GraphHeightNeighbors
import PoincareConjecture.Proofs.M76.Mathlib.GraphLinkSublevels
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineHeightSigns











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]




theorem mem_both_height_closures_of_generic_nonvertex
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices)
    {x : E} (hx : x ∈ K.space) (hxv : x ∉ K.vertices) :
    x ∈ closure (K.space ∩ {y | A y < A x}) ∧
      x ∈ closure (K.space ∩ {y | A x < A y}) := by
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  have hverts : (s : Set E) ⊆ K.vertices := fun v hv =>
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  obtain ⟨p, hp, hmin⟩ := s.exists_min_image A (K.nonempty_of_mem_faces hs)
  obtain ⟨q, hq, hmax⟩ := s.exists_max_image A (K.nonempty_of_mem_faces hs)
  have hlo : A p ≤ A x := convexHull_min (fun v hv => hmin v hv)
    ((convex_Ici (A p)).affine_preimage A) hxs
  have hhi : A x ≤ A q := convexHull_min (fun v hv => hmax v hv)
    ((convex_Iic (A q)).affine_preimage A) hxs
  have hpstrict : A p < A x := by
    apply lt_of_le_of_ne hlo
    intro heq
    have hxp := s.eq_vertex_of_generic_affine_minimum A (hA.mono hverts)
      hp hmin hxs heq.symm
    exact hxv (hxp.symm ▸ hverts hp)
  have hqstrict : A x < A q := by
    apply lt_of_le_of_ne hhi
    intro heq
    have hnegA : InjOn (-A) (s : Set E) := fun _ hv _ hw h =>
      hA (hverts hv) (hverts hw) (neg_injective h)
    have hxq := s.eq_vertex_of_generic_affine_minimum (-A) hnegA hq
      (fun v hv => neg_le_neg (hmax v hv)) hxs (congrArg Neg.neg heq)
    exact hxv (hxq.symm ▸ hverts hq)
  have hface := K.convexHull_subset_space hs
  have hnegative := (convex_convexHull ℝ (s : Set E)).mem_closure_lower_affine_height A
    hxs (subset_convexHull ℝ _ hp) hpstrict
  have hpositive := (convex_convexHull ℝ (s : Set E)).mem_closure_upper_affine_height A
    hxs (subset_convexHull ℝ _ hq) hqstrict
  exact ⟨closure_mono (inter_subset_inter_left _ hface) hnegative,
    closure_mono (inter_subset_inter_left _ hface) hpositive⟩



theorem mem_lower_height_closure_of_adjacent_vertex
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    (p q : K.vertices) (hpq : K.vertexAbstractComplex.edgeGraph.Adj p q)
    (hheight : A q < A p) :
    (p : E) ∈ closure (K.space ∩ {y | A y < A p}) := by
  have hface : ({(p : E), (q : E)} : Finset E) ∈ K.faces := by
    have h := hpq.2
    change ({p, q} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces at h
    simpa only [Finset.map_insert, Finset.map_singleton,
      Function.Embedding.coe_subtype] using h
  have hp : (p : E) ∈ convexHull ℝ (↑({(p : E), (q : E)} : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
  have hq : (q : E) ∈ convexHull ℝ (↑({(p : E), (q : E)} : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  exact closure_mono (inter_subset_inter_left _ (K.convexHull_subset_space hface))
    ((convex_convexHull ℝ _).mem_closure_lower_affine_height A hp hq hheight)






theorem mem_both_height_closures_of_preconnected_sublevels
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A : E →ᵃ[ℝ] ℝ) (hA : InjOn A K.vertices)
    (hgraphs : ∀ c,
      (K.vertexAbstractComplex.edgeGraph.induce {v : K.vertices | A (v : E) < c}).Preconnected ∧
        (K.vertexAbstractComplex.edgeGraph.induce {v : K.vertices | c < A (v : E)}).Preconnected)
    {x p q : E} (hx : x ∈ K.space) (hp : p ∈ K.vertices) (hq : q ∈ K.vertices)
    (hpx : A p < A x) (hxq : A x < A q) :
    x ∈ closure (K.space ∩ {y | A y < A x}) ∧
      x ∈ closure (K.space ∩ {y | A x < A y}) := by
  by_cases hxv : x ∈ K.vertices
  · let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
    have hAv : Function.Injective (fun v : K.vertices => A v) :=
      fun v w h => Subtype.ext (hA v.property w.property h)
    obtain ⟨v, hxv', hv⟩ := K.vertexAbstractComplex.edgeGraph.exists_lower_neighbor_of_preconnected_sublevels
      (fun v : K.vertices => A v) hAv (fun c => (hgraphs c).1)
      (p := ⟨x, hxv⟩) (q := ⟨p, hp⟩) hpx
    have hneggraphs : ∀ c,
        (K.vertexAbstractComplex.edgeGraph.induce {v : K.vertices | -A (v : E) < c}).Preconnected := by
      intro c
      have hs : {v : K.vertices | -A (v : E) < c} =
          {v : K.vertices | -c < A (v : E)} := by
        ext v
        change (-A (v : E) < c) ↔ -c < A (v : E)
        exact neg_lt
      exact hs.symm ▸ (hgraphs (-c)).2
    obtain ⟨w, hxw, hw⟩ := K.vertexAbstractComplex.edgeGraph.exists_lower_neighbor_of_preconnected_sublevels
      (fun v : K.vertices => -A v) (fun v w h => hAv (neg_injective h)) hneggraphs
      (p := ⟨x, hxv⟩) (q := ⟨q, hq⟩) (neg_lt_neg hxq)
    refine ⟨K.mem_lower_height_closure_of_adjacent_vertex A ⟨x, hxv⟩ v hxv' hv, ?_⟩
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_neg_iff] using
      K.mem_lower_height_closure_of_adjacent_vertex (-A) ⟨x, hxv⟩ w hxw hw
  · exact K.mem_both_height_closures_of_generic_nonvertex A hA hx hxv

end Geometry.SimplicialComplex
