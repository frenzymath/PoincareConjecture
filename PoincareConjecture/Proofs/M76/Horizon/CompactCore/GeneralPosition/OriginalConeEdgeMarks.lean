import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.ConeEdges
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeMarks
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.PlanarTriangleBoundaryComplex









set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem original_cone_edges_have_unmarked_vertices
    (K R T : SimplicialComplex ℝ E) (hdim : Module.finrank ℝ E = 2)
    (L C : {s : K.faces // s.val.card = 3} → SimplicialComplex ℝ E)
    (Q : {s : K.faces // s.val.card = 2} → SimplicialComplex ℝ E)
    (hLR : ∀ s, L s ≤ R)
    (hLS : ∀ s, (L s).space = frontier (convexHull ℝ (s.val.val : Set E)))
    (hQR : ∀ s, Q s ≤ R)
    (hQS : ∀ s, (Q s).space = convexHull ℝ (s.val.val : Set E))
    (hfaces : T.faces = ⋃ s, (C s).faces)
    (hcone : ∀ s z, z ∈ (C s).faces ↔ z.Nonempty ∧
      (z.erase (s.val.val.centroid ℝ id) = ∅ ∨
        z.erase (s.val.val.centroid ℝ id) ∈ (L s).faces))
    (g0 g : E → X) (F : Set X)
    (hboundary : ∀ s : {s : K.faces // s.val.card = 3},
      EqOn g g0 (frontier (convexHull ℝ (s.val.val : Set E))))
    (hapex : ∀ s : {s : K.faces // s.val.card = 3}, g (s.val.val.centroid ℝ id) ∉ F)
    (hvertices : ∀ x ∈ K.vertices, g0 x ∉ F)
    (hcrossing : ∀ s ∈ K.faces, s.card = 2 →
      ∀ x ∈ convexHull ℝ (s : Set E), g0 x ∈ F →
      ∀ y ∈ convexHull ℝ (s : Set E), g0 y ∈ F → x = y) :
    ∀ z ∈ T.faces, z.card = 2 → ∃ x ∈ z, g x ∉ F := by
  intro z hz hcard
  rw [hfaces] at hz
  obtain ⟨s, hs⟩ := mem_iUnion.mp hz
  apply (L s).cone_edge_has_unmarked_vertex (C s) (hcone s) (g ⁻¹' F) (hapex s) _ z hs hcard
  obtain ⟨J, hJ, hJK, hJS, _, hJdim, _⟩ :=
    K.exists_planar_triangle_boundary_complex hdim s.val.property s.property
  let QJ : {e : J.faces // e.val.card = 2} → SimplicialComplex ℝ E :=
    fun e => Q ⟨⟨e.val.val, hJK e.val.property⟩, e.property⟩
  have hJvertices : Disjoint J.vertices (g ⁻¹' F) := by
    apply disjoint_left.mpr
    intro x hx hxF
    have hxS : x ∈ J.space := J.vertices_subset_space hx
    have hxK : x ∈ K.vertices := hJK hx
    exact hvertices x hxK (by rwa [← hboundary s (hJS.subset hxS)])
  apply J.refined_boundary_edge_has_unmarked_vertex R (L s) hJ hJdim (hLR s)
    ((hLS s).trans hJS.symm) QJ (fun e => hQR _) (fun e => hQS _) (g ⁻¹' F) hJvertices
  intro e he hecard x hx hxF y hy hyF
  refine hcrossing e (hJK he) hecard x hx ?_ y hy ?_
  · rwa [← hboundary s (hJS.subset (J.convexHull_subset_space he hx))]
  · rwa [← hboundary s (hJS.subset (J.convexHull_subset_space he hy))]

end PoincareConjecture.M76
