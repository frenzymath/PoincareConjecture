import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.IndependentFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.GeneralBoundaryFans








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface


theorem mesh_frontier_nonvertex_mem_open_edge (M : TriangleMesh) (t : M.Triangle)
    {q : Plane} (hq : q ∈ frontier (convexHull ℝ (range (meshTriangleBasis M t))))
    (hnew : q ∉ range (meshTriangleBasis M t)) :
    ∃ a ∈ t.1, ∃ b ∈ t.1, a ≠ b ∧ q ∈ openSegment ℝ (M.position a) (M.position b) := by
  rw [frontier_convexHull_affineBasis_fin3_segments] at hq
  obtain ⟨k, hk⟩ := mem_iUnion.mp hq
  rw [affineSegment_eq_segment] at hk
  have hopen := mem_openSegment_of_ne_left_right
    (fun h => hnew ⟨k.succAbove 0, h⟩) (fun h => hnew ⟨k.succAbove 1, h⟩) hk
  obtain ⟨a, ha, hea⟩ : meshTriangleBasis M t (k.succAbove 0) ∈ M.position '' (t.1 : Set M.Vertex) := by
    rw [← range_meshTriangleBasis]
    exact mem_range_self _
  obtain ⟨b, hb, heb⟩ : meshTriangleBasis M t (k.succAbove 1) ∈ M.position '' (t.1 : Set M.Vertex) := by
    rw [← range_meshTriangleBasis]
    exact mem_range_self _
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · intro heq
    have hidx := (meshTriangleBasis M t).ind.injective (hea.symm.trans (heq ▸ heb))
    have h01 : (0 : Fin 2) = 1 := Fin.succAbove_right_injective hidx
    norm_num at h01
  · simpa only [hea, heb] using hopen



theorem mesh_open_edge_mem_hull_iff (M : TriangleMesh) (t : M.Triangle)
    {a b : M.Vertex} (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b)
    {q : Plane} (hq : q ∈ openSegment ℝ (M.position a) (M.position b)) (u : M.Triangle) :
    q ∈ convexHull ℝ (range (meshTriangleBasis M u)) ↔ a ∈ u.1 ∧ b ∈ u.1 := by
  constructor
  · exact mesh_edge_endpoints_mem_of_openSegment_mem_hull M t u ha hb hab hq
  · rintro ⟨hau, hbu⟩
    apply (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ ?_) (subset_convexHull ℝ _ ?_)
      (openSegment_subset_segment ℝ _ _ hq)
    · rw [range_meshTriangleBasis]
      exact ⟨a, hau, rfl⟩
    · rw [range_meshTriangleBasis]
      exact ⟨b, hbu, rfl⟩



theorem mesh_open_edge_mem_interior_of_other_parent
    (M : TriangleMesh) (t u : M.Triangle) (htu : t ≠ u)
    {a b : M.Vertex} (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b)
    (hau : a ∈ u.1) (hbu : b ∈ u.1) {q : Plane}
    (hq : q ∈ openSegment ℝ (M.position a) (M.position b)) :
    q ∈ interior M.toPlaneComplex.support := by
  obtain ⟨c, hc0, hc1, hcrange⟩ := exists_meshTriangleBasis_with_edge M t ha hb hab
  obtain ⟨d, hd0, hd1, hdrange⟩ := exists_meshTriangleBasis_with_edge M u hau hbu hab
  have h0 := hc0.trans hd0.symm
  have h1 := hc1.trans hd1.symm
  have hdisj : Disjoint (interior (convexHull ℝ (range c)))
      (interior (convexHull ℝ (range d))) := by
    rw [hcrange, hdrange]
    exact mesh_common_edge_disjoint_interiors M t u htu hab ha hb hau hbu
  apply interior_mono (union_subset ?_ ?_)
    (affineTriangle_shared_edge_mem_interior_union c d h0 h1
      (affineTriangle_shared_edge_coord_neg c d h0 h1 hdisj)
      (by simpa only [hc0, hc1] using hq))
  · rw [hcrange]
    exact meshTriangleBasis_subset_support M t
  · rw [hdrange]
    exact meshTriangleBasis_subset_support M u



theorem mesh_open_edge_parent_card (M : TriangleMesh) (t : M.Triangle)
    {a b : M.Vertex} (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b)
    {q : Plane} (hq : q ∈ openSegment ℝ (M.position a) (M.position b)) :
    (Finset.univ.filter fun u : M.Triangle =>
      q ∈ convexHull ℝ (range (meshTriangleBasis M u))).card =
        if q ∈ interior M.toPlaneComplex.support then 2 else 1 := by
  simp only [mesh_open_edge_mem_hull_iff M t ha hb hab hq]
  split_ifs with hi
  · apply le_antisymm (mesh_edge_parent_card_le_two M hab)
    obtain ⟨u, hut, hau, hbu⟩ := mesh_edge_exists_other_parent_of_interior M t ha hb hab hq hi
    have hsub : ({t, u} : Finset M.Triangle) ⊆
        Finset.univ.filter (fun v : M.Triangle => a ∈ v.1 ∧ b ∈ v.1) := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hb⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hau, hbu⟩
    simpa only [Finset.card_pair hut.symm] using Finset.card_le_card hsub
  · have heq : Finset.univ.filter (fun u : M.Triangle => a ∈ u.1 ∧ b ∈ u.1) = {t} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hau, hbu⟩
        by_contra hut
        exact hi (mesh_open_edge_mem_interior_of_other_parent M t u (Ne.symm hut) ha hb hab hau hbu hq)
      · rintro rfl
        exact ⟨ha, hb⟩
    rw [heq, Finset.card_singleton]

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem independently_refined_mesh_fan_in_parent_interior
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (lines : M.Triangle → List (Plane →ᵃ[ℝ] ℝ)) (t : M.Triangle) {q : Plane}
    (hq : q ∈ interior (convexHull ℝ (range (meshTriangleBasis M t))))
    (hused : ∃ (u : ((TriangleMesh.single (meshTriangleBasis M t)
        (meshTriangleBasis M t).ind).refineByLines (lines t)).Triangle)
      (v : ((TriangleMesh.single (meshTriangleBasis M t)
        (meshTriangleBasis M t).ind).refineByLines (lines t)).Vertex),
      v ∈ u.1 ∧ ((TriangleMesh.single (meshTriangleBasis M t)
        (meshTriangleBasis M t).ind).refineByLines (lines t)).position v = q) :
    (∑ u : M.Triangle, meshVertexAngleContribution g F
      ((TriangleMesh.single (meshTriangleBasis M u) (meshTriangleBasis M u).ind).refineByLines (lines u))
      (F q)) = 2 * Real.pi := by
  have hqsource := hM (meshTriangleBasis_subset_support M t (interior_subset hq))
  rw [Finset.sum_eq_single t]
  · obtain ⟨u, v, hv, hpos⟩ := hused
    rw [← hpos]
    apply single_refineByLines_interior_vertex_fan g F _ _ hF hFi
      ((meshTriangleBasis_subset_support M t).trans hM) u v hv
    simpa only [TriangleMesh.refineByLines_support, TriangleMesh.single_support, hpos] using hq
  · intro u _ hut
    apply single_refineByLines_contribution_eq_zero_of_not_mem
    rintro ⟨z, hz, heq⟩
    have hzq := F.injOn (hM (meshTriangleBasis_subset_support M u hz)) hqsource heq
    subst z
    exact (mesh_triangle_inter_frontier M t u (Ne.symm hut) ⟨interior_subset hq, hz⟩).2 hq
  · simp




theorem independently_refined_mesh_new_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (lines : M.Triangle → List (Plane →ᵃ[ℝ] ℝ)) {q : Plane}
    (hq : q ∈ M.toPlaneComplex.support)
    (hnew : ∀ t : M.Triangle, q ∉ range (meshTriangleBasis M t))
    (hused : ∀ t : M.Triangle, q ∈ convexHull ℝ (range (meshTriangleBasis M t)) →
      ∃ (u : ((TriangleMesh.single (meshTriangleBasis M t)
          (meshTriangleBasis M t).ind).refineByLines (lines t)).Triangle)
        (v : ((TriangleMesh.single (meshTriangleBasis M t)
          (meshTriangleBasis M t).ind).refineByLines (lines t)).Vertex),
        v ∈ u.1 ∧ ((TriangleMesh.single (meshTriangleBasis M t)
          (meshTriangleBasis M t).ind).refineByLines (lines t)).position v = q) :
    (∑ t : M.Triangle, meshVertexAngleContribution g F
      ((TriangleMesh.single (meshTriangleBasis M t) (meshTriangleBasis M t).ind).refineByLines (lines t))
      (F q)) = if q ∈ interior M.toPlaneComplex.support then 2 * Real.pi else Real.pi := by
  by_cases hi : ∃ t : M.Triangle, q ∈ interior (convexHull ℝ (range (meshTriangleBasis M t)))
  · obtain ⟨t, ht⟩ := hi
    rw [if_pos (interior_mono (meshTriangleBasis_subset_support M t) ht)]
    exact independently_refined_mesh_fan_in_parent_interior g F M hF hFi hM lines t ht
      (hused t (interior_subset ht))
  · have hnint (t : M.Triangle) : q ∉ interior (convexHull ℝ (range (meshTriangleBasis M t))) :=
      fun ht => hi ⟨t, ht⟩
    have heach (t : M.Triangle) : meshVertexAngleContribution g F
        ((TriangleMesh.single (meshTriangleBasis M t) (meshTriangleBasis M t).ind).refineByLines (lines t))
        (F q) = if q ∈ convexHull ℝ (range (meshTriangleBasis M t)) then Real.pi else 0 := by
      split_ifs with ht
      · obtain ⟨u, v, hv, hpos⟩ := hused t ht
        rw [← hpos]
        exact single_refineByLines_new_boundary_vertex_fan g F _ _ hF hFi
          ((meshTriangleBasis_subset_support M t).trans hM) u v hv
          (hpos ▸ hnint t) (hpos ▸ hnew t)
      · apply single_refineByLines_contribution_eq_zero_of_not_mem
        rintro ⟨z, hz, heq⟩
        exact ht (F.injOn (hM (meshTriangleBasis_subset_support M t hz)) (hM hq) heq ▸ hz)
    simp_rw [heach]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← meshTriangleBasis_sources_cover] at hq
    obtain ⟨t, ht⟩ := mem_iUnion.mp hq
    obtain ⟨a, ha, b, hb, hab, hedge⟩ := mesh_frontier_nonvertex_mem_open_edge M t
      ⟨subset_closure ht, hnint t⟩ (hnew t)
    rw [mesh_open_edge_parent_card M t ha hb hab hedge]
    split_ifs <;> norm_num



theorem independently_refined_mesh_interior_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (lines : M.Triangle → List (Plane →ᵃ[ℝ] ℝ))
    (hfan : ∀ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 →
      M.position v ∈ interior M.toPlaneComplex.support →
      meshVertexAngleContribution g F M (F (M.position v)) = 2 * Real.pi)
    {q : Plane} (hq : q ∈ interior M.toPlaneComplex.support)
    (hused : ∀ t : M.Triangle, q ∈ convexHull ℝ (range (meshTriangleBasis M t)) →
      ∃ (u : ((TriangleMesh.single (meshTriangleBasis M t)
          (meshTriangleBasis M t).ind).refineByLines (lines t)).Triangle)
        (v : ((TriangleMesh.single (meshTriangleBasis M t)
          (meshTriangleBasis M t).ind).refineByLines (lines t)).Vertex),
        v ∈ u.1 ∧ ((TriangleMesh.single (meshTriangleBasis M t)
          (meshTriangleBasis M t).ind).refineByLines (lines t)).position v = q) :
    (∑ t : M.Triangle, meshVertexAngleContribution g F
      ((TriangleMesh.single (meshTriangleBasis M t) (meshTriangleBasis M t).ind).refineByLines (lines t))
      (F q)) = 2 * Real.pi := by
  by_cases hold : ∃ t : M.Triangle, q ∈ range (meshTriangleBasis M t)
  · obtain ⟨t, ht⟩ := hold
    rw [range_meshTriangleBasis] at ht
    obtain ⟨v, hv, rfl⟩ := ht
    rw [independently_refined_mesh_contribution_at_used_vertex g F M hF hFi hM lines t v hv]
    exact hfan t v hv hq
  · rw [independently_refined_mesh_new_vertex_fan g F M hF hFi hM lines (interior_subset hq)
      (fun t ht => hold ⟨t, ht⟩) hused, if_pos hq]

end PoincareConjecture.Topology.Surface
