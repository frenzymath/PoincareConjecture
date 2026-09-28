import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.Compact

set_option autoImplicit false
open Set Classical

namespace Poincare.Topology.Plane.Meshes

namespace TriangleMesh

variable (T : TriangleMesh)

def triangleCarrier (t : Finset T.Vertex) : Set Plane :=
  convexHull ℝ (T.position '' (t : Set T.Vertex))

theorem interior_triangleCarrier_nonempty (t : T.Triangle) :
    (interior (T.triangleCarrier t.1)).Nonempty := by
  apply (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [affineSpan_convexHull]
  have hrange : range (fun v : t.1 => T.position v) = T.position '' (t.1 : Set T.Vertex) := by
    ext x
    simp
  rw [← hrange]
  apply (T.affineIndependent_triangle t.1 t.2).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  rw [Fintype.card_coe, T.card_triangle t.1 t.2]
  simp [Plane]

theorem closure_interior_triangleCarrier (t : T.Triangle) :
    closure (interior (T.triangleCarrier t.1)) = T.triangleCarrier t.1 := by
  change closure (interior (convexHull ℝ (T.position '' (t.1 : Set T.Vertex)))) =
    convexHull ℝ (T.position '' (t.1 : Set T.Vertex))
  rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
    (T.interior_triangleCarrier_nonempty t)]
  exact (t.1.finite_toSet.image T.position).isClosed_convexHull ℝ |>.closure_eq

theorem IsMonochromatic.interior_disjoint_zero {l : Plane →ᵃ[ℝ] ℝ}
    (hmono : T.IsMonochromatic l) (hsurj : Function.Surjective l) (t : T.Triangle) :
    Disjoint (interior (T.triangleCarrier t.1)) {z | l z = 0} := by
  apply disjoint_left.mpr
  intro z hz hz0
  rcases hmono t.1 t.2 with hpos | hneg
  · have hsub : T.triangleCarrier t.1 ⊆ l ⁻¹' Ici (0 : ℝ) := by
      apply convexHull_min
      · rintro _ ⟨v, hv, rfl⟩
        exact hpos v hv
      · exact (convex_Ici (0 : ℝ)).affine_preimage l
    have hzi := interior_mono hsub hz
    rw [← (l.isOpenMap l.continuous_of_finiteDimensional hsurj).preimage_interior_eq_interior_preimage
      l.continuous_of_finiteDimensional,
      interior_Ici] at hzi
    exact (ne_of_gt hzi) hz0
  · have hsub : T.triangleCarrier t.1 ⊆ l ⁻¹' Iic (0 : ℝ) := by
      apply convexHull_min
      · rintro _ ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact (convex_Iic (0 : ℝ)).affine_preimage l
    have hzi := interior_mono hsub hz
    rw [← (l.isOpenMap l.continuous_of_finiteDimensional hsurj).preimage_interior_eq_interior_preimage
      l.continuous_of_finiteDimensional,
      interior_Iic] at hzi
    exact (ne_of_lt hzi) hz0

theorem exists_restriction_support_eq_closure_with_refinement {U : Set Plane} (hU : IsOpen U)
    (hUT : closure U ⊆ T.toPlaneComplex.support)
    (hfront : ∀ t : T.Triangle, Disjoint (interior (T.triangleCarrier t.1)) (frontier U)) :
    ∃ S : TriangleMesh, S.toPlaneComplex.support = closure U ∧
      S = T.restrictTriangles (fun t => interior (T.triangleCarrier t) ⊆ U) := by
  classical
  let P (t : Finset T.Vertex) : Prop := interior (T.triangleCarrier t) ⊆ U
  let S := T.restrictTriangles P
  have hside (t : T.Triangle) (hmeet : (interior (T.triangleCarrier t.1) ∩ U).Nonempty) :
      P t.1 := by
    apply ((convex_convexHull ℝ _).interior.isPreconnected).subset_of_closure_inter_subset hU hmeet
    rintro z ⟨hzclosure, hztriangle⟩
    by_contra hzU
    apply disjoint_left.mp (hfront t) hztriangle
    rw [frontier, hU.interior_eq]
    exact ⟨hzclosure, hzU⟩
  have hSU : S.toPlaneComplex.support ⊆ closure U := by
    rw [TriangleMesh.toPlaneComplex_support]
    rintro z hz
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hz
    obtain ⟨htT, htP⟩ := (T.mem_restrictTriangles_triangles P).mp ht
    have hsub := closure_mono htP
    rw [T.closure_interior_triangleCarrier ⟨t, htT⟩] at hsub
    exact hsub hzt
  have hUS : U ⊆ S.toPlaneComplex.support := by
    intro z hz
    have hzt := hUT (subset_closure hz)
    rw [TriangleMesh.toPlaneComplex_support] at hzt
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hzt
    have hzcl : z ∈ closure (interior (T.triangleCarrier t)) := by
      rw [T.closure_interior_triangleCarrier ⟨t, ht⟩]
      exact hzt
    have hmeet : (interior (T.triangleCarrier t) ∩ U).Nonempty := by
      obtain ⟨w, hwU, hwt⟩ := Set.Nonempty.of_closure
        ⟨z, hU.inter_closure ⟨hz, hzcl⟩⟩
      exact ⟨w, hwt, hwU⟩
    rw [TriangleMesh.toPlaneComplex_support]
    exact mem_iUnion₂.mpr ⟨t, (T.mem_restrictTriangles_triangles P).mpr
      ⟨ht, hside ⟨t, ht⟩ hmeet⟩, hzt⟩
  exact ⟨S, subset_antisymm hSU
    (closure_minimal hUS S.toPlaneComplex.isCompact_support.isClosed), rfl⟩

theorem exists_restriction_support_eq_closure {U : Set Plane} (hU : IsOpen U)
    (hUT : closure U ⊆ T.toPlaneComplex.support)
    (hfront : ∀ t : T.Triangle, Disjoint (interior (T.triangleCarrier t.1)) (frontier U)) :
    ∃ S : TriangleMesh, S.toPlaneComplex.support = closure U := by
  obtain ⟨S, hs, _⟩ := T.exists_restriction_support_eq_closure_with_refinement hU hUT hfront
  exact ⟨S, hs⟩

end TriangleMesh

theorem exists_triangleMesh_of_frontier_in_finitely_many_lines_with_refinement
    {U : Set Plane} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hsurj : ∀ l ∈ lines, Function.Surjective l)
    (hfrontier : frontier U ⊆ ⋃ l ∈ lines, {p : Plane | l p = 0}) :
    ∃ T : TriangleMesh, T.toPlaneComplex.support = closure U ∧
      ∃ (b : AffineBasis (Fin 3) ℝ Plane)
        (P : Finset ((TriangleMesh.single b b.ind).refineByLines lines).Vertex → Prop),
        T = ((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P ∧
        T.toPlaneComplex.support ⊆ interior (convexHull ℝ (range b)) := by
  obtain ⟨b, hb⟩ := exists_triangle_containing_bounded
    (hbounded.closure.thickening (δ := 1))
  have hbint : closure U ⊆ interior (convexHull ℝ (range b)) :=
    (Metric.self_subset_thickening (by norm_num : (0 : ℝ) < 1) (closure U)).trans
      (Metric.isOpen_thickening.subset_interior_iff.mpr hb)
  let T := (TriangleMesh.single b b.ind).refineByLines lines
  have hUT : closure U ⊆ T.toPlaneComplex.support := by
    rw [TriangleMesh.refineByLines_support, TriangleMesh.single_support]
    exact hbint.trans interior_subset
  have hfront : ∀ t : T.Triangle,
      Disjoint (interior (T.triangleCarrier t.1)) (frontier U) := by
    intro t
    apply disjoint_left.mpr
    intro z hz hzfront
    obtain ⟨l, hl, hzl⟩ := mem_iUnion₂.mp (hfrontier hzfront)
    have hmono : T.IsMonochromatic l :=
      (TriangleMesh.single b b.ind).refineByLines_isMonochromatic_of_mem lines hl
    exact disjoint_left.mp
      (TriangleMesh.IsMonochromatic.interior_disjoint_zero T hmono (hsurj l hl) t) hz hzl
  obtain ⟨S, hs, hS⟩ :=
    T.exists_restriction_support_eq_closure_with_refinement hU hUT hfront
  exact ⟨S, hs, b, _, hS, hs ▸ hbint⟩

theorem exists_triangleMesh_of_frontier_in_finitely_many_lines
    {U : Set Plane} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hsurj : ∀ l ∈ lines, Function.Surjective l)
    (hfrontier : frontier U ⊆ ⋃ l ∈ lines, {p : Plane | l p = 0}) :
    ∃ T : TriangleMesh, T.toPlaneComplex.support = closure U := by
  obtain ⟨T, hs, _⟩ := exists_triangleMesh_of_frontier_in_finitely_many_lines_with_refinement
    hU hbounded lines hsurj hfrontier
  exact ⟨T, hs⟩

end Poincare.Topology.Plane.Meshes
