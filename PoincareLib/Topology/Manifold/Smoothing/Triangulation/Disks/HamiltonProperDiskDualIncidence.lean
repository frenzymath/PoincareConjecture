import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskTriangleBlocks
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskVertexIncidence
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.HamiltonProperDiskFrontierStars
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricDualSubcomplex

/-!
# Exact frontier incidence for the same proper-disk dual carriers

A dual block of a disk face outside the frontier avoids the entire
frontier and lies in the region interior. Frontier edge cofaces are
the two original triangles obtained from the retained planar chart.
See Hudson 1969, pp.58--63 and M76 derivation351.
-/

set_option autoImplicit false

open Set Metric Geometry
open scoped Topology

namespace PoincareMT.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}

/-- An original disk face outside the frontier has its entire
ambient dual block in the region interior. Thus no region cut is
needed on that block, even when all its vertices lie on the frontier.
See Hudson pp.58--63 and derivation351. -/
theorem HamiltonProperDiskTriangulation.dualBlock_subset_interior
    (T : HamiltonProperDiskTriangulation R D b) {s : Finset E}
    (hs : s ∈ T.disk.faces) (hsF : s ∉ T.boundary.faces) :
    let : Fintype T.ambient.faces := T.finite.fintype
    (T.ambient.barycentricDualBlock s).space ⊆ interior R := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let : Fintype T.boundary.faces := (T.finite.subset T.boundary_le).fintype
  let N := T.ambient.barycentricDualBlock s
  let p := s.centroid ℝ id
  have hpN : p ∈ N.space := N.vertices_subset_space
    (T.ambient.faceCentroid_mem_barycentricDualBlock_vertices (T.disk_le hs))
  have hdis : N.space ∩ frontier R = ∅ := by
    calc
      N.space ∩ frontier R = N.space ∩ T.boundary.space :=
        congrArg (fun S => N.space ∩ S) T.boundary_space.symm
      _ = (T.boundary.barycentricDualBlock s).space :=
        T.ambient.barycentricDualBlock_space_inter_subcomplex T.boundary T.boundary_le s
      _ = ∅ := T.boundary.barycentricDualBlock_space_eq_empty_of_not_face
        (T.disk.nonempty_of_mem_faces hs) hsF
  have hstar : N.closedStar p = N :=
    T.ambient.barycentricDualBlock_closedStar_faceCentroid (T.disk_le hs)
  have hcv : StarConvex ℝ p N.space := by
    have h := N.starConvex_closedFaceStar {p} (p := p) (by
      simp only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff])
    simpa only [SimplicialComplex.closedFaceStar_singleton_eq_closedStar, hstar] using h
  have hpR : p ∈ R := T.disk_subset_region (T.disk_space.subset
    (T.disk.convexHull_subset_space hs
      (s.centroid_mem_convexHull (T.disk.nonempty_of_mem_faces hs))))
  have hpint : p ∈ interior R := by
    by_contra hp
    exact hdis.subset ⟨hpN, subset_closure hpR, hp⟩
  apply (hcv.isPathConnected hpN).isConnected.isPreconnected.m76_subset_of_disjoint_frontier
    isOpen_interior
  · apply disjoint_left.mpr
    exact fun x hx hxN => hdis.subset ⟨hxN, frontier_interior_subset hx⟩
  · exact ⟨p, hpN, hpint⟩

variable [FiniteDimensional ℝ E]

/-- The actual frontier subcomplex has only vertices, edges and
triangles in dimension three. A full tetrahedron would give an
interior point of the frontier of the closed region. See derivation351. -/
theorem HamiltonProperDiskTriangulation.frontier_face_card_le
    (T : HamiltonProperDiskTriangulation R D b) (h3 : Module.finrank ℝ E = 3)
    {s : Finset E} (hs : s ∈ T.boundary.faces) : s.card ≤ 3 := by
  have hbound : s.card ≤ 4 := by
    have h := (T.boundary.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa only [Fintype.card_coe, h3] using h
  by_contra hnot
  have hcard : s.card = Module.finrank ℝ E + 1 := by omega
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E))
    (Finset.coe_nonempty.mpr (T.boundary.nonempty_of_mem_faces hs)).convexHull
  have hxint := T.boundary.mem_interior_space_of_full_face hs hcard hx
  have hRclosed : IsClosed R := T.region_space ▸
    (T.region.isCompact_space_of_finite (T.finite.subset T.region_le)).isClosed
  rw [T.boundary_space, interior_frontier hRclosed] at hxint
  exact hxint

/-- The paired frontier triangles of an actual boundary disk edge
are obtained with their original labels and exhaust all cofaces.
See Hudson pp.58--63 and derivation351. -/
theorem HamiltonProperDiskTriangulation.exists_frontier_edge_triangle_cofaces
    (T : HamiltonProperDiskTriangulation R D b) {s : Finset E}
    (hsD : s ∈ T.disk.faces) (hsF : s ∈ T.boundary.faces) (hscard : s.card = 2) :
    ∃ t ∈ T.boundary.faces, ∃ u ∈ T.boundary.faces,
      s ⊆ t ∧ s ⊆ u ∧ t.card = 3 ∧ u.card = 3 ∧ t ≠ u ∧
      ∀ v ∈ T.boundary.faces, s ⊆ v → v.card = 3 → v = t ∨ v = u := by
  obtain ⟨t, u, htu, heq⟩ := ncard_eq_two.mp
    (T.frontier_edge_triangle_count hsD hsF hscard)
  have ht : t ∈ {v : Finset E | v ∈ T.boundary.faces ∧ v.card = 3 ∧ s ⊆ v} :=
    heq.symm.subset (Or.inl rfl)
  have hu : u ∈ {v : Finset E | v ∈ T.boundary.faces ∧ v.card = 3 ∧ s ⊆ v} :=
    heq.symm.subset (Or.inr rfl)
  exact ⟨t, ht.1, u, hu.1, ht.2.2, hu.2.2, ht.2.1, hu.2.1, htu,
    fun v hv hsv hvc => heq.subset ⟨hv, hvc, hsv⟩⟩

end PoincareMT.M76.HamiltonIndexOne
