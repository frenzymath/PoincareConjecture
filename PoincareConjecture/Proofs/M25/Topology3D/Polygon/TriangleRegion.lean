import PoincareConjecture.Proofs.M25.Topology3D.Polygon.RegionNesting
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.SimpleTriangle
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ConvexExterior

set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} {p : Polygon E n}

theorem IsSimplePolygon.polygonInterior_eq_interior_of_boundary_eq_frontier
    (hp : IsSimplePolygon p) (hdim : Module.finrank ℝ E = 2) {C : Set E}
    (hclosed : IsClosed C) (hconv : Convex ℝ C) (hbounded : Bornology.IsBounded C)
    (hint : (interior C).Nonempty) (hfront : p.boundary ℝ = frontier C) :
    polygonInterior p = interior C := by
  have hcoverC : interior C ∪ Cᶜ = (p.boundary ℝ)ᶜ := by
    rw [hfront, hclosed.frontier_eq]
    ext x
    simp only [mem_union, mem_compl_iff, mem_sdiff]
    tauto
  have hdisC : Disjoint (interior C) Cᶜ :=
    Set.disjoint_left.mpr fun _ hx hnot => hnot (interior_subset hx)
  obtain ⟨hI, hO, _, hOp, hdis, hcover, _, hOb, _⟩ := hp.polygonRegions_spec hdim
  have hOsub : polygonExterior p ⊆ Cᶜ := by
    have hcoverO : polygonExterior p ⊆ interior C ∪ Cᶜ := by
      rw [hcoverC]
      exact fun _ hx => hx.1
    rcases hOp.isConnected.isPreconnected.subset_or_subset isOpen_interior hclosed.isOpen_compl
        hdisC hcoverO with h | h
    · exact (hOb (hbounded.subset (h.trans interior_subset))).elim
    · exact h
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank, hdim]
    norm_num
  have hCc : IsPathConnected Cᶜ := by
    simpa only [hclosed.closure_eq] using
      isPathConnected_compl_closure_of_convex hrank hconv hint hbounded
  have hCcover : Cᶜ ⊆ polygonInterior p ∪ polygonExterior p := by
    rw [hcover]
    intro x hx hxB
    exact hx (hclosed.frontier_subset (hfront ▸ hxB))
  obtain ⟨z, hz⟩ := hOp.isConnected.nonempty
  have hCcsub : Cᶜ ⊆ polygonExterior p :=
    hCc.isConnected.isPreconnected.subset_right_of_subset_union
      hI hO hdis hCcover ⟨z, hOsub hz, hz⟩
  apply subset_antisymm
  · intro x hx
    have hxcover : x ∈ interior C ∪ Cᶜ := hcoverC.symm ▸ hx.1
    exact hxcover.resolve_right fun hxc => Set.disjoint_left.mp hdis hx (hCcsub hxc)
  · intro x hx
    have hxB : x ∉ p.boundary ℝ := by
      change x ∈ (p.boundary ℝ)ᶜ
      rw [← hcoverC]
      exact Or.inl hx
    have hxcover : x ∈ polygonInterior p ∪ polygonExterior p := hcover.symm ▸ hxB
    exact hxcover.resolve_right fun hxO => hOsub hxO (interior_subset hx)

theorem IsSimplePolygon.triangle_polygonInterior {p : Polygon E 3}
    (hp : IsSimplePolygon p) (hdim : Module.finrank ℝ E = 2) :
    polygonInterior p = interior (convexHull ℝ (range p)) := by
  have hcompact := (finite_range p).isCompact_convexHull ℝ
  exact hp.polygonInterior_eq_interior_of_boundary_eq_frontier hdim hcompact.isClosed
    (convex_convexHull ℝ _) hcompact.isBounded
    ⟨_, (hp.triangleAffineBasis hdim).centroid_mem_interior_convexHull⟩
    (hp.triangle_boundary_eq_frontier hdim)

theorem IsSimplePolygon.triangle_closure_polygonInterior {p : Polygon E 3}
    (hp : IsSimplePolygon p) (hdim : Module.finrank ℝ E = 2) :
    closure (polygonInterior p) = convexHull ℝ (range p) := by
  rw [hp.triangle_polygonInterior hdim,
    (convex_convexHull ℝ (range p)).closure_interior_eq_closure_of_nonempty_interior
      ⟨_, (hp.triangleAffineBasis hdim).centroid_mem_interior_convexHull⟩,
    ((finite_range p).isCompact_convexHull ℝ).isClosed.closure_eq]

end PoincareConjecture.M25.Topology3D
