import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.EdgeMultiplicity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface



theorem affineTriangle_shared_edge_mem_interior_union
    (b c : AffineBasis (Fin 3) ℝ Plane) (h0 : b 0 = c 0) (h1 : b 1 = c 1)
    (hside : b.coord 2 (c 2) < 0) {q : Plane}
    (hq : q ∈ openSegment ℝ (b 0) (b 1)) :
    q ∈ interior (convexHull ℝ (range b) ∪ convexHull ℝ (range c)) := by
  rw [openSegment_eq_image_lineMap] at hq
  obtain ⟨s, hs, rfl⟩ := hq
  let q := AffineMap.lineMap (b 0) (b 1) s
  have hb0 : 0 < b.coord 0 q := by
    norm_num [q, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
      AffineBasis.coord_apply, Fin.ext_iff]
    linarith [hs.2]
  have hb1 : 0 < b.coord 1 q := by
    simpa [q, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
      AffineBasis.coord_apply, Fin.ext_iff] using hs.1
  have hc0 : 0 < c.coord 0 q := by
    norm_num [q, h0, h1, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
      AffineBasis.coord_apply, Fin.ext_iff]
    linarith [hs.2]
  have hc1 : 0 < c.coord 1 q := by
    simpa [q, h0, h1, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
      AffineBasis.coord_apply, Fin.ext_iff] using hs.1
  have hnb0 : ∀ᶠ z in 𝓝 q, 0 < b.coord 0 z :=
    (continuous_barycentric_coord b 0).continuousAt.eventually (Ioi_mem_nhds hb0)
  have hnb1 : ∀ᶠ z in 𝓝 q, 0 < b.coord 1 z :=
    (continuous_barycentric_coord b 1).continuousAt.eventually (Ioi_mem_nhds hb1)
  have hnc0 : ∀ᶠ z in 𝓝 q, 0 < c.coord 0 z :=
    (continuous_barycentric_coord c 0).continuousAt.eventually (Ioi_mem_nhds hc0)
  have hnc1 : ∀ᶠ z in 𝓝 q, 0 < c.coord 1 z :=
    (continuous_barycentric_coord c 1).continuousAt.eventually (Ioi_mem_nhds hc1)
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hnb0, hnb1, hnc0, hnc1] with z hzb0 hzb1 hzc0 hzc1
  by_cases hz2 : 0 ≤ b.coord 2 z
  · left
    rw [b.convexHull_eq_nonneg_coord]
    intro i
    fin_cases i
    · exact hzb0.le
    · exact hzb1.le
    · exact hz2
  · right
    rw [c.convexHull_eq_nonneg_coord]
    have hrelation := congrArg (fun l : Plane →ᵃ[ℝ] ℝ => l z)
      (affineTriangle_shared_edge_coord b c h0 h1)
    change b.coord 2 z = b.coord 2 (c 2) * c.coord 2 z at hrelation
    have hcz2 : 0 ≤ c.coord 2 z := by nlinarith
    intro i
    fin_cases i
    · exact hzc0.le
    · exact hzc1.le
    · exact hcz2



theorem localRefinementBoundaryCuts_mem_interior_of_other_parent (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (u : M.Triangle) (htu : t ≠ u)
    (hqu : q ∈ convexHull ℝ (range (meshTriangleBasis M u))) :
    q ∈ interior M.toPlaneComplex.support := by
  obtain ⟨a, hat, d, hdt, had, _, hseg, hparents⟩ :=
    localRefinementBoundaryCuts_incident_edge M f t hq
  obtain ⟨hau, hdu⟩ := (hparents u).mp hqu
  obtain ⟨b, hb0, hb1, hbrange⟩ := exists_meshTriangleBasis_with_edge M t hat hdt had
  obtain ⟨c, hc0, hc1, hcrange⟩ := exists_meshTriangleBasis_with_edge M u hau hdu had
  have h0 := hb0.trans hc0.symm
  have h1 := hb1.trans hc1.symm
  have hdisj : Disjoint (interior (convexHull ℝ (range b)))
      (interior (convexHull ℝ (range c))) := by
    rw [hbrange, hcrange]
    exact mesh_common_edge_disjoint_interiors M t u htu had hat hdt hau hdu
  have hint := affineTriangle_shared_edge_mem_interior_union b c h0 h1
    (affineTriangle_shared_edge_coord_neg b c h0 h1 hdisj)
    (by simpa only [hb0, hb1] using hseg)
  apply interior_mono (union_subset ?_ ?_) hint
  · rw [hbrange]
    exact meshTriangleBasis_subset_support M t
  · rw [hcrange]
    exact meshTriangleBasis_subset_support M u



theorem localRefinementBoundaryCuts_parent_card_eq_one (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (hqboundary : q ∉ interior M.toPlaneComplex.support) :
    (Finset.univ.filter fun u : M.Triangle =>
      q ∈ convexHull ℝ (range (meshTriangleBasis M u))).card = 1 := by
  have heq : (Finset.univ.filter fun u : M.Triangle =>
      q ∈ convexHull ℝ (range (meshTriangleBasis M u))) = {t} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hqu
      by_contra hut
      exact hqboundary
        (localRefinementBoundaryCuts_mem_interior_of_other_parent M f t hq u
          (fun h => hut h.symm) hqu)
    · intro heq
      subst u
      exact ((finite_range _).isClosed_convexHull ℝ).frontier_subset
        (localRefinementBoundaryCuts_geometry M f t hq).1
  rw [heq, Finset.card_singleton]



theorem localRefinementBoundaryCuts_card_eq_one (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (hqboundary : q ∉ interior M.toPlaneComplex.support) :
    (Finset.univ.filter fun u : M.Triangle => q ∈ localRefinementBoundaryCuts M f u).card = 1 := by
  simp only [localRefinementBoundaryCuts_mem_iff_mem_hull M f t hq]
  exact localRefinementBoundaryCuts_parent_card_eq_one M f t hq hqboundary

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem lineRefinementMesh_new_boundary_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (hqboundary : q ∉ interior M.toPlaneComplex.support)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source) :
    meshVertexAngleContribution g F (M.lineRefinementMesh f) (F q) = Real.pi := by
  rw [lineRefinementMesh_vertex_contribution_new_cut g F M f t hq hF hFi hM,
    localRefinementBoundaryCuts_card_eq_one M f t hq hqboundary]
  norm_num

end PoincareConjecture.Topology.Surface
