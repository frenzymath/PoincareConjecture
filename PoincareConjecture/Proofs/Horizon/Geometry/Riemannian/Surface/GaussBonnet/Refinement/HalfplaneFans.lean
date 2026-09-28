import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.CoreBoundarySectors
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.BoundaryFans
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.BoundaryContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

theorem localRefinementMesh_halfspace_iff_parent
    (M : TriangleMesh) (f l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (t : M.Triangle) (s : (M.localRefinementMesh f t).Triangle) :
    (M.localRefinementMesh f t).triangleCarrier s.1 ⊆ {z | 0 ≤ l z} ↔
      M.triangleCarrier t.1 ⊆ {z | 0 ≤ l z} := by
  have hsub : (M.localRefinementMesh f t).triangleCarrier s.1 ⊆ M.triangleCarrier t.1 := by
    intro z hz
    have hz' : z ∈ (M.localRefinementMesh f t).toPlaneComplex.support := by
      rw [TriangleMesh.toPlaneComplex_support]
      exact mem_iUnion₂.mpr ⟨s.1, s.2, hz⟩
    rw [M.localRefinementMesh_support f t] at hz'
    exact hz'
  constructor
  · intro hs
    rcases hmono.triangleCarrier_halfspace M t with hpos | hneg
    · exact hpos
    · exfalso
      let b := meshTriangleBasis (M.localRefinementMesh f t) s
      have hzero : ∀ i : Fin 3, l (b i) = 0 := by
        intro i
        have hi : b i ∈ (M.localRefinementMesh f t).triangleCarrier s.1 := by
          rw [TriangleMesh.triangleCarrier, ← range_meshTriangleBasis]
          exact subset_convexHull ℝ _ (mem_range_self i)
        exact le_antisymm (hneg _ (hsub hi)) (hs hi)
      have heq : l = 0 := AffineMap.ext_on b.tot (by
        rintro z ⟨i, rfl⟩
        exact hzero i)
      obtain ⟨z, hz⟩ := hl 1
      rw [heq] at hz
      norm_num at hz
  · exact fun ht => ht.trans' hsub

theorem lineRefinementTriangleEquiv_halfspace_iff_parent
    (M : TriangleMesh) (f l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (t : M.Triangle) (s : (M.localRefinementMesh f t).Triangle) :
    (M.lineRefinementMesh f).triangleCarrier
      (lineRefinementTriangleEquiv M f ⟨t, s⟩).1 ⊆ {z | 0 ≤ l z} ↔
      M.triangleCarrier t.1 ⊆ {z | 0 ≤ l z} := by
  have hc : (M.lineRefinementMesh f).triangleCarrier
      (lineRefinementTriangleEquiv M f ⟨t, s⟩).1 =
        (M.localRefinementMesh f t).triangleCarrier s.1 := by
    simp only [TriangleMesh.triangleCarrier, ← range_meshTriangleBasis,
      range_meshTriangleBasis_lineRefinementTriangleEquiv]
  rw [hc]
  exact localRefinementMesh_halfspace_iff_parent M f l hl hmono t s

theorem localRefinementBoundaryCuts_restrictTriangles_toFinset
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (f : Plane →ᵃ[ℝ] ℝ)
    (t : (M.restrictTriangles P).Triangle) :
    (localRefinementBoundaryCuts (M.restrictTriangles P) f t).toFinset =
      (localRefinementBoundaryCuts M f (restrictTrianglesTriangleEquiv M P t).1).toFinset := by
  ext q
  simp only [List.mem_toFinset, mem_localRefinementBoundaryCuts_iff_crossed_edge]
  rfl

theorem halfspace_restriction_support_subset (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ) :
    (M.restrictTriangles (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ l z})).toPlaneComplex.support ⊆
      {z | 0 ≤ l z} := by
  intro z hz
  rw [TriangleMesh.toPlaneComplex_support] at hz
  obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hz
  exact ((M.mem_restrictTriangles_triangles _).mp ht).2 hzt

theorem mem_halfspace_restriction_of_mem_interior
    (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    {q : Plane} (hq : q ∈ interior M.toPlaneComplex.support) (hql : 0 ≤ l q) :
    q ∈ (M.restrictTriangles (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ l z})).toPlaneComplex.support := by
  let N := M.restrictTriangles (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ l z})
  have hpos : interior M.toPlaneComplex.support ∩ l ⁻¹' Ioi (0 : ℝ) ⊆
      N.toPlaneComplex.support := by
    rintro z ⟨hz, hzl⟩
    have hzM := interior_subset hz
    rw [TriangleMesh.toPlaneComplex_support] at hzM ⊢
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hzM
    refine mem_iUnion₂.mpr ⟨t, (M.mem_restrictTriangles_triangles _).mpr ⟨ht, ?_⟩, hzt⟩
    rcases hmono.triangleCarrier_halfspace M ⟨t, ht⟩ with hnonneg | hnonpos
    · exact hnonneg
    · exact False.elim ((not_lt_of_ge (hnonpos z hzt)) hzl)
  have hqcl : q ∈ closure (l ⁻¹' Ioi (0 : ℝ)) := by
    rw [← (l.isOpenMap l.continuous_of_finiteDimensional hl).preimage_closure_eq_closure_preimage
      l.continuous_of_finiteDimensional, closure_Ioi]
    exact hql
  exact (closure_minimal hpos N.toPlaneComplex.isCompact_support.isClosed)
    (isOpen_interior.inter_closure ⟨hq, hqcl⟩)

theorem halfspace_restriction_support_eventuallyEq
    (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    {q : Plane} (hq : q ∈ interior M.toPlaneComplex.support) :
    (M.restrictTriangles (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ l z})).toPlaneComplex.support
      =ᶠ[𝓝 q] {z | 0 ≤ l z} := by
  filter_upwards [isOpen_interior.mem_nhds hq] with z hz
  exact propext ⟨fun h => halfspace_restriction_support_subset M l h,
    fun h => mem_halfspace_restriction_of_mem_interior M l hl hmono hz h⟩

theorem not_mem_interior_halfspace_restriction_of_zero
    (M : TriangleMesh) (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l)
    {q : Plane} (hql : l q = 0) :
    q ∉ interior (M.restrictTriangles
      (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ l z})).toPlaneComplex.support := by
  intro hq
  have h := interior_mono (halfspace_restriction_support_subset M l) hq
  change q ∈ interior (l ⁻¹' Ici (0 : ℝ)) at h
  rw [← (l.isOpenMap l.continuous_of_finiteDimensional hl).preimage_interior_eq_interior_preimage
    l.continuous_of_finiteDimensional, interior_Ici] at h
  exact (ne_of_gt h) hql

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem meshVertexAngleContribution_lineRefinementMesh_halfspace
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l) (x : S) :
    meshVertexAngleContribution g F ((M.lineRefinementMesh f).restrictTriangles
      (fun s => (M.lineRefinementMesh f).triangleCarrier s ⊆ {z | 0 ≤ l z})) x =
      ∑ t : M.Triangle, if M.triangleCarrier t.1 ⊆ {z | 0 ≤ l z} then
        meshVertexAngleContribution g F (M.localRefinementMesh f t) x else 0 := by
  rw [meshVertexAngleContribution_restrictTriangles_eq_sum,
    ← (lineRefinementTriangleEquiv M f).sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  simp only [lineRefinementTriangleEquiv_halfspace_iff_parent M f l hl hmono]
  by_cases ht : M.triangleCarrier t.1 ⊆ {z | 0 ≤ l z}
  · simp only [ht, if_true]
    unfold meshVertexAngleContribution
    apply Finset.sum_congr rfl
    intro s _
    exact coordinateTriangle_vertex_contribution_eq_of_range_eq g F _ _
      (range_meshTriangleBasis_lineRefinementTriangleEquiv M f t s) x
  · simp only [ht, if_false, Finset.sum_const_zero]

theorem lineRefinementMesh_halfspace_vertex_contribution
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source) (x : S) :
    meshVertexAngleContribution g F ((M.lineRefinementMesh f).restrictTriangles
      (fun s => (M.lineRefinementMesh f).triangleCarrier s ⊆ {z | 0 ≤ l z})) x =
      meshVertexAngleContribution g F (M.restrictTriangles
        (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ l z})) x +
      ∑ t : M.Triangle, if M.triangleCarrier t.1 ⊆ {z | 0 ≤ l z} then
        ∑ q ∈ (localRefinementBoundaryCuts M f t).toFinset,
          if F q = x then Real.pi else 0 else 0 := by
  rw [meshVertexAngleContribution_lineRefinementMesh_halfspace g F M f l hl hmono x]
  simp_rw [localRefinementMesh_vertex_contribution_finset g F M f _ hF hFi
    ((meshTriangleBasis_subset_support M _).trans hM) x]
  rw [meshVertexAngleContribution_restrictTriangles_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp only [add_zero]

theorem meshVertexAngleContribution_halfspace_refine_commute
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source) (x : S) :
    meshVertexAngleContribution g F ((M.lineRefinementMesh f).restrictTriangles
      (fun s => (M.lineRefinementMesh f).triangleCarrier s ⊆ {z | 0 ≤ l z})) x =
      meshVertexAngleContribution g F ((M.restrictTriangles
        (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ l z})).lineRefinementMesh f) x := by
  let P := fun t : Finset M.Vertex => M.triangleCarrier t ⊆ {z | 0 ≤ l z}
  rw [lineRefinementMesh_halfspace_vertex_contribution g F M f l hl hmono hF hFi hM x,
    lineRefinementMesh_vertex_contribution g F (M.restrictTriangles P) f hF hFi
      ((restrictTriangles_support_subset M P).trans hM) x]
  congr 1
  rw [← (restrictTrianglesTriangleEquiv M P).symm.sum_comp]
  simp only [localRefinementBoundaryCuts_restrictTriangles_toFinset,
    Equiv.apply_symm_apply]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter fun t : M.Triangle => P t.1)
    (by simp) (fun t : M.Triangle =>
      ∑ q ∈ (localRefinementBoundaryCuts M f t).toFinset,
        if F q = x then Real.pi else 0))

theorem lineRefinementMesh_halfspace_new_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (t : M.Triangle) {q : Plane} (hq : q ∈ localRefinementBoundaryCuts M f t)
    (hqint : q ∈ interior M.toPlaneComplex.support) (hql : l q = 0)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source) :
    meshVertexAngleContribution g F ((M.lineRefinementMesh f).restrictTriangles
      (fun s => (M.lineRefinementMesh f).triangleCarrier s ⊆ {z | 0 ≤ l z})) (F q) = Real.pi := by
  let P := fun t : Finset M.Vertex => M.triangleCarrier t ⊆ {z | 0 ≤ l z}
  let N := M.restrictTriangles P
  have hqN : q ∈ N.toPlaneComplex.support :=
    mem_halfspace_restriction_of_mem_interior M l hl hmono hqint hql.ge
  rw [TriangleMesh.toPlaneComplex_support] at hqN
  obtain ⟨u, hu, hqu⟩ := mem_iUnion₂.mp hqN
  let U : N.Triangle := ⟨u, hu⟩
  have hqU : q ∈ localRefinementBoundaryCuts N f U := by
    rw [← List.mem_toFinset, localRefinementBoundaryCuts_restrictTriangles_toFinset,
      List.mem_toFinset]
    apply localRefinementBoundaryCuts_mem_of_mem_hull M f t hq
    rw [range_meshTriangleBasis]
    exact hqu
  rw [meshVertexAngleContribution_halfspace_refine_commute g F M f l hl hmono hF hFi hM]
  exact lineRefinementMesh_new_boundary_vertex_fan g F N f U hqU
    (not_mem_interior_halfspace_restriction_of_zero M l hl hql) hF hFi
    ((restrictTriangles_support_subset M P).trans hM)

theorem lineRefinementMesh_halfspace_old_vertex_contribution
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (t : M.Triangle) (v : M.Vertex) (hv : v ∈ t.1) :
    meshVertexAngleContribution g F ((M.lineRefinementMesh f).restrictTriangles
      (fun s => (M.lineRefinementMesh f).triangleCarrier s ⊆ {z | 0 ≤ l z})) (F (M.position v)) =
      meshVertexAngleContribution g F (M.restrictTriangles
        (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})) (F (M.position v)) := by
  have hvsource : M.position v ∈ F.source := by
    apply hM
    apply meshTriangleBasis_subset_support M t
    rw [range_meshTriangleBasis]
    exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩
  rw [lineRefinementMesh_halfspace_vertex_contribution g F M f l hl hmono hF hFi hM,
    add_eq_left]
  apply Finset.sum_eq_zero
  intro u _
  split_ifs
  · apply Finset.sum_eq_zero
    intro q hq
    have hqu := List.mem_toFinset.mp hq
    have hqsource : q ∈ F.source := hM (meshTriangleBasis_subset_support M u
      (((finite_range _).isClosed_convexHull ℝ).frontier_subset
        (localRefinementBoundaryCuts_geometry M f u hqu).1))
    rw [if_neg]
    intro heq
    exact localRefinementBoundaryCuts_ne_usedVertex M f u hqu t v hv
      (F.injOn hqsource hvsource heq)
  · rfl

end PoincareConjecture.Topology.Surface
