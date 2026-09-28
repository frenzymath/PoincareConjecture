import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.GeneralBoundaryFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.FanAncestry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.ConvexSectorFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.CoreSupportGerms

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

theorem refineByLines_append (M : TriangleMesh)
    (first second : List (Plane →ᵃ[ℝ] ℝ)) :
    M.refineByLines (first ++ second) = (M.refineByLines first).refineByLines second := by
  induction first generalizing M with
  | nil => rfl
  | cons f fs ih => exact ih (M.lineRefinementMesh f)

theorem restrictTriangles_exists_usedVertex_of_mem_support
    (M : TriangleMesh) (P : Finset M.Vertex → Prop)
    (u : M.Triangle) (v : M.Vertex) (hv : v ∈ u.1)
    (hq : M.position v ∈ (M.restrictTriangles P).toPlaneComplex.support) :
    ∃ t : (M.restrictTriangles P).Triangle, v ∈ t.1 := by
  rw [TriangleMesh.toPlaneComplex_support] at hq
  obtain ⟨s, hs, hqs⟩ := mem_iUnion₂.mp hq
  let t : M.Triangle := ⟨s, ((M.mem_restrictTriangles_triangles P).mp hs).1⟩
  refine ⟨⟨s, hs⟩, mesh_usedVertex_mem_triangle_of_mem_hull M t u hv ?_⟩
  rw [range_meshTriangleBasis]
  exact hqs

theorem restrictTriangles_compl_support_eventuallyEq
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) {q : Plane}
    (hq : q ∈ interior M.toPlaneComplex.support) :
    (M.restrictTriangles (fun t => ¬P t)).toPlaneComplex.support =ᶠ[𝓝 q]
      (interior (M.restrictTriangles P).toPlaneComplex.support)ᶜ := by
  let N := M.restrictTriangles P
  let C := M.restrictTriangles (fun t => ¬P t)
  have hsub : interior M.toPlaneComplex.support ∩ N.toPlaneComplex.supportᶜ ⊆
      C.toPlaneComplex.support := by
    rintro z ⟨hz, hzN⟩
    have hzM := interior_subset hz
    rw [TriangleMesh.toPlaneComplex_support] at hzM ⊢
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hzM
    refine mem_iUnion₂.mpr ⟨t,
      (M.mem_restrictTriangles_triangles _).mpr ⟨ht, ?_⟩, hzt⟩
    intro htP
    apply hzN
    rw [TriangleMesh.toPlaneComplex_support]
    exact mem_iUnion₂.mpr ⟨t, (M.mem_restrictTriangles_triangles P).mpr ⟨ht, htP⟩, hzt⟩
  filter_upwards [isOpen_interior.mem_nhds hq] with z hz
  apply propext
  constructor
  · intro hzC hzN
    rw [TriangleMesh.toPlaneComplex_support] at hzC
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hzC
    obtain ⟨htM, htP⟩ := (M.mem_restrictTriangles_triangles (fun t => ¬P t)).mp ht
    apply htP (restrictTriangles_retains_incident_triangle M P hzN ⟨t, htM⟩ ?_)
    rw [range_meshTriangleBasis]
    exact hzt
  · intro hzN
    have hzcl : z ∈ closure N.toPlaneComplex.supportᶜ := by
      rw [closure_compl]
      exact hzN
    exact closure_minimal hsub C.toPlaneComplex.isCompact_support.isClosed
      (isOpen_interior.inter_closure ⟨hz, hzcl⟩)

theorem closure_interior_convexSector (c : AffineBasis (Fin 3) ℝ Plane) :
    closure (interior {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) =
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
  have hc : Convex ℝ {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} :=
    ((convex_Ici (0 : ℝ)).affine_preimage (c.coord 1)).inter
      ((convex_Ici (0 : ℝ)).affine_preimage (c.coord 2))
  have hs : IsClosed {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} :=
    (isClosed_le continuous_const (continuous_barycentric_coord c 1)).inter
      (isClosed_le continuous_const (continuous_barycentric_coord c 2))
  have ht : convexHull ℝ (range c) ⊆ {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
    intro z hz
    rw [c.convexHull_eq_nonneg_coord] at hz
    exact ⟨hz 1, hz 2⟩
  have hn : (interior (convexHull ℝ (range c))).Nonempty :=
    (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top.mpr
      (by simpa only [affineSpan_convexHull] using c.tot)
  rw [hc.closure_interior_eq_closure_of_nonempty_interior (hn.mono (interior_mono ht)),
    hs.closure_eq]

theorem restrictTriangles_compl_support_convexSector_germ
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (c : AffineBasis (Fin 3) ℝ Plane)
    (hq : c 0 ∈ interior M.toPlaneComplex.support)
    (hlocal : (M.restrictTriangles P).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      (interior {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})ᶜ) :
    (M.restrictTriangles (fun t => ¬P t)).toPlaneComplex.support =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
  have hcomp := restrictTriangles_compl_support_eventuallyEq M P hq
  have hint := support_eventuallyEq_interior hlocal
  filter_upwards [hcomp, hint] with z hz hi
  change (z ∈ (M.restrictTriangles (fun t => ¬P t)).toPlaneComplex.support) =
    (z ∈ {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})
  change (z ∈ (M.restrictTriangles (fun t => ¬P t)).toPlaneComplex.support) =
    ¬(z ∈ interior (M.restrictTriangles P).toPlaneComplex.support) at hz
  change (z ∈ interior (M.restrictTriangles P).toPlaneComplex.support) =
    (z ∈ interior (interior {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})ᶜ) at hi
  rw [hz, hi]
  simp only [interior_compl, mem_compl_iff, not_not, closure_interior_convexSector]

theorem localRefinementMesh_subset_restriction_iff_parent
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (f : Plane →ᵃ[ℝ] ℝ)
    (t : M.Triangle) (s : (M.localRefinementMesh f t).Triangle) :
    (M.localRefinementMesh f t).triangleCarrier s.1 ⊆
      (M.restrictTriangles P).toPlaneComplex.support ↔ P t.1 := by
  have hsub : (M.localRefinementMesh f t).triangleCarrier s.1 ⊆
      M.triangleCarrier t.1 := by
    intro z hz
    have hz' : z ∈ (M.localRefinementMesh f t).toPlaneComplex.support := by
      rw [TriangleMesh.toPlaneComplex_support]
      exact mem_iUnion₂.mpr ⟨s.1, s.2, hz⟩
    rw [M.localRefinementMesh_support f t] at hz'
    exact hz'
  constructor
  · intro hs
    have hne := (M.localRefinementMesh f t).interior_triangleCarrier_nonempty s
    obtain ⟨z, hz⟩ := hne
    apply restrictTriangles_retains_incident_triangle M P (interior_mono hs hz) t
    simpa only [TriangleMesh.triangleCarrier, range_meshTriangleBasis] using
      hsub (interior_subset hz)
  · intro ht z hz
    rw [TriangleMesh.toPlaneComplex_support]
    exact mem_iUnion₂.mpr ⟨t.1, (M.mem_restrictTriangles_triangles P).mpr ⟨t.2, ht⟩, hsub hz⟩

theorem lineRefinementTriangleEquiv_subset_restriction_iff_parent
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (f : Plane →ᵃ[ℝ] ℝ)
    (t : M.Triangle) (s : (M.localRefinementMesh f t).Triangle) :
    (M.lineRefinementMesh f).triangleCarrier
      (lineRefinementTriangleEquiv M f ⟨t, s⟩).1 ⊆
        (M.restrictTriangles P).toPlaneComplex.support ↔ P t.1 := by
  have hc : (M.lineRefinementMesh f).triangleCarrier
      (lineRefinementTriangleEquiv M f ⟨t, s⟩).1 =
        (M.localRefinementMesh f t).triangleCarrier s.1 := by
    simp only [TriangleMesh.triangleCarrier, ← range_meshTriangleBasis,
      range_meshTriangleBasis_lineRefinementTriangleEquiv]
  rw [hc]
  exact localRefinementMesh_subset_restriction_iff_parent M P f t s

theorem lineRefinementMesh_restriction_support
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (f : Plane →ᵃ[ℝ] ℝ) :
    ((M.lineRefinementMesh f).restrictTriangles
      (fun s => (M.lineRefinementMesh f).triangleCarrier s ⊆
        (M.restrictTriangles P).toPlaneComplex.support)).toPlaneComplex.support =
      (M.restrictTriangles P).toPlaneComplex.support := by
  apply subset_antisymm
  · intro z hz
    rw [TriangleMesh.toPlaneComplex_support] at hz
    obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.mp hz
    exact (((M.lineRefinementMesh f).mem_restrictTriangles_triangles _).mp hs).2 hzs
  · intro z hz
    rw [TriangleMesh.toPlaneComplex_support] at hz
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp hz
    obtain ⟨htM, htP⟩ := (M.mem_restrictTriangles_triangles P).mp ht
    let T : M.Triangle := ⟨t, htM⟩
    have hzl : z ∈ (M.localRefinementMesh f T).toPlaneComplex.support := by
      rw [M.localRefinementMesh_support]
      exact hzt
    rw [← meshTriangleBasis_sources_cover] at hzl
    obtain ⟨s, hzs⟩ := mem_iUnion.mp hzl
    let u := lineRefinementTriangleEquiv M f ⟨T, s⟩
    rw [TriangleMesh.toPlaneComplex_support]
    refine mem_iUnion₂.mpr ⟨u.1,
      ((M.lineRefinementMesh f).mem_restrictTriangles_triangles _).mpr
        ⟨u.2, (lineRefinementTriangleEquiv_subset_restriction_iff_parent M P f T s).mpr htP⟩, ?_⟩
    change z ∈ (M.lineRefinementMesh f).triangleCarrier u.1
    simpa only [u, TriangleMesh.triangleCarrier, ← range_meshTriangleBasis,
      range_meshTriangleBasis_lineRefinementTriangleEquiv] using hzs

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem meshVertexAngleContribution_lineRefinementMesh_restriction
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (f : Plane →ᵃ[ℝ] ℝ) (x : S) :
    meshVertexAngleContribution g F ((M.lineRefinementMesh f).restrictTriangles
      (fun s => (M.lineRefinementMesh f).triangleCarrier s ⊆
        (M.restrictTriangles P).toPlaneComplex.support)) x =
      ∑ t : M.Triangle, if P t.1 then
        meshVertexAngleContribution g F (M.localRefinementMesh f t) x else 0 := by
  rw [meshVertexAngleContribution_restrictTriangles_eq_sum,
    ← (lineRefinementTriangleEquiv M f).sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  simp only [lineRefinementTriangleEquiv_subset_restriction_iff_parent M P f]
  by_cases ht : P t.1
  · simp only [ht, if_true]
    unfold meshVertexAngleContribution
    apply Finset.sum_congr rfl
    intro s _
    exact coordinateTriangle_vertex_contribution_eq_of_range_eq g F _ _
      (range_meshTriangleBasis_lineRefinementTriangleEquiv M f t s) x
  · simp only [ht, if_false, Finset.sum_const_zero]

theorem lineRefinementMesh_restriction_old_vertex_contribution
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (f : Plane →ᵃ[ℝ] ℝ)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (u : M.Triangle) (v : M.Vertex) (hv : v ∈ u.1) :
    meshVertexAngleContribution g F ((M.lineRefinementMesh f).restrictTriangles
      (fun s => (M.lineRefinementMesh f).triangleCarrier s ⊆
        (M.restrictTriangles P).toPlaneComplex.support)) (F (M.position v)) =
      meshVertexAngleContribution g F (M.restrictTriangles P) (F (M.position v)) := by
  have hvsource : M.position v ∈ F.source := by
    apply hM
    apply meshTriangleBasis_subset_support M u
    rw [range_meshTriangleBasis]
    exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩
  rw [meshVertexAngleContribution_lineRefinementMesh_restriction,
    meshVertexAngleContribution_restrictTriangles_eq_sum]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs
  · rw [localRefinementMesh_vertex_contribution_finset g F M f t hF hFi
      ((meshTriangleBasis_subset_support M t).trans hM), add_eq_left]
    apply Finset.sum_eq_zero
    intro q hq
    have hqu := List.mem_toFinset.mp hq
    have hqsource : q ∈ F.source := hM (meshTriangleBasis_subset_support M t
      (((finite_range _).isClosed_convexHull ℝ).frontier_subset
        (localRefinementBoundaryCuts_geometry M f t hqu).1))
    rw [if_neg]
    intro heq
    exact localRefinementBoundaryCuts_ne_usedVertex M f t hqu u v hv
      (F.injOn hqsource hvsource heq)
  · rfl

theorem exists_refined_restriction_support_and_old_contribution
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source) :
    ∃ Q : Finset (M.refineByLines lines).Vertex → Prop,
      ((M.refineByLines lines).restrictTriangles Q).toPlaneComplex.support =
        (M.restrictTriangles P).toPlaneComplex.support ∧
      ∀ (u : M.Triangle) (v : M.Vertex), v ∈ u.1 →
        meshVertexAngleContribution g F ((M.refineByLines lines).restrictTriangles Q)
          (F (M.position v)) =
            meshVertexAngleContribution g F (M.restrictTriangles P) (F (M.position v)) := by
  induction lines generalizing M with
  | nil => exact ⟨P, rfl, fun _ _ _ => rfl⟩
  | cons f fs ih =>
    let Q := fun s => (M.lineRefinementMesh f).triangleCarrier s ⊆
      (M.restrictTriangles P).toPlaneComplex.support
    obtain ⟨R, hRs, hRv⟩ := ih (M.lineRefinementMesh f) Q
      (by simpa only [M.lineRefinementMesh_support f] using hM)
    refine ⟨R, hRs.trans (lineRefinementMesh_restriction_support M P f), ?_⟩
    intro u v hv
    obtain ⟨t, ht⟩ := lineRefinementMesh_oldVertex_mem_triangle M f u v hv
    exact (hRv t (M.oldRefinedVertex f v) ht).trans
      (lineRefinementMesh_restriction_old_vertex_contribution g F M P f hF hFi hM u v hv)

theorem exists_refined_restriction_comparing_selected_old_vertex
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : (M.restrictTriangles P).toPlaneComplex.support ⊆ F.source)
    (u : (M.restrictTriangles P).Triangle) (v : (M.restrictTriangles P).Vertex)
    (hv : v ∈ u.1) :
    ∃ Q : Finset (M.refineByLines lines).Vertex → Prop,
      ((M.refineByLines lines).restrictTriangles Q).toPlaneComplex.support =
        (M.restrictTriangles P).toPlaneComplex.support ∧
      meshVertexAngleContribution g F ((M.restrictTriangles P).refineByLines lines)
        (F (M.position v)) =
          meshVertexAngleContribution g F ((M.refineByLines lines).restrictTriangles Q)
            (F (M.position v)) := by
  let q := M.position v
  have hq : q ∈ F.source := by
    apply hsource
    apply meshTriangleBasis_subset_support (M.restrictTriangles P) u
    rw [range_meshTriangleBasis]
    exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩
  let G := coordinateTangentMetric g F hF hFi q hq
  obtain ⟨Q, hQs, hQv⟩ := exists_refined_restriction_support_and_old_contribution
    G (OpenPartialHomeomorph.refl Plane) M P lines contMDiffOn_id contMDiffOn_id (by simp)
  refine ⟨Q, hQs, ?_⟩
  have hactual : ((M.restrictTriangles P).refineByLines lines).toPlaneComplex.support ⊆
      F.source := by
    simpa only [TriangleMesh.refineByLines_support] using hsource
  have haux : ((M.refineByLines lines).restrictTriangles Q).toPlaneComplex.support ⊆
      F.source := hQs ▸ hsource
  rw [meshVertexAngleContribution_eq_tangentMetric g F hF hFi q hq _ hactual,
    meshVertexAngleContribution_eq_tangentMetric g F hF hFi q hq _ haux]
  have hpres := refineByLines_vertex_contribution_old_vertex
    G (OpenPartialHomeomorph.refl Plane) (M.restrictTriangles P) lines
    contMDiffOn_id contMDiffOn_id (by simp) u v hv
  exact hpres.trans (hQv (restrictTrianglesTriangleEquiv M P u).1 v hv).symm

theorem convex_subset_halfspace_of_local
    {C : Set Plane} (hC : Convex ℝ C) {q : Plane} (hq : q ∈ C)
    (l : Plane →ᵃ[ℝ] ℝ) (hlq : l q = 0)
    (hlocal : ∀ᶠ z in 𝓝 q, z ∈ C → 0 ≤ l z) : C ⊆ {z | 0 ≤ l z} := by
  intro z hz
  let path : ℝ → Plane := AffineMap.lineMap q z
  have hp : Continuous path := by
    simp only [path]
    fun_prop
  have he : ∀ᶠ r in 𝓝 (0 : ℝ), path r ∈ C → 0 ≤ l (path r) := by
    have hpt : Tendsto path (𝓝 (0 : ℝ)) (𝓝 q) := by
      simpa only [path, AffineMap.lineMap_apply_zero] using
        hp.continuousAt.tendsto (x := (0 : ℝ))
    exact hpt.eventually hlocal
  have hlt : ∀ᶠ r in 𝓝 (0 : ℝ), r < 1 := Iio_mem_nhds (by norm_num)
  have hnear : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 < r ∧ r < 1 ∧ (path r ∈ C → 0 ≤ l (path r)) := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,
      hlt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hr hr1 hr0
    exact ⟨hr0, hr1, hr⟩
  obtain ⟨r, hr0, hr1, hr⟩ := hnear.exists
  have hpr : path r ∈ C := by
    simp only [path, AffineMap.lineMap_apply_module]
    exact hC hq hz (sub_nonneg.mpr hr1.le) hr0.le (by ring)
  have hnonneg := hr hpr
  simp only [path, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
    hlq, mul_zero, zero_add] at hnonneg
  exact nonneg_of_mul_nonneg_right hnonneg hr0

theorem mesh_exists_usedVertex_of_convexSector_germ
    (M : TriangleMesh) (c : AffineBasis (Fin 3) ℝ Plane)
    (hq : c 0 ∈ M.toPlaneComplex.support)
    (hlocal : ∀ᶠ z in 𝓝 (c 0), z ∈ M.toPlaneComplex.support →
      0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z) :
    ∃ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 ∧ M.position v = c 0 := by
  rw [TriangleMesh.toPlaneComplex_support] at hq
  obtain ⟨t, ht, hqt⟩ := mem_iUnion₂.mp hq
  let T : M.Triangle := ⟨t, ht⟩
  have hsub : M.triangleCarrier t ⊆ M.toPlaneComplex.support := by
    intro z hz
    rw [TriangleMesh.toPlaneComplex_support]
    exact mem_iUnion₂.mpr ⟨t, ht, hz⟩
  have hside (i : Fin 3) (hi : i = 1 ∨ i = 2) :
      M.triangleCarrier t ⊆ {z | 0 ≤ c.coord i z} := by
    apply convex_subset_halfspace_of_local (convex_convexHull ℝ _) hqt (c.coord i)
    · rcases hi with rfl | rfl <;> norm_num [AffineBasis.coord_apply, Fin.ext_iff]
    · filter_upwards [hlocal] with z hz hzt
      rcases hi with rfl | rfl
      · exact (hz (hsub hzt)).1
      · exact (hz (hsub hzt)).2
  let l : Plane →ᵃ[ℝ] ℝ := c.coord 1 + c.coord 2
  let points : Finset Plane := t.image M.position
  have hn : ∀ z ∈ points, 0 ≤ l z := by
    intro z hz
    have hzt : z ∈ M.triangleCarrier t := by
      apply subset_convexHull ℝ _
      simpa only [points, Finset.mem_image, mem_image, Finset.mem_coe] using hz
    exact add_nonneg (hside 1 (Or.inl rfl) hzt) (hside 2 (Or.inr rfl) hzt)
  have hcorner : c 0 ∈ convexHull ℝ (points.filter (fun z => l z = 0) : Set Plane) := by
    rw [← convexHull_inter_affine_zero_of_nonneg points l hn]
    refine ⟨?_, ?_⟩
    · simpa only [points, Finset.coe_image] using hqt
    · norm_num [l, AffineBasis.coord_apply, Fin.ext_iff]
  have hne : (points.filter fun z => l z = 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hcorner
    simp at hcorner
  obtain ⟨z, hz⟩ := hne
  obtain ⟨hzpoints, hzero⟩ := Finset.mem_filter.mp hz
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hzpoints
  have hvt : M.position v ∈ M.triangleCarrier t := subset_convexHull ℝ _ ⟨v, hv, rfl⟩
  have hv1 : 0 ≤ c.coord 1 (M.position v) := hside 1 (Or.inl rfl) hvt
  have hv2 : 0 ≤ c.coord 2 (M.position v) := hside 2 (Or.inr rfl) hvt
  change c.coord 1 (M.position v) + c.coord 2 (M.position v) = 0 at hzero
  have h1 : c.coord 1 (M.position v) = 0 := by linarith
  have h2 : c.coord 2 (M.position v) = 0 := by linarith
  refine ⟨T, v, hv, c.ext_elem fun i => ?_⟩
  have hs := c.sum_coord_apply_eq_one (M.position v)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change c.coord 0 (M.position v) + (c.coord 1 (M.position v) + c.coord 2 (M.position v)) = 1 at hs
  fin_cases i
  · change c.coord 0 (M.position v) = c.coord 0 (c 0)
    norm_num [AffineBasis.coord_apply]
    linarith
  · change c.coord 1 (M.position v) = c.coord 1 (c 0)
    simpa only [AffineBasis.coord_apply, show (1 : Fin 3) ≠ 0 by decide, if_false] using h1
  · change c.coord 2 (M.position v) = c.coord 2 (c 0)
    simpa only [AffineBasis.coord_apply, show (2 : Fin 3) ≠ 0 by decide, if_false] using h2

theorem single_refineByLines_restrict_refineByLines_convexSector_fan_of_source
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b c : AffineBasis (Fin 3) ℝ Plane)
    (first second : List (Plane →ᵃ[ℝ] ℝ))
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines first).Vertex → Prop)
    (h1 : ((TriangleMesh.single b b.ind).refineByLines (first ++ second)).IsMonochromatic (c.coord 1))
    (h2 : ((TriangleMesh.single b b.ind).refineByLines (first ++ second)).IsMonochromatic (c.coord 2))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : (((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).toPlaneComplex.support ⊆
      F.source)
    (hq : c 0 ∈ (((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).toPlaneComplex.support)
    (hqint : c 0 ∈ interior (convexHull ℝ (range b)))
    (hlocal : (((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).toPlaneComplex.support
      =ᶠ[𝓝 (c 0)] {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    meshVertexAngleContribution g F
      ((((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).refineByLines second)
      (F (c 0)) = g.cornerAngle (F (c 0))
        ((mfderiv (𝓡 2) (𝓡 2) F (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) F (c 0)) (c 2 - c 0)) := by
  obtain ⟨u, v, hv, hpos⟩ := mesh_exists_usedVertex_of_convexSector_germ
    (((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P) c hq
    (hlocal.mono fun z hz h => hz.mp h)
  have hex := exists_refined_restriction_comparing_selected_old_vertex g F
    ((TriangleMesh.single b b.ind).refineByLines first) P second hF hFi hsource u v hv
  rw [← refineByLines_append] at hex
  obtain ⟨Q, hQs, hQv⟩ := hex
  change ((TriangleMesh.single b b.ind).refineByLines first).position v = c 0 at hpos
  rw [hpos] at hQv
  rw [hQv]
  have hQq : c 0 ∈ (((TriangleMesh.single b b.ind).refineByLines (first ++ second)).restrictTriangles Q).toPlaneComplex.support :=
    hQs.symm ▸ hq
  have hQlocal : (((TriangleMesh.single b b.ind).refineByLines (first ++ second)).restrictTriangles Q).toPlaneComplex.support
      =ᶠ[𝓝 (c 0)] {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := hQs.symm ▸ hlocal
  obtain ⟨t, a, ha, ha0⟩ := mesh_exists_usedVertex_of_convexSector_germ
    (((TriangleMesh.single b b.ind).refineByLines (first ++ second)).restrictTriangles Q) c hQq
    (hQlocal.mono fun z hz h => hz.mp h)
  have hfan := single_refineByLines_restrict_convexSector_vertex_fan_of_source
    g F b c (first ++ second) Q h1 h2 hF hFi (hQs.symm ▸ hsource) t a ha
    (ha0.symm ▸ hqint) ha0 (ha0.symm ▸ hQlocal)
  dsimp only at hfan
  have hright := congrArg (fun z : Plane => g.cornerAngle (F z)
    ((mfderiv (𝓡 2) (𝓡 2) F z) (c 1 - c 0))
    ((mfderiv (𝓡 2) (𝓡 2) F z) (c 2 - c 0))) ha0
  rw [hright] at hfan
  simpa only [ha0] using hfan

theorem single_refineByLines_restrict_straight_boundary_fan_of_monochromatic_of_source
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l)
    (hmono : ((TriangleMesh.single b b.ind).refineByLines lines).IsMonochromatic l)
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines lines).Vertex → Prop)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support ⊆
      F.source)
    (u : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Triangle)
    (a : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Vertex)
    (hau : a ∈ u.1)
    (haint : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a ∈
      interior (convexHull ℝ (range b)))
    (hal : l ((((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a) = 0)
    (hlocal : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support
      =ᶠ[𝓝 ((((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a)]
        {z | 0 ≤ l z}) :
    meshVertexAngleContribution g F
      (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P)
      (F ((((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position a)) =
        Real.pi := by
  let M := (TriangleMesh.single b b.ind).refineByLines lines
  let q := (M.restrictTriangles P).position a
  have hq : q ∈ F.source := by
    apply hsource
    apply meshTriangleBasis_subset_support (M.restrictTriangles P) u
    rw [range_meshTriangleBasis]
    exact subset_convexHull ℝ _ ⟨a, hau, rfl⟩
  let G := coordinateTangentMetric g F hF hFi q hq
  have hqint : q ∈ interior M.toPlaneComplex.support := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using haint
  rw [meshVertexAngleContribution_eq_tangentMetric g F hF hFi q hq _ hsource]
  have hglue := meshVertexAngleContribution_restrictTriangles_eq_of_support_eventuallyEq
    G (OpenPartialHomeomorph.refl Plane) M P
    (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ l z}) (by simp) (q := q) (by simp)
    (hlocal.trans (halfspace_restriction_support_eventuallyEq M l hl hmono hqint).symm)
  apply hglue.trans
  exact single_refineByLines_halfspace_vertex_fan_of_monochromatic G (OpenPartialHomeomorph.refl Plane)
    b lines l hl hmono contMDiffOn_id contMDiffOn_id (by simp)
    (restrictTrianglesTriangleEquiv M P u).1 a hau haint hal

theorem single_refineByLines_restrict_refineByLines_straight_boundary_fan_of_source
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane)
    (first second : List (Plane →ᵃ[ℝ] ℝ))
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines first).Vertex → Prop)
    (l : Plane →ᵃ[ℝ] ℝ) (hl : Function.Surjective l)
    (hmono : ((TriangleMesh.single b b.ind).refineByLines (first ++ second)).IsMonochromatic l)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : (((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).toPlaneComplex.support ⊆
      F.source)
    (u : ((((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).refineByLines second).Triangle)
    (a : ((((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).refineByLines second).Vertex)
    (hau : a ∈ u.1)
    (haint : ((((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).refineByLines second).position a ∈
      interior (convexHull ℝ (range b)))
    (hal : l (((((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).refineByLines second).position a) = 0)
    (hlocal : (((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).toPlaneComplex.support
      =ᶠ[𝓝 (((((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).refineByLines second).position a)]
        {z | 0 ≤ l z}) :
    meshVertexAngleContribution g F
      ((((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).refineByLines second)
      (F (((((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).refineByLines second).position a)) =
        Real.pi := by
  let M := (TriangleMesh.single b b.ind).refineByLines first
  let N := M.restrictTriangles P
  let q := (N.refineByLines second).position a
  have hnot : q ∉ interior N.toPlaneComplex.support := by
    intro hq
    have hi := (Filter.EventuallyEq.mem_interior_iff hlocal).mp hq
    change q ∈ interior (l ⁻¹' Ici (0 : ℝ)) at hi
    rw [← (l.isOpenMap l.continuous_of_finiteDimensional hl).preimage_interior_eq_interior_preimage
      l.continuous_of_finiteDimensional, interior_Ici] at hi
    exact (ne_of_gt hi) hal
  rcases refineByLines_vertex_contribution_old_or_new g F N second hF hFi hsource u a hau with
    ⟨t, v, hv, hpos, _⟩ | hnew
  · have hex := exists_refined_restriction_comparing_selected_old_vertex
      g F M P second hF hFi hsource t v hv
    dsimp only [M] at hex
    rw [← refineByLines_append] at hex
    obtain ⟨Q, hQs, hQv⟩ := hex
    change M.position v = q at hpos
    rw [hpos] at hQv
    rw [hQv]
    have hused := refineByLines_exists_usedVertex M second
      (restrictTrianglesTriangleEquiv M P t).1 v hv
    dsimp only [M] at hused
    rw [← refineByLines_append] at hused
    obtain ⟨w, x, hx, hxpos⟩ := hused
    have hxq : ((TriangleMesh.single b b.ind).refineByLines (first ++ second)).position x = q :=
      hxpos.trans hpos
    have hqN : q ∈ N.toPlaneComplex.support := by
      rw [← hpos]
      apply meshTriangleBasis_subset_support N t
      rw [range_meshTriangleBasis]
      exact subset_convexHull ℝ _ ⟨v, hv, rfl⟩
    obtain ⟨z, hz⟩ := restrictTriangles_exists_usedVertex_of_mem_support
      ((TriangleMesh.single b b.ind).refineByLines (first ++ second)) Q w x hx
      (by rw [hxq, hQs]; exact hqN)
    have hfan := single_refineByLines_restrict_straight_boundary_fan_of_monochromatic_of_source
      g F b (first ++ second) l hl hmono Q hF hFi (hQs.symm ▸ hsource) z x hz
      (hxq.symm ▸ haint) (hxq.symm ▸ hal) (by rw [hQs]; exact hxq.symm ▸ hlocal)
    change meshVertexAngleContribution g F
      (((TriangleMesh.single b b.ind).refineByLines (first ++ second)).restrictTriangles Q)
      (F (((TriangleMesh.single b b.ind).refineByLines (first ++ second)).position x)) = Real.pi at hfan
    rwa [hxq] at hfan
  · change meshVertexAngleContribution g F (N.refineByLines second) (F q) =
      if q ∈ interior N.toPlaneComplex.support then 2 * Real.pi else Real.pi at hnew
    simpa only [if_neg hnot] using hnew

theorem single_refineByLines_restrict_refineByLines_reflexSector_fan_of_source
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b c : AffineBasis (Fin 3) ℝ Plane)
    (first second : List (Plane →ᵃ[ℝ] ℝ))
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines first).Vertex → Prop)
    (h1 : ((TriangleMesh.single b b.ind).refineByLines (first ++ second)).IsMonochromatic (c.coord 1))
    (h2 : ((TriangleMesh.single b b.ind).refineByLines (first ++ second)).IsMonochromatic (c.coord 2))
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : (((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).toPlaneComplex.support ⊆
      F.source)
    (hq : c 0 ∈ (((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).toPlaneComplex.support)
    (hqint : c 0 ∈ interior (convexHull ℝ (range b)))
    (hlocal : (((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).toPlaneComplex.support
      =ᶠ[𝓝 (c 0)] (interior {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z})ᶜ) :
    meshVertexAngleContribution g F
      ((((TriangleMesh.single b b.ind).refineByLines first).restrictTriangles P).refineByLines second)
      (F (c 0)) = 2 * Real.pi - g.cornerAngle (F (c 0))
        ((mfderiv (𝓡 2) (𝓡 2) F (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) F (c 0)) (c 2 - c 0)) := by
  let M := (TriangleMesh.single b b.ind).refineByLines first
  let N := M.restrictTriangles P
  let C := M.restrictTriangles (fun t => ¬P t)
  have hqM : c 0 ∈ interior M.toPlaneComplex.support := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using hqint
  have hc := restrictTriangles_compl_support_convexSector_germ M P c hqM hlocal
  have hqC : c 0 ∈ C.toPlaneComplex.support := by
    have he := hc.eq_of_nhds
    change (c 0 ∈ C.toPlaneComplex.support) = (0 ≤ c.coord 1 (c 0) ∧ 0 ≤ c.coord 2 (c 0)) at he
    rw [he]
    norm_num [AffineBasis.coord_apply, Fin.ext_iff]
  obtain ⟨t, v, hv, hpos⟩ := mesh_exists_usedVertex_of_convexSector_germ C c hqC
    (hc.mono fun z hz h => hz.mp h)
  let u : M.Triangle := (restrictTrianglesTriangleEquiv M (fun t => ¬P t) t).1
  have hposM : M.position v = c 0 := hpos
  obtain ⟨s, hs⟩ := restrictTriangles_exists_usedVertex_of_mem_support M P u v hv
    (hposM.symm ▸ hq)
  have hqsource : c 0 ∈ F.source := hsource hq
  let G := coordinateTangentMetric g F hF hFi (c 0) hqsource
  have hactualsource : (N.refineByLines second).toPlaneComplex.support ⊆ F.source := by
    simpa only [TriangleMesh.refineByLines_support] using hsource
  rw [meshVertexAngleContribution_eq_tangentMetric g F hF hFi (c 0) hqsource _ hactualsource]
  have hN := refineByLines_vertex_contribution_old_vertex G (OpenPartialHomeomorph.refl Plane)
    N second contMDiffOn_id contMDiffOn_id (by simp) s v hs
  have hC := refineByLines_vertex_contribution_old_vertex G (OpenPartialHomeomorph.refl Plane)
    C second contMDiffOn_id contMDiffOn_id (by simp) t v hv
  change meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane)
    (N.refineByLines second) (M.position v) =
      meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane) N (M.position v) at hN
  change meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane)
    (C.refineByLines second) (M.position v) =
      meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane) C (M.position v) at hC
  rw [hposM] at hN hC
  have hCeq : C = @TriangleMesh.restrictTriangles M (fun t => ¬P t)
      (fun t => Classical.propDecidable (¬P t)) := by
    dsimp only [C]
    congr 1
  have hw := single_refineByLines_restrict_refineByLines_convexSector_fan_of_source
    G (OpenPartialHomeomorph.refl Plane) b c first second (fun t => ¬P t) h1 h2
    contMDiffOn_id contMDiffOn_id (by simp) (by rw [← hCeq]; exact hqC) hqint
    (by rw [← hCeq]; exact hc)
  rw [← hCeq] at hw
  change meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane)
    (C.refineByLines second) (c 0) =
      G.cornerAngle (c 0) ((mfderiv (𝓡 2) (𝓡 2) id (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) id (c 0)) (c 2 - c 0)) at hw
  rw [mfderiv_id] at hw
  have hsum := meshVertexAngleContribution_restrictTriangles_add_compl
    G (OpenPartialHomeomorph.refl Plane) M P (c 0)
  have hall := single_refineByLines_interior_vertex_fan G (OpenPartialHomeomorph.refl Plane)
    b first contMDiffOn_id contMDiffOn_id (by simp) u v hv (hposM.symm ▸ hqM)
  change meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane) M (M.position v) =
    2 * Real.pi at hall
  rw [hposM] at hall
  rw [hall] at hsum
  have hangle : G.cornerAngle (c 0) (c 1 - c 0) (c 2 - c 0) =
      g.cornerAngle (F (c 0)) ((mfderiv (𝓡 2) (𝓡 2) F (c 0)) (c 1 - c 0))
        ((mfderiv (𝓡 2) (𝓡 2) F (c 0)) (c 2 - c 0)) := by
    simp only [G, RiemannianMetric.cornerAngle, coordinateTangentMetric_inner, map_smul, smul_apply]
  change meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane) (N.refineByLines second)
    (c 0) = _
  change meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane) N (c 0) +
    meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane) C (c 0) = 2 * Real.pi at hsum
  change meshVertexAngleContribution G (OpenPartialHomeomorph.refl Plane) (C.refineByLines second)
    (c 0) = G.cornerAngle (c 0) (c 1 - c 0) (c 2 - c 0) at hw
  rw [hangle] at hw
  linarith

end PoincareConjecture.Topology.Surface
