import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.HalfplaneFans








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface



theorem single_lineRefinementMesh_usedVertex_not_mem_interior
    (b : AffineBasis (Fin 3) ℝ Plane) (l : Plane →ᵃ[ℝ] ℝ)
    (u : ((TriangleMesh.single b b.ind).lineRefinementMesh l).Triangle)
    (x : ((TriangleMesh.single b b.ind).lineRefinementMesh l).Vertex) (hx : x ∈ u.1) :
    ((TriangleMesh.single b b.ind).lineRefinementMesh l).position x ∉
      interior (convexHull ℝ (range b)) := by
  obtain ⟨t, ⟨v, hv, hpos⟩ | hcut⟩ :=
    lineRefinementMesh_vertex_old_or_cut (TriangleMesh.single b b.ind) l u x hx
  · rw [hpos, b.interior_convexHull]
    change ¬∀ i : Fin 3, 0 < b.coord i (b v)
    intro hint
    have h0 := hint 0
    have h1 := hint 1
    fin_cases v
    · norm_num [AffineBasis.coord_apply, Fin.ext_iff] at h1
    · norm_num [AffineBasis.coord_apply, Fin.ext_iff] at h0
    · norm_num [AffineBasis.coord_apply, Fin.ext_iff] at h0
  · have ht : t.1 = Finset.univ := Finset.mem_singleton.mp t.2
    have hrange : range (meshTriangleBasis (TriangleMesh.single b b.ind) t) = range b := by
      rw [range_meshTriangleBasis, ht]
      simp only [Finset.coe_univ, image_univ]
      rfl
    have hfront := (localRefinementBoundaryCuts_geometry (TriangleMesh.single b b.ind) l t hcut).1
    rw [hrange] at hfront
    exact hfront.2

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem lineRefinementMesh_halfspace_vertex_fan_of_initial
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (hfan : ∀ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 →
      M.position v ∈ interior M.toPlaneComplex.support → l (M.position v) = 0 →
      meshVertexAngleContribution g F (M.restrictTriangles
        (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})) (F (M.position v)) = Real.pi)
    (u : (M.lineRefinementMesh f).Triangle) (x : (M.lineRefinementMesh f).Vertex)
    (hx : x ∈ u.1)
    (hxint : (M.lineRefinementMesh f).position x ∈
      interior (M.lineRefinementMesh f).toPlaneComplex.support)
    (hxl : l ((M.lineRefinementMesh f).position x) = 0) :
    meshVertexAngleContribution g F ((M.lineRefinementMesh f).restrictTriangles
      (fun s => (M.lineRefinementMesh f).triangleCarrier s ⊆ {z | 0 ≤ l z}))
      (F ((M.lineRefinementMesh f).position x)) = Real.pi := by
  rw [M.lineRefinementMesh_support f] at hxint
  obtain ⟨t, ⟨v, hv, hpos⟩ | hcut⟩ := lineRefinementMesh_vertex_old_or_cut M f u x hx
  · rw [hpos] at hxint hxl ⊢
    rw [lineRefinementMesh_halfspace_old_vertex_contribution g F M f l hl hmono hF hFi hM t v hv]
    exact hfan t v hv hxint hxl
  · exact lineRefinementMesh_halfspace_new_vertex_fan g F M f l hl hmono t hcut hxint hxl hF hFi hM



theorem refineByLines_halfspace_vertex_fan_of_initial
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (lines : List (Plane →ᵃ[ℝ] ℝ)) (l : Plane →ᵃ[ℝ] ℝ)
    (hl : Function.Surjective l) (hmono : M.IsMonochromatic l)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source)
    (hfan : ∀ (t : M.Triangle) (v : M.Vertex), v ∈ t.1 →
      M.position v ∈ interior M.toPlaneComplex.support → l (M.position v) = 0 →
      meshVertexAngleContribution g F (M.restrictTriangles
        (fun s => M.triangleCarrier s ⊆ {z | 0 ≤ l z})) (F (M.position v)) = Real.pi)
    (u : (M.refineByLines lines).Triangle) (x : (M.refineByLines lines).Vertex)
    (hx : x ∈ u.1)
    (hxint : (M.refineByLines lines).position x ∈
      interior (M.refineByLines lines).toPlaneComplex.support)
    (hxl : l ((M.refineByLines lines).position x) = 0) :
    meshVertexAngleContribution g F ((M.refineByLines lines).restrictTriangles
      (fun s => (M.refineByLines lines).triangleCarrier s ⊆ {z | 0 ≤ l z}))
      (F ((M.refineByLines lines).position x)) = Real.pi := by
  induction lines generalizing M with
  | nil => exact hfan u x hx hxint hxl
  | cons f fs ih =>
    apply ih (M.lineRefinementMesh f) (M.lineRefinementMesh_preserves_monochromatic f l hmono)
      (by simpa only [M.lineRefinementMesh_support f] using hM)
      (lineRefinementMesh_halfspace_vertex_fan_of_initial g F M f l hl hmono hF hFi hM hfan)
      u x hx hxint hxl




theorem single_refineByLines_halfspace_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (l : Plane →ᵃ[ℝ] ℝ)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) (hl : Function.Surjective l)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (u : ((TriangleMesh.single b b.ind).refineByLines (l :: lines)).Triangle)
    (x : ((TriangleMesh.single b b.ind).refineByLines (l :: lines)).Vertex)
    (hx : x ∈ u.1)
    (hxint : ((TriangleMesh.single b b.ind).refineByLines (l :: lines)).position x ∈
      interior (convexHull ℝ (range b)))
    (hxl : l (((TriangleMesh.single b b.ind).refineByLines (l :: lines)).position x) = 0) :
    meshVertexAngleContribution g F
      (((TriangleMesh.single b b.ind).refineByLines (l :: lines)).restrictTriangles
        (fun s => ((TriangleMesh.single b b.ind).refineByLines (l :: lines)).triangleCarrier s ⊆
          {z | 0 ≤ l z}))
      (F (((TriangleMesh.single b b.ind).refineByLines (l :: lines)).position x)) = Real.pi := by
  apply refineByLines_halfspace_vertex_fan_of_initial g F
    ((TriangleMesh.single b b.ind).lineRefinementMesh l) lines l hl
    ((TriangleMesh.single b b.ind).lineRefinementMesh_isMonochromatic l) hF hFi
    (by simpa only [TriangleMesh.lineRefinementMesh_support, TriangleMesh.single_support] using hb)
    ?_ u x hx ?_ hxl
  · intro t v hv hvint _
    exact False.elim (single_lineRefinementMesh_usedVertex_not_mem_interior b l t v hv
      (by simpa only [TriangleMesh.lineRefinementMesh_support, TriangleMesh.single_support] using hvint))
  · simpa only [TriangleMesh.refineByLines_support, TriangleMesh.lineRefinementMesh_support,
      TriangleMesh.single_support, TriangleMesh.refineByLines] using hxint




theorem single_refineByLines_restrict_straight_boundary_fan_of_source
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (l : Plane →ᵃ[ℝ] ℝ)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) (hl : Function.Surjective l)
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines (l :: lines)).Vertex → Prop)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : (((TriangleMesh.single b b.ind).refineByLines (l :: lines)).restrictTriangles P).toPlaneComplex.support ⊆
      F.source)
    (u : (((TriangleMesh.single b b.ind).refineByLines (l :: lines)).restrictTriangles P).Triangle)
    (x : (((TriangleMesh.single b b.ind).refineByLines (l :: lines)).restrictTriangles P).Vertex)
    (hx : x ∈ u.1)
    (hxint : (((TriangleMesh.single b b.ind).refineByLines (l :: lines)).restrictTriangles P).position x ∈
      interior (convexHull ℝ (range b)))
    (hxl : l ((((TriangleMesh.single b b.ind).refineByLines (l :: lines)).restrictTriangles P).position x) = 0)
    (hq : (((TriangleMesh.single b b.ind).refineByLines (l :: lines)).restrictTriangles P).position x ∈ F.source)
    (hlocal : (((TriangleMesh.single b b.ind).refineByLines (l :: lines)).restrictTriangles P).toPlaneComplex.support
      =ᶠ[𝓝 ((((TriangleMesh.single b b.ind).refineByLines (l :: lines)).restrictTriangles P).position x)]
        {z | 0 ≤ l z}) :
    meshVertexAngleContribution g F
      (((TriangleMesh.single b b.ind).refineByLines (l :: lines)).restrictTriangles P)
      (F ((((TriangleMesh.single b b.ind).refineByLines (l :: lines)).restrictTriangles P).position x)) =
        Real.pi := by
  let M := (TriangleMesh.single b b.ind).refineByLines (l :: lines)
  let q := (M.restrictTriangles P).position x
  let G := coordinateTangentMetric g F hF hFi q hq
  have hM : M.IsMonochromatic l :=
    (TriangleMesh.single b b.ind).refineByLines_isMonochromatic_of_mem (l :: lines) (by simp)
  have hqint : q ∈ interior M.toPlaneComplex.support := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using hxint
  rw [meshVertexAngleContribution_eq_tangentMetric g F hF hFi q hq _ hsource]
  have hglue := meshVertexAngleContribution_restrictTriangles_eq_of_support_eventuallyEq
    G (OpenPartialHomeomorph.refl Plane) M P
    (fun t => M.triangleCarrier t ⊆ {z | 0 ≤ l z}) (by simp) (q := q) (by simp)
    (hlocal.trans (halfspace_restriction_support_eventuallyEq M l hl hM hqint).symm)
  apply hglue.trans
  apply single_refineByLines_halfspace_vertex_fan G (OpenPartialHomeomorph.refl Plane)
    b l lines hl contMDiffOn_id contMDiffOn_id (by simp)
    (restrictTrianglesTriangleEquiv M P u).1 x hx
  · exact hxint
  · exact hxl

end PoincareConjecture.Topology.Surface
