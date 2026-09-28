import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.InitialFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.TangentMetric
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.PolygonalDomains










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface


theorem mesh_triangle_inter_frontier (M : TriangleMesh)
    (t u : M.Triangle) (htu : t ≠ u) :
    convexHull ℝ (range (meshTriangleBasis M t)) ∩
      convexHull ℝ (range (meshTriangleBasis M u)) ⊆
        frontier (convexHull ℝ (range (meshTriangleBasis M t))) := by
  rcases meshTriangleBasis_pair_intersections M t u htu with
    ⟨k, l, hk, _⟩ | ⟨v, hv, hsub⟩
  · rw [hk, frontier_convexHull_affineBasis_fin3_segments]
    exact subset_iUnion (fun i : Fin 3 => affineSegment ℝ
      (meshTriangleBasis M t (i.succAbove 0)) (meshTriangleBasis M t (i.succAbove 1))) k
  · intro z hz
    rw [mem_singleton_iff.mp (hsub hz)]
    obtain ⟨i, hi⟩ : M.position v ∈ range (meshTriangleBasis M t) := by
      rw [range_meshTriangleBasis]
      exact ⟨v, hv, rfl⟩
    rw [← hi]
    refine ⟨subset_closure (subset_convexHull ℝ _ (mem_range_self i)), ?_⟩
    intro hint
    rw [(meshTriangleBasis M t).interior_convexHull] at hint
    have h0 := hint 0
    have h1 := hint 1
    fin_cases i
    · norm_num [AffineBasis.coord_apply, Fin.ext_iff] at h1
    · norm_num [AffineBasis.coord_apply, Fin.ext_iff] at h0
    · norm_num [AffineBasis.coord_apply, Fin.ext_iff] at h0


theorem restrictTriangles_support_subset (M : TriangleMesh)
    (P : Finset M.Vertex → Prop) :
    (M.restrictTriangles P).toPlaneComplex.support ⊆ M.toPlaneComplex.support := by
  rw [TriangleMesh.toPlaneComplex_support, TriangleMesh.toPlaneComplex_support]
  rintro q hq
  obtain ⟨t, ht, hqt⟩ := mem_iUnion₂.mp hq
  exact mem_iUnion₂.mpr ⟨t, ((M.mem_restrictTriangles_triangles P).mp ht).1, hqt⟩



theorem restrictTriangles_retains_incident_triangle (M : TriangleMesh)
    (P : Finset M.Vertex → Prop) {q : Plane}
    (hq : q ∈ interior (M.restrictTriangles P).toPlaneComplex.support)
    (t : M.Triangle) (hqt : q ∈ convexHull ℝ (range (meshTriangleBasis M t))) : P t.1 := by
  have hqcl : q ∈ closure (interior (M.triangleCarrier t.1)) := by
    rw [M.closure_interior_triangleCarrier t]
    simpa only [TriangleMesh.triangleCarrier, range_meshTriangleBasis] using hqt
  obtain ⟨z, hzS, hzt⟩ := Set.Nonempty.of_closure
    ⟨q, isOpen_interior.inter_closure ⟨hq, hqcl⟩⟩
  have hzsupport := interior_subset hzS
  rw [TriangleMesh.toPlaneComplex_support] at hzsupport
  obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.mp hzsupport
  have hu' := (M.mem_restrictTriangles_triangles P).mp hu
  let U : M.Triangle := ⟨u, hu'.1⟩
  by_cases htu : t = U
  · exact htu ▸ hu'.2
  · have hinter := mesh_triangle_inter_frontier M t U htu
    have hzt' : z ∈ interior (convexHull ℝ (range (meshTriangleBasis M t))) := by
      simpa only [TriangleMesh.triangleCarrier, range_meshTriangleBasis] using hzt
    have hzu' : z ∈ convexHull ℝ (range (meshTriangleBasis M U)) := by
      rw [range_meshTriangleBasis]
      exact hzu
    exact False.elim ((hinter ⟨interior_subset hzt', hzu'⟩).2 hzt')

private def restrictedTriangleEquiv (M : TriangleMesh) (P : Finset M.Vertex → Prop)
    [DecidablePred P] :
    (M.restrictTriangles P).Triangle ≃ {t : M.Triangle // P t.1} where
  toFun t := ⟨⟨t.1, ((M.mem_restrictTriangles_triangles P).mp t.2).1⟩,
    ((M.mem_restrictTriangles_triangles P).mp t.2).2⟩
  invFun t := ⟨t.1.1, (M.mem_restrictTriangles_triangles P).mpr ⟨t.1.2, t.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem meshVertexAngleContribution_restrictTriangles_of_incident
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (x : S)
    (hinc : ∀ (t : M.Triangle) (k : Fin 3), F (meshTriangleBasis M t k) = x → P t.1) :
    meshVertexAngleContribution g F (M.restrictTriangles P) x =
      meshVertexAngleContribution g F M x := by
  let c (t : M.Triangle) := ∑ k : Fin 3,
    if F (meshTriangleBasis M t k) = x then
      coordinateTriangleAngle g F (meshTriangleBasis M t) k else 0
  have heq : meshVertexAngleContribution g F (M.restrictTriangles P) x =
      ∑ t : {t : M.Triangle // P t.1}, c t.1 := by
    unfold meshVertexAngleContribution
    rw [← (restrictedTriangleEquiv M P).symm.sum_comp]
    apply Finset.sum_congr rfl
    intro t _
    apply coordinateTriangle_vertex_contribution_eq_of_range_eq g F _ _ _ x
    simp only [range_meshTriangleBasis]
    rfl
  rw [heq]
  change _ = ∑ t : M.Triangle, c t
  rw [← Finset.sum_subtype (Finset.univ.filter fun t : M.Triangle => P t.1) (by simp) c]
  apply Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro t ht hnot
  dsimp only [c]
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg]
  intro heqx
  exact hnot (Finset.mem_filter.mpr ⟨ht, hinc t k heqx⟩)



theorem meshVertexAngleContribution_restrictTriangles_interior
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (P : Finset M.Vertex → Prop)
    (hM : M.toPlaneComplex.support ⊆ F.source) {q : Plane}
    (hq : q ∈ interior (M.restrictTriangles P).toPlaneComplex.support) :
    meshVertexAngleContribution g F (M.restrictTriangles P) (F q) =
      meshVertexAngleContribution g F M (F q) := by
  apply meshVertexAngleContribution_restrictTriangles_of_incident
  intro t k heq
  have hk : meshTriangleBasis M t k ∈ convexHull ℝ (range (meshTriangleBasis M t)) :=
    subset_convexHull ℝ _ (mem_range_self k)
  have hkq : meshTriangleBasis M t k = q := F.injOn
    (hM (meshTriangleBasis_subset_support M t hk))
    (hM (restrictTriangles_support_subset M P (interior_subset hq))) heq
  exact restrictTriangles_retains_incident_triangle M P hq t (hkq ▸ hk)



theorem single_refineByLines_restrict_interior_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines lines).Vertex → Prop)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hb : convexHull ℝ (range b) ⊆ F.source)
    (u : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Triangle)
    (x : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Vertex)
    (hx : x ∈ u.1)
    (hxint : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position x ∈
      interior (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support) :
    meshVertexAngleContribution g F
      (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P)
      (F ((((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position x)) =
        2 * Real.pi := by
  let M := (TriangleMesh.single b b.ind).refineByLines lines
  have hM : M.toPlaneComplex.support ⊆ F.source := by
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using hb
  rw [meshVertexAngleContribution_restrictTriangles_interior g F M P hM hxint]
  exact single_refineByLines_interior_vertex_fan g F b lines hF hFi hb
    ⟨u.1, ((M.mem_restrictTriangles_triangles P).mp u.2).1⟩ x hx
    (interior_mono (restrictTriangles_support_subset M P) hxint)




theorem single_refineByLines_restrict_interior_vertex_fan_of_source
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (b : AffineBasis (Fin 3) ℝ Plane) (lines : List (Plane →ᵃ[ℝ] ℝ))
    (P : Finset ((TriangleMesh.single b b.ind).refineByLines lines).Vertex → Prop)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support ⊆
      F.source)
    (u : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Triangle)
    (x : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).Vertex)
    (hx : x ∈ u.1)
    (hxint : (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position x ∈
      interior (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).toPlaneComplex.support) :
    meshVertexAngleContribution g F
      (((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P)
      (F ((((TriangleMesh.single b b.ind).refineByLines lines).restrictTriangles P).position x)) =
        2 * Real.pi := by
  have hq := hsource (interior_subset hxint)
  rw [meshVertexAngleContribution_eq_tangentMetric g F hF hFi _ hq _ hsource]
  exact single_refineByLines_restrict_interior_vertex_fan
    (coordinateTangentMetric g F hF hFi _ hq) (OpenPartialHomeomorph.refl Plane)
    b lines P contMDiffOn_id contMDiffOn_id (by simp) u x hx hxint



theorem meshVertexAngleContribution_restrictTriangles_add_compl
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (x : S) :
    meshVertexAngleContribution g F (M.restrictTriangles P) x +
      meshVertexAngleContribution g F (M.restrictTriangles fun t => ¬P t) x =
        meshVertexAngleContribution g F M x := by
  let c (t : M.Triangle) := ∑ k : Fin 3,
    if F (meshTriangleBasis M t k) = x then
      coordinateTriangleAngle g F (meshTriangleBasis M t) k else 0
  have heq (Q : Finset M.Vertex → Prop) [DecidablePred Q] :
      meshVertexAngleContribution g F (M.restrictTriangles Q) x =
        ∑ t : M.Triangle, if Q t.1 then c t else 0 := by
    have hsub : meshVertexAngleContribution g F (M.restrictTriangles Q) x =
        ∑ t : {t : M.Triangle // Q t.1}, c t.1 := by
      unfold meshVertexAngleContribution
      rw [← (restrictedTriangleEquiv M Q).symm.sum_comp]
      apply Finset.sum_congr rfl
      intro t _
      apply coordinateTriangle_vertex_contribution_eq_of_range_eq g F _ _ _ x
      simp only [range_meshTriangleBasis]
      rfl
    rw [hsub, ← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter fun t : M.Triangle => Q t.1)
      (by simp) c).symm
  simp only [heq]
  rw [← Finset.sum_add_distrib]
  change (∑ t : M.Triangle, _) = ∑ t : M.Triangle, c t
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : P t.1 <;> simp [ht]

end PoincareConjecture.Topology.Surface
