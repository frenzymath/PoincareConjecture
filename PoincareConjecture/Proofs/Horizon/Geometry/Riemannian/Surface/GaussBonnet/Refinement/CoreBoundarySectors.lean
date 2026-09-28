import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.RestrictedFans









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface



theorem restrictTriangles_retains_incident_triangle_of_local_subset
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) {q : Plane}
    (t : M.Triangle) (hqt : q ∈ M.triangleCarrier t.1)
    (hlocal : ∀ᶠ z in 𝓝 q, z ∈ M.triangleCarrier t.1 →
      z ∈ (M.restrictTriangles P).toPlaneComplex.support) : P t.1 := by
  obtain ⟨V, hV, hVo, hqV⟩ := mem_nhds_iff.mp hlocal
  have hqcl : q ∈ closure (interior (M.triangleCarrier t.1)) := by
    rw [M.closure_interior_triangleCarrier t]
    exact hqt
  obtain ⟨z, hzV, hzt⟩ := Set.Nonempty.of_closure
    ⟨q, hVo.inter_closure ⟨hqV, hqcl⟩⟩
  have hsub : V ∩ interior (M.triangleCarrier t.1) ⊆
      (M.restrictTriangles P).toPlaneComplex.support :=
    fun _ hz => hV hz.1 (interior_subset hz.2)
  apply restrictTriangles_retains_incident_triangle M P
    ((hVo.inter isOpen_interior).subset_interior_iff.mpr hsub ⟨hzV, hzt⟩) t
  simpa only [TriangleMesh.triangleCarrier, range_meshTriangleBasis] using interior_subset hzt



theorem restrictTriangles_incident_iff_of_support_eventuallyEq
    (M : TriangleMesh) (P Q : Finset M.Vertex → Prop) {q : Plane}
    (hlocal : (M.restrictTriangles P).toPlaneComplex.support =ᶠ[𝓝 q]
      (M.restrictTriangles Q).toPlaneComplex.support)
    (t : M.Triangle) (hqt : q ∈ M.triangleCarrier t.1) : P t.1 ↔ Q t.1 := by
  have hforward (P Q : Finset M.Vertex → Prop)
      (hlocal : (M.restrictTriangles P).toPlaneComplex.support =ᶠ[𝓝 q]
        (M.restrictTriangles Q).toPlaneComplex.support) (ht : P t.1) : Q t.1 := by
    apply restrictTriangles_retains_incident_triangle_of_local_subset M Q t hqt
    filter_upwards [hlocal] with z hz hzt
    apply hz.mp
    rw [TriangleMesh.toPlaneComplex_support]
    exact mem_iUnion₂.mpr ⟨t.1, (M.mem_restrictTriangles_triangles P).mpr ⟨t.2, ht⟩, hzt⟩
  exact ⟨hforward P Q hlocal, hforward Q P hlocal.symm⟩



theorem affineTriangle_eventually_mem_iff_active_halfspaces
    (b : AffineBasis (Fin 3) ℝ Plane) {q : Plane}
    (hq : q ∈ convexHull ℝ (range b)) :
    ∀ᶠ z in 𝓝 q, z ∈ convexHull ℝ (range b) ↔
      ∀ i : Fin 3, b.coord i q = 0 → 0 ≤ b.coord i z := by
  have hnonneg : ∀ i : Fin 3, 0 ≤ b.coord i q := by
    simpa only [b.convexHull_eq_nonneg_coord, mem_ofPred_eq] using hq
  have hpos : ∀ᶠ z in 𝓝 q, ∀ i : Fin 3, b.coord i q ≠ 0 → 0 < b.coord i z := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : b.coord i q = 0
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hi))
    · have h := (continuous_barycentric_coord b i).continuousAt.eventually
        (Ioi_mem_nhds (lt_of_le_of_ne (hnonneg i) (Ne.symm hi)))
      exact h.mono (fun _ hz _ => hz)
  filter_upwards [hpos] with z hz
  rw [b.convexHull_eq_nonneg_coord]
  change (∀ i, 0 ≤ b.coord i z) ↔ _
  constructor
  · exact fun h i _ => h i
  · intro h i
    by_cases hi : b.coord i q = 0
    · exact h i hi
    · exact (hz i hi).le



theorem affineTriangle_eventually_mem_iff_corner_halfspaces
    (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) :
    ∀ᶠ z in 𝓝 (b i), z ∈ convexHull ℝ (range b) ↔
      ∀ j : Fin 3, j ≠ i → 0 ≤ b.coord j z := by
  have h := affineTriangle_eventually_mem_iff_active_halfspaces b
    (subset_convexHull ℝ _ (mem_range_self i))
  filter_upwards [h] with z hz
  rw [hz]
  simp only [AffineBasis.coord_apply]
  simp




theorem restrictTriangles_support_eventually_eq_active_halfspaces
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) (q : Plane) :
    ∀ᶠ z in 𝓝 q, z ∈ (M.restrictTriangles P).toPlaneComplex.support ↔
      ∃ t : M.Triangle, P t.1 ∧ q ∈ M.triangleCarrier t.1 ∧
        ∀ i : Fin 3, (meshTriangleBasis M t).coord i q = 0 →
          0 ≤ (meshTriangleBasis M t).coord i z := by
  have hevent : ∀ᶠ z in 𝓝 q, ∀ t : M.Triangle,
      z ∈ M.triangleCarrier t.1 ↔ q ∈ M.triangleCarrier t.1 ∧
        ∀ i : Fin 3, (meshTriangleBasis M t).coord i q = 0 →
          0 ≤ (meshTriangleBasis M t).coord i z := by
    apply Filter.eventually_all.mpr
    intro t
    by_cases hqt : q ∈ M.triangleCarrier t.1
    · have hq : q ∈ convexHull ℝ (range (meshTriangleBasis M t)) := by
        simpa only [TriangleMesh.triangleCarrier, range_meshTriangleBasis] using hqt
      filter_upwards [affineTriangle_eventually_mem_iff_active_halfspaces
        (meshTriangleBasis M t) hq] with z hz
      simp only [hqt, true_and]
      simpa only [TriangleMesh.triangleCarrier, range_meshTriangleBasis] using hz
    · have hc : IsClosed (M.triangleCarrier t.1) :=
        (t.1.finite_toSet.image M.position).isClosed_convexHull ℝ
      filter_upwards [hc.isOpen_compl.mem_nhds hqt] with z hz
      simp only [hqt, false_and]
      exact iff_false_intro hz
  filter_upwards [hevent] with z hz
  rw [TriangleMesh.toPlaneComplex_support]
  constructor
  · intro h
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp h
    obtain ⟨htM, htP⟩ := (M.mem_restrictTriangles_triangles P).mp ht
    exact ⟨⟨t, htM⟩, htP, (hz ⟨t, htM⟩).mp hzt⟩
  · rintro ⟨t, htP, hqt, hsector⟩
    exact mem_iUnion₂.mpr ⟨t.1,
      (M.mem_restrictTriangles_triangles P).mpr ⟨t.2, htP⟩, (hz t).mpr ⟨hqt, hsector⟩⟩



def restrictTrianglesTriangleEquiv (M : TriangleMesh) (P : Finset M.Vertex → Prop)
    [DecidablePred P] :
    (M.restrictTriangles P).Triangle ≃ {t : M.Triangle // P t.1} where
  toFun t := ⟨⟨t.1, ((M.mem_restrictTriangles_triangles P).mp t.2).1⟩,
    ((M.mem_restrictTriangles_triangles P).mp t.2).2⟩
  invFun t := ⟨t.1.1, (M.mem_restrictTriangles_triangles P).mpr ⟨t.1.2, t.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem meshVertexAngleContribution_restrictTriangles_eq_sum
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (P : Finset M.Vertex → Prop) [DecidablePred P] (x : S) :
    meshVertexAngleContribution g F (M.restrictTriangles P) x =
      ∑ t : M.Triangle, if P t.1 then
        ∑ k : Fin 3, if F (meshTriangleBasis M t k) = x then
          coordinateTriangleAngle g F (meshTriangleBasis M t) k else 0 else 0 := by
  let c (t : M.Triangle) := ∑ k : Fin 3,
    if F (meshTriangleBasis M t k) = x then
      coordinateTriangleAngle g F (meshTriangleBasis M t) k else 0
  have heq : meshVertexAngleContribution g F (M.restrictTriangles P) x =
      ∑ t : {t : M.Triangle // P t.1}, c t.1 := by
    unfold meshVertexAngleContribution
    rw [← (restrictTrianglesTriangleEquiv M P).symm.sum_comp]
    apply Finset.sum_congr rfl
    intro t _
    apply coordinateTriangle_vertex_contribution_eq_of_range_eq g F _ _ _ x
    simp only [range_meshTriangleBasis]
    rfl
  rw [heq, ← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter fun t : M.Triangle => P t.1)
    (by simp) c).symm



theorem meshVertexAngleContribution_restrictTriangles_eq_of_support_eventuallyEq
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (P Q : Finset M.Vertex → Prop)
    (hM : M.toPlaneComplex.support ⊆ F.source) {q : Plane} (hq : q ∈ F.source)
    (hlocal : (M.restrictTriangles P).toPlaneComplex.support =ᶠ[𝓝 q]
      (M.restrictTriangles Q).toPlaneComplex.support) :
    meshVertexAngleContribution g F (M.restrictTriangles P) (F q) =
      meshVertexAngleContribution g F (M.restrictTriangles Q) (F q) := by
  rw [meshVertexAngleContribution_restrictTriangles_eq_sum,
    meshVertexAngleContribution_restrictTriangles_eq_sum]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hqt : q ∈ M.triangleCarrier t.1
  · rw [restrictTriangles_incident_iff_of_support_eventuallyEq M P Q hlocal t hqt]
  · have hzero : (∑ k : Fin 3, if F (meshTriangleBasis M t k) = F q then
        coordinateTriangleAngle g F (meshTriangleBasis M t) k else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg]
      intro heq
      have hk : meshTriangleBasis M t k ∈ convexHull ℝ (range (meshTriangleBasis M t)) :=
        subset_convexHull ℝ _ (mem_range_self k)
      have hkp := F.injOn (hM (meshTriangleBasis_subset_support M t hk)) hq heq
      apply hqt
      simpa only [TriangleMesh.triangleCarrier, ← range_meshTriangleBasis, hkp] using hk
    simp only [hzero, ite_self]

end PoincareConjecture.Topology.Surface
