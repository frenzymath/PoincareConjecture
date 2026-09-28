import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.Global









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface



theorem mesh_usedVertex_mem_triangle_of_mem_hull (M : TriangleMesh)
    (t u : M.Triangle) {v : M.Vertex} (hv : v ∈ u.1)
    (hvt : M.position v ∈ convexHull ℝ (range (meshTriangleBasis M t))) :
    v ∈ t.1 := by
  by_contra hnot
  have hvface : ({v} : Finset M.Vertex) ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨Finset.singleton_nonempty _, u.1, u.2,
      Finset.singleton_subset_iff.mpr hv⟩
  have htface : t.1 ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by rw [M.card_triangle t.1 t.2]; norm_num),
      t.1, t.2, subset_rfl⟩
  have h := M.toPlaneComplex.face_inter {v} hvface t.1 htface
  change convexHull ℝ (M.position '' (({v} : Finset M.Vertex) : Set M.Vertex)) ∩
    convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) =
      convexHull ℝ (M.position '' (({v} ∩ t.1 : Finset M.Vertex) : Set M.Vertex)) at h
  have hmem : M.position v ∈
      convexHull ℝ (M.position '' (({v} : Finset M.Vertex) : Set M.Vertex)) ∩
      convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) := by
    refine ⟨by simp, ?_⟩
    simpa only [range_meshTriangleBasis] using hvt
  rw [h] at hmem
  have hempty : ({v} ∩ t.1 : Finset M.Vertex) = ∅ := by
    simp [hnot]
  simp [hempty] at hmem



theorem localRefinementBoundaryCuts_ne_usedVertex (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (u : M.Triangle) (v : M.Vertex) (hv : v ∈ u.1) : q ≠ M.position v := by
  intro heq
  have hgeom := localRefinementBoundaryCuts_geometry M f t hq
  have hclosed : IsClosed (convexHull ℝ (range (meshTriangleBasis M t))) :=
    (Set.finite_range _).isClosed_convexHull ℝ
  have hmem := hclosed.frontier_subset hgeom.1
  rw [heq] at hmem
  have hvt := mesh_usedVertex_mem_triangle_of_mem_hull M t u hv hmem
  apply hgeom.2.1
  rw [range_meshTriangleBasis, heq]
  exact ⟨v, hvt, rfl⟩



theorem affineCutPoint_mem_openSegment_of_mul_neg (f : Plane →ᵃ[ℝ] ℝ)
    (a b : Plane) (hcross : f a * f b < 0) :
    affineCutPoint f a b ∈ openSegment ℝ a b := by
  rcases mul_neg_iff.mp hcross with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [openSegment_eq_image_lineMap]
    exact ⟨f a / (f a - f b),
      ⟨affineCutPoint.parameter_pos f a b ha hb,
        affineCutPoint.parameter_lt_one f a b ha hb⟩, rfl⟩
  · rw [← affineCutPoint.neg]
    rw [openSegment_eq_image_lineMap]
    exact ⟨(-f) a / ((-f) a - (-f) b),
      ⟨affineCutPoint.parameter_pos (-f) a b (neg_pos.mpr ha) (neg_neg_of_pos hb),
        affineCutPoint.parameter_lt_one (-f) a b (neg_pos.mpr ha) (neg_neg_of_pos hb)⟩,
      rfl⟩


theorem localRefinementBoundaryCuts_crossed_edge (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t) :
    ∃ a ∈ t.1, ∃ b ∈ t.1,
      f (M.position a) * f (M.position b) < 0 ∧
      q = affineCutPoint f (M.position a) (M.position b) := by
  unfold localRefinementBoundaryCuts at hq
  split_ifs at hq with hp hn hep hen
  · let o := Classical.choice hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, M.orderedVertex_mem t _, _, M.orderedVertex_mem t _,
        mul_neg_of_pos_of_neg o.positive o.negative_one, rfl⟩
    · exact ⟨_, M.orderedVertex_mem t _, _, M.orderedVertex_mem t _,
        mul_neg_of_pos_of_neg o.positive o.negative_two, rfl⟩
  · let o := Classical.choice hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, M.orderedVertex_mem t _, _, M.orderedVertex_mem t _,
        mul_neg_of_neg_of_pos o.negative o.positive_one, rfl⟩
    · exact ⟨_, M.orderedVertex_mem t _, _, M.orderedVertex_mem t _,
        mul_neg_of_neg_of_pos o.negative o.positive_two, rfl⟩
  · let o := Classical.choice hep
    simp only [List.mem_singleton] at hq
    subst q
    exact ⟨_, M.orderedVertex_mem t _, _, M.orderedVertex_mem t _,
      mul_neg_of_pos_of_neg o.positive o.negative, rfl⟩
  · let o := Classical.choice hen
    simp only [List.mem_singleton] at hq
    subst q
    exact ⟨_, M.orderedVertex_mem t _, _, M.orderedVertex_mem t _,
      mul_neg_of_neg_of_pos o.negative o.positive, rfl⟩
  · exact False.elim (List.not_mem_nil hq)



theorem mesh_edge_endpoints_mem_of_openSegment_mem_hull (M : TriangleMesh)
    (t u : M.Triangle) {a b : M.Vertex} (ha : a ∈ t.1) (hb : b ∈ t.1)
    (hab : a ≠ b) {q : Plane} (hq : q ∈ openSegment ℝ (M.position a) (M.position b))
    (hu : q ∈ convexHull ℝ (range (meshTriangleBasis M u))) :
    a ∈ u.1 ∧ b ∈ u.1 := by
  have hedge : ({a, b} : Finset M.Vertex) ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨by simp, t.1, t.2, by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ha
      · exact hb⟩
  have huface : u.1 ∈ M.toPlaneComplex.simplexes :=
    M.mem_faces_iff.mpr ⟨Finset.card_pos.mp (by rw [M.card_triangle u.1 u.2]; norm_num),
      u.1, u.2, subset_rfl⟩
  have hinter := M.toPlaneComplex.face_inter {a, b} hedge u.1 huface
  change convexHull ℝ (M.position '' (({a, b} : Finset M.Vertex) : Set M.Vertex)) ∩
    convexHull ℝ (M.position '' (u.1 : Set M.Vertex)) =
      convexHull ℝ (M.position '' (({a, b} ∩ u.1 : Finset M.Vertex) : Set M.Vertex)) at hinter
  have hqinter : q ∈ convexHull ℝ (M.position '' (({a, b} ∩ u.1 : Finset M.Vertex) : Set _)) := by
    rw [← hinter]
    refine ⟨?_, ?_⟩
    · simpa only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
        Set.image_singleton, convexHull_pair] using openSegment_subset_segment ℝ _ _ hq
    · simpa only [range_meshTriangleBasis] using hu
  have hleft (hnot : a ∉ u.1) : q = M.position b := by
    have hsub : ({a, b} ∩ u.1 : Finset M.Vertex) ⊆ {b} := by
      intro v hv
      rcases Finset.mem_inter.mp hv with ⟨hv, hvu⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      rcases hv with rfl | rfl
      · exact False.elim (hnot hvu)
      · rfl
    have h := convexHull_mono (Set.image_mono hsub) hqinter
    simpa using h
  have hright (hnot : b ∉ u.1) : q = M.position a := by
    have hsub : ({a, b} ∩ u.1 : Finset M.Vertex) ⊆ {a} := by
      intro v hv
      rcases Finset.mem_inter.mp hv with ⟨hv, hvu⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      rcases hv with rfl | rfl
      · rfl
      · exact False.elim (hnot hvu)
    have h := convexHull_mono (Set.image_mono hsub) hqinter
    simpa using h
  constructor
  · by_contra hnot
    rw [hleft hnot, right_mem_openSegment_iff] at hq
    exact hab (M.position_injective hq)
  · by_contra hnot
    rw [hright hnot, left_mem_openSegment_iff] at hq
    exact hab (M.position_injective hq)



theorem localRefinementBoundaryCuts_incident_edge (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t) :
    ∃ a ∈ t.1, ∃ b ∈ t.1, a ≠ b ∧
      f (M.position a) * f (M.position b) < 0 ∧
      q ∈ openSegment ℝ (M.position a) (M.position b) ∧
      ∀ u : M.Triangle,
        q ∈ convexHull ℝ (range (meshTriangleBasis M u)) ↔ a ∈ u.1 ∧ b ∈ u.1 := by
  obtain ⟨a, ha, b, hb, hcross, rfl⟩ := localRefinementBoundaryCuts_crossed_edge M f t hq
  have hab : a ≠ b := by
    intro heq
    subst b
    exact (not_lt_of_ge (mul_self_nonneg _)) hcross
  have hsegment := affineCutPoint_mem_openSegment_of_mul_neg f _ _ hcross
  refine ⟨a, ha, b, hb, hab, hcross, hsegment, fun u => ⟨?_, ?_⟩⟩
  · exact mesh_edge_endpoints_mem_of_openSegment_mem_hull M t u ha hb hab hsegment
  · rintro ⟨hau, hbu⟩
    rw [range_meshTriangleBasis]
    apply convexHull_mono (show {M.position a, M.position b} ⊆
      M.position '' (u.1 : Set M.Vertex) from by
        simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨⟨a, hau, rfl⟩, ⟨b, hbu, rfl⟩⟩)
    rw [convexHull_pair]
    exact openSegment_subset_segment ℝ _ _ hsegment




theorem localRefinementBoundaryCuts_exists_other_parent (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (hqint : q ∈ interior M.toPlaneComplex.support) :
    ∃ u : M.Triangle, u ≠ t ∧ q ∈ convexHull ℝ (range (meshTriangleBasis M u)) := by
  by_contra hnone
  push Not at hnone
  let A : Set Plane := ⋃ u : M.Triangle, ⋃ (_ : u ≠ t),
    convexHull ℝ (range (meshTriangleBasis M u))
  have hclosed : IsClosed A := isClosed_iUnion_of_finite fun u =>
    isClosed_iUnion_of_finite fun (_ : u ≠ t) => (finite_range _).isClosed_convexHull ℝ
  have hqA : q ∉ A := by
    simp only [A, mem_iUnion]
    rintro ⟨u, hut, hqu⟩
    exact hnone u hut hqu
  have hnhds : M.toPlaneComplex.support ∩ Aᶜ ∈ 𝓝 q :=
    Filter.inter_mem (mem_interior_iff_mem_nhds.mp hqint) (hclosed.isOpen_compl.mem_nhds hqA)
  have hsub : M.toPlaneComplex.support ∩ Aᶜ ⊆
      convexHull ℝ (range (meshTriangleBasis M t)) := by
    rintro z ⟨hz, hzA⟩
    rw [← meshTriangleBasis_sources_cover] at hz
    obtain ⟨u, hzu⟩ := mem_iUnion.mp hz
    by_cases hut : u = t
    · exact hut ▸ hzu
    · exact False.elim (hzA (mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨hut, hzu⟩⟩))
  have hint : q ∈ interior (convexHull ℝ (range (meshTriangleBasis M t))) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hnhds hsub)
  exact (localRefinementBoundaryCuts_geometry M f t hq).1.2 hint

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]


theorem meshVertexAngleContribution_eq_zero_at_new_cut
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (hM : M.toPlaneComplex.support ⊆ F.source) :
    meshVertexAngleContribution g F M (F q) = 0 := by
  have hqsource : q ∈ F.source := hM (meshTriangleBasis_subset_support M t
    (((finite_range _).isClosed_convexHull ℝ).frontier_subset
      (localRefinementBoundaryCuts_geometry M f t hq).1))
  unfold meshVertexAngleContribution
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg]
  intro heq
  have hsource : meshTriangleBasis M u k ∈ F.source := hM
    (meshTriangleBasis_subset_support M u (subset_convexHull ℝ _ (mem_range_self k)))
  have hpoint := F.injOn hsource hqsource heq
  exact localRefinementBoundaryCuts_ne_usedVertex M f t hq u (M.orderedVertex u k)
    (M.orderedVertex_mem u k) hpoint.symm



theorem lineRefinementMesh_vertex_contribution_new_cut
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source) :
    meshVertexAngleContribution g F (M.lineRefinementMesh f) (F q) =
      ((Finset.univ.filter fun u : M.Triangle =>
        q ∈ localRefinementBoundaryCuts M f u).card : ℝ) * Real.pi := by
  have hsource (u : M.Triangle) {r : Plane}
      (hr : r ∈ localRefinementBoundaryCuts M f u) : r ∈ F.source :=
    hM (meshTriangleBasis_subset_support M u
      (((finite_range _).isClosed_convexHull ℝ).frontier_subset
        (localRefinementBoundaryCuts_geometry M f u hr).1))
  rw [lineRefinementMesh_vertex_contribution g F M f hF hFi hM,
    meshVertexAngleContribution_eq_zero_at_new_cut g F M f t hq hM, zero_add]
  have hinner (u : M.Triangle) :
      (∑ r ∈ (localRefinementBoundaryCuts M f u).toFinset,
        if F r = F q then Real.pi else 0) =
      if q ∈ localRefinementBoundaryCuts M f u then Real.pi else 0 := by
    calc
      _ = ∑ r ∈ (localRefinementBoundaryCuts M f u).toFinset,
          if r = q then Real.pi else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        have heq : F r = F q ↔ r = q :=
          ⟨F.injOn (hsource u (List.mem_toFinset.mp hr)) (hsource t hq), congrArg F⟩
        simp only [heq]
      _ = _ := by simp
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  simp [nsmul_eq_mul]

end PoincareConjecture.Topology.Surface
