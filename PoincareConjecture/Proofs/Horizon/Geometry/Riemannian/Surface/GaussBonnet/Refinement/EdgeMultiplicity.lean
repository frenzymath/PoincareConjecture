import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.CutMembership

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface

theorem affineTriangle_shared_edge_coord
    (b c : AffineBasis (Fin 3) ℝ Plane) (h0 : b 0 = c 0) (h1 : b 1 = c 1) :
    b.coord 2 = (b.coord 2 (c 2)) • c.coord 2 := by
  apply AffineMap.ext_on c.tot
  rintro z ⟨i, rfl⟩
  have hb0 : b.coord 2 (c 0) = 0 := by rw [← h0]; exact b.coord_apply_ne (by decide)
  have hb1 : b.coord 2 (c 1) = 0 := by rw [← h1]; exact b.coord_apply_ne (by decide)
  fin_cases i <;> simp [hb0, hb1, Fin.ext_iff]

theorem affineTriangle_shared_edge_coord_ne_zero
    (b c : AffineBasis (Fin 3) ℝ Plane) (h0 : b 0 = c 0) (h1 : b 1 = c 1) :
    b.coord 2 (c 2) ≠ 0 := by
  intro hzero
  have h := congrArg (fun l : Plane →ᵃ[ℝ] ℝ => l (b 2))
    (affineTriangle_shared_edge_coord b c h0 h1)
  simp [hzero] at h

theorem affineTriangle_shared_edge_interiors_overlap
    (b c : AffineBasis (Fin 3) ℝ Plane) (h0 : b 0 = c 0) (h1 : b 1 = c 1)
    (hside : 0 < b.coord 2 (c 2)) :
    (interior (convexHull ℝ (range b)) ∩ interior (convexHull ℝ (range c))).Nonempty := by
  let q := AffineMap.lineMap (c 0) (c 1) (1 / 2 : ℝ)
  let path : ℝ → Plane := AffineMap.lineMap q (c 2)
  have hq (i : Fin 3) : c.coord i q = if i = 2 then 0 else 1 / 2 := by
    fin_cases i <;> norm_num [q, AffineMap.apply_lineMap,
      AffineMap.lineMap_apply_ring, AffineBasis.coord_apply, Fin.ext_iff]
  have hbq (i : Fin 3) : b.coord i q = if i = 2 then 0 else 1 / 2 := by
    fin_cases i <;> norm_num [q, AffineMap.apply_lineMap,
      AffineMap.lineMap_apply_ring, ← h0, ← h1, AffineBasis.coord_apply, Fin.ext_iff]
  have hpath : Continuous path := by
    change Continuous (fun t : ℝ => AffineMap.lineMap q (c 2) t)
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hp0 : path 0 = q := AffineMap.lineMap_apply_zero _ _
  have hpos0 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < b.coord 0 (path t) :=
    ((continuous_barycentric_coord b 0).comp hpath).continuousAt.eventually
      (Ioi_mem_nhds (by norm_num [Function.comp_apply, hp0, hbq, Fin.ext_iff]))
  have hpos1 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < b.coord 1 (path t) :=
    ((continuous_barycentric_coord b 1).comp hpath).continuousAt.eventually
      (Ioi_mem_nhds (by norm_num [Function.comp_apply, hp0, hbq, Fin.ext_iff]))
  have hlt : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := Iio_mem_nhds (by norm_num)
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t ∧ t < 1 ∧ 0 < b.coord 0 (path t) ∧ 0 < b.coord 1 (path t) := by
    filter_upwards [hpos0.filter_mono nhdsWithin_le_nhds,
      hpos1.filter_mono nhdsWithin_le_nhds,
      hlt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht0 ht1 htlt htpos
    exact ⟨htpos, htlt, ht0, ht1⟩
  obtain ⟨t, htpos, htlt, ht0, ht1⟩ := hevent.exists
  refine ⟨path t, ?_, ?_⟩
  · rw [b.interior_convexHull]
    intro i
    fin_cases i
    · exact ht0
    · exact ht1
    · simpa [path, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hbq]
        using mul_pos htpos hside
  · rw [c.interior_convexHull]
    intro i
    fin_cases i <;> simp only [path, AffineMap.apply_lineMap,
      AffineMap.lineMap_apply_ring, hq, AffineBasis.coord_apply] <;>
      norm_num [Fin.ext_iff] <;> linarith

theorem affineTriangle_shared_edge_coord_neg
    (b c : AffineBasis (Fin 3) ℝ Plane) (h0 : b 0 = c 0) (h1 : b 1 = c 1)
    (hdisjoint : Disjoint (interior (convexHull ℝ (range b)))
      (interior (convexHull ℝ (range c)))) : b.coord 2 (c 2) < 0 := by
  have hnonpos : b.coord 2 (c 2) ≤ 0 := by
    by_contra h
    obtain ⟨z, hzb, hzc⟩ := affineTriangle_shared_edge_interiors_overlap b c h0 h1 (lt_of_not_ge h)
    exact disjoint_left.mp hdisjoint hzb hzc
  exact lt_of_le_of_ne hnonpos (affineTriangle_shared_edge_coord_ne_zero b c h0 h1)

theorem not_three_affineTriangles_shared_edge
    (a b c : AffineBasis (Fin 3) ℝ Plane)
    (hab0 : a 0 = b 0) (hab1 : a 1 = b 1)
    (hac0 : a 0 = c 0) (hac1 : a 1 = c 1)
    (hab : Disjoint (interior (convexHull ℝ (range a)))
      (interior (convexHull ℝ (range b))))
    (hac : Disjoint (interior (convexHull ℝ (range a)))
      (interior (convexHull ℝ (range c))))
    (hbc : Disjoint (interior (convexHull ℝ (range b)))
      (interior (convexHull ℝ (range c)))) : False := by
  have h1 := affineTriangle_shared_edge_coord_neg a b hab0 hab1 hab
  have h2 := affineTriangle_shared_edge_coord_neg a c hac0 hac1 hac
  have h3 := affineTriangle_shared_edge_coord_neg b c (hab0.symm.trans hac0)
    (hab1.symm.trans hac1) hbc
  have heq := congrArg (fun l : Plane →ᵃ[ℝ] ℝ => l (c 2))
    (affineTriangle_shared_edge_coord a b hab0 hab1)
  change a.coord 2 (c 2) = a.coord 2 (b 2) * b.coord 2 (c 2) at heq
  nlinarith

theorem exists_meshTriangleBasis_with_edge (M : TriangleMesh) (t : M.Triangle)
    {a b : M.Vertex} (ha : a ∈ t.1) (hb : b ∈ t.1) (hab : a ≠ b) :
    ∃ c : AffineBasis (Fin 3) ℝ Plane,
      c 0 = M.position a ∧ c 1 = M.position b ∧
      range c = range (meshTriangleBasis M t) := by
  obtain ⟨i, hi⟩ : M.position a ∈ range (meshTriangleBasis M t) := by
    rw [range_meshTriangleBasis]
    exact ⟨a, ha, rfl⟩
  obtain ⟨j, hj⟩ : M.position b ∈ range (meshTriangleBasis M t) := by
    rw [range_meshTriangleBasis]
    exact ⟨b, hb, rfl⟩
  have hij : i ≠ j := by
    intro heq
    exact hab (M.position_injective (hi.symm.trans (heq ▸ hj)))
  have hperm : ∃ e : Equiv.Perm (Fin 3), e 0 = i ∧ e 1 = j := by
    have h : ∀ i j : Fin 3, i ≠ j → ∃ e : Equiv.Perm (Fin 3), e 0 = i ∧ e 1 = j := by decide
    exact h i j hij
  obtain ⟨e, he0, he1⟩ := hperm
  refine ⟨(meshTriangleBasis M t).reindex e.symm, ?_, ?_, ?_⟩
  · simpa only [AffineBasis.reindex_apply, Equiv.symm_symm, he0] using hi
  · simpa only [AffineBasis.reindex_apply, Equiv.symm_symm, he1] using hj
  · simp only [AffineBasis.coe_reindex, Equiv.symm_symm, Set.range_comp, Equiv.range_eq_univ,
      Set.image_univ]

theorem mesh_common_edge_intersection (M : TriangleMesh) (t u : M.Triangle)
    (htu : t ≠ u) {a b : M.Vertex} (hab : a ≠ b)
    (hat : a ∈ t.1) (hbt : b ∈ t.1) (hau : a ∈ u.1) (hbu : b ∈ u.1) :
    convexHull ℝ (range (meshTriangleBasis M t)) ∩
      convexHull ℝ (range (meshTriangleBasis M u)) =
        segment ℝ (M.position a) (M.position b) := by
  rw [range_meshTriangleBasis, range_meshTriangleBasis, M.triangle_inter t.1 t.2 u.1 u.2]
  have hle : (t.1 ∩ u.1).card ≤ 3 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (M.card_triangle t.1 t.2).le
  have hne : (t.1 ∩ u.1).card ≠ 3 := by
    intro h
    have ht : t.1 ∩ u.1 = t.1 := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by rw [M.card_triangle t.1 t.2, h])
    have hu : t.1 ∩ u.1 = u.1 := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by rw [M.card_triangle u.1 u.2, h])
    exact htu (Subtype.ext (ht.symm.trans hu))
  have hsub : ({a, b} : Finset M.Vertex) ⊆ t.1 ∩ u.1 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hat, hau⟩
    · exact Finset.mem_inter.mpr ⟨hbt, hbu⟩
  have heq : ({a, b} : Finset M.Vertex) = t.1 ∩ u.1 :=
    Finset.eq_of_subset_of_card_le hsub (by simp only [Finset.card_pair hab]; omega)
  rw [← heq]
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton, convexHull_pair]

theorem mesh_common_edge_disjoint_interiors (M : TriangleMesh) (t u : M.Triangle)
    (htu : t ≠ u) {a b : M.Vertex} (hab : a ≠ b)
    (hat : a ∈ t.1) (hbt : b ∈ t.1) (hau : a ∈ u.1) (hbu : b ∈ u.1) :
    Disjoint (interior (convexHull ℝ (range (meshTriangleBasis M t))))
      (interior (convexHull ℝ (range (meshTriangleBasis M u)))) := by
  apply disjoint_left.mpr
  intro z hzt hzu
  have hz : z ∈ convexHull ℝ (range (meshTriangleBasis M t)) ∩
      convexHull ℝ (range (meshTriangleBasis M u)) :=
    ⟨interior_subset hzt, interior_subset hzu⟩
  rw [mesh_common_edge_intersection M t u htu hab hat hbt hau hbu,
    segment_eq_image_lineMap] at hz
  obtain ⟨r, _, rfl⟩ := hz
  obtain ⟨c, hc0, hc1, hcrange⟩ := exists_meshTriangleBasis_with_edge M t hat hbt hab
  rw [← hcrange, c.interior_convexHull] at hzt
  have hpos := hzt 2
  norm_num [← hc0, ← hc1, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
    AffineBasis.coord_apply, Fin.ext_iff] at hpos

theorem mesh_edge_parent_card_le_two (M : TriangleMesh) {a b : M.Vertex} (hab : a ≠ b) :
    (Finset.univ.filter fun t : M.Triangle => a ∈ t.1 ∧ b ∈ t.1).card ≤ 2 := by
  by_contra h
  obtain ⟨t, u, v, ht, hu, hv, htu, htv, huv⟩ :=
    Finset.two_lt_card_iff.mp (lt_of_not_ge h)
  have ht' := (Finset.mem_filter.mp ht).2
  have hu' := (Finset.mem_filter.mp hu).2
  have hv' := (Finset.mem_filter.mp hv).2
  obtain ⟨bt, hbt0, hbt1, hrt⟩ := exists_meshTriangleBasis_with_edge M t ht'.1 ht'.2 hab
  obtain ⟨bu, hbu0, hbu1, hru⟩ := exists_meshTriangleBasis_with_edge M u hu'.1 hu'.2 hab
  obtain ⟨bv, hbv0, hbv1, hrv⟩ := exists_meshTriangleBasis_with_edge M v hv'.1 hv'.2 hab
  apply not_three_affineTriangles_shared_edge bt bu bv
    (hbt0.trans hbu0.symm) (hbt1.trans hbu1.symm)
    (hbt0.trans hbv0.symm) (hbt1.trans hbv1.symm)
  · rw [hrt, hru]
    exact mesh_common_edge_disjoint_interiors M t u htu hab ht'.1 ht'.2 hu'.1 hu'.2
  · rw [hrt, hrv]
    exact mesh_common_edge_disjoint_interiors M t v htv hab ht'.1 ht'.2 hv'.1 hv'.2
  · rw [hru, hrv]
    exact mesh_common_edge_disjoint_interiors M u v huv hab hu'.1 hu'.2 hv'.1 hv'.2

theorem localRefinementBoundaryCuts_parent_card_eq_two (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (hqint : q ∈ interior M.toPlaneComplex.support) :
    (Finset.univ.filter fun u : M.Triangle =>
      q ∈ convexHull ℝ (range (meshTriangleBasis M u))).card = 2 := by
  obtain ⟨a, _, b, _, hab, _, _, hparent⟩ :=
    localRefinementBoundaryCuts_incident_edge M f t hq
  have hle : (Finset.univ.filter fun u : M.Triangle =>
      q ∈ convexHull ℝ (range (meshTriangleBasis M u))).card ≤ 2 := by
    simpa only [hparent] using mesh_edge_parent_card_le_two M hab
  obtain ⟨u, hut, hqu⟩ := localRefinementBoundaryCuts_exists_other_parent M f t hq hqint
  have hqt : q ∈ convexHull ℝ (range (meshTriangleBasis M t)) :=
    ((finite_range _).isClosed_convexHull ℝ).frontier_subset
      (localRefinementBoundaryCuts_geometry M f t hq).1
  have hgt : 1 < (Finset.univ.filter fun u : M.Triangle =>
      q ∈ convexHull ℝ (range (meshTriangleBasis M u))).card :=
    Finset.one_lt_card.mpr ⟨t, by simp [hqt], u, by simp [hqu], hut.symm⟩
  omega

theorem localRefinementBoundaryCuts_card_eq_two (M : TriangleMesh)
    (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (hqint : q ∈ interior M.toPlaneComplex.support) :
    (Finset.univ.filter fun u : M.Triangle => q ∈ localRefinementBoundaryCuts M f u).card = 2 := by
  simp only [localRefinementBoundaryCuts_mem_iff_mem_hull M f t hq]
  exact localRefinementBoundaryCuts_parent_card_eq_two M f t hq hqint

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem lineRefinementMesh_new_vertex_fan
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (M : TriangleMesh) (f : Plane →ᵃ[ℝ] ℝ) (t : M.Triangle) {q : Plane}
    (hq : q ∈ localRefinementBoundaryCuts M f t)
    (hqint : q ∈ interior M.toPlaneComplex.support)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hM : M.toPlaneComplex.support ⊆ F.source) :
    meshVertexAngleContribution g F (M.lineRefinementMesh f) (F q) = 2 * Real.pi := by
  rw [lineRefinementMesh_vertex_contribution_new_cut g F M f t hq hF hFi hM,
    localRefinementBoundaryCuts_card_eq_two M f t hq hqint]
  norm_num

end PoincareConjecture.Topology.Surface
