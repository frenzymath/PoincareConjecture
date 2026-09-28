import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.BoundaryFans
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.InitialFans
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.EdgeGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Set Classical
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

private theorem segment_eq_lineMap (a b : Plane) (t : ℝ) :
    affineChartSegment a b t = AffineMap.lineMap a b t := by
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

private theorem segment_mem_hull (k : Fin 3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    affineChartSegment (rightTriangleBasis B.scale_pos (k.succAbove 0))
      (rightTriangleBasis B.scale_pos (k.succAbove 1)) t ∈
        convexHull ℝ (range (rightTriangleBasis B.scale_pos)) := by
  apply (convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ (mem_range_self (k.succAbove 0)))
    (subset_convexHull ℝ _ (mem_range_self (k.succAbove 1)))
  rw [segment_eq_image_lineMap]
  exact ⟨t, ht, by simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]⟩

theorem open_boundary_mem_boundary_iff (i : Bool × Bool) (k l : Fin 3)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ((B.face i).boundary k).map t ∈ ((B.face i).boundary l).map '' Icc (0 : ℝ) 1 ↔
      k = l := by
  constructor
  · rintro ⟨s, hs, heq⟩
    rw [B.boundary_map, B.boundary_map] at heq
    have he := (B.coordinates i).injOn
      (B.triangle_subset_source i (B.segment_mem_hull l hs))
      (B.triangle_subset_source i (B.segment_mem_hull k ⟨ht.1.le, ht.2.le⟩)) heq
    have hc := congrArg ((rightTriangleBasis B.scale_pos).coord l) he
    simp only [segment_eq_lineMap] at hc
    rw [AffineMap.apply_lineMap, AffineMap.apply_lineMap] at hc
    simp only [AffineMap.lineMap_apply_ring, AffineBasis.coord_apply] at hc
    fin_cases k <;> fin_cases l <;>
      norm_num [Fin.succAbove, Fin.lt_def, Fin.ext_iff] at hc ⊢ <;> linarith [ht.1, ht.2]
  · rintro rfl
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩

theorem open_chord_mem_carrier_iff (i j : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ((B.face i).boundary 0).map t ∈ (B.face j).carrier ↔ j = i := by
  have hi : ((B.face i).boundary 0).map t ∈ (B.face i).carrier := by
    rw [B.carrier_eq, B.boundary_map]
    exact ⟨_, B.segment_mem_hull 0 ⟨ht.1.le, ht.2.le⟩, rfl⟩
  constructor
  · intro hj
    by_contra hji
    have haxes : ((B.face i).boundary 0).map t ∈
        P.firstSide i B.scale ∪ P.secondSide i B.scale := by
      rcases B.carrier_subset_sector_sides i hi with h | h
      · exact (disjoint_left.mp (P.sector_disjoint_closedSector (Ne.symm hji)) h
          (B.carrier_subset_sector j hj)).elim
      · exact h
    rcases haxes with h | h
    · rw [← B.first_image] at h
      exact (by decide : (0 : Fin 3) ≠ 2)
        ((B.open_boundary_mem_boundary_iff i 0 2 ht).mp h)
    · rw [← B.second_image] at h
      exact (by decide : (0 : Fin 3) ≠ 1)
        ((B.open_boundary_mem_boundary_iff i 0 1 ht).mp h)
  · rintro rfl
    exact hi

private theorem refined_vertex_mem_hull
    (lines : List (Plane →ᵃ[ℝ] ℝ))
    (u : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
      (rightTriangleBasis B.scale_pos).ind).refineByLines lines).Triangle)
    (v : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
      (rightTriangleBasis B.scale_pos).ind).refineByLines lines).Vertex) (hv : v ∈ u.1) :
    ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
      (rightTriangleBasis B.scale_pos).ind).refineByLines lines).position v ∈
        convexHull ℝ (range (rightTriangleBasis B.scale_pos)) := by
  let M := (TriangleMesh.single (rightTriangleBasis B.scale_pos)
    (rightTriangleBasis B.scale_pos).ind).refineByLines lines
  have hr : M.position v ∈ range (meshTriangleBasis M u) := by
    rw [range_meshTriangleBasis]
    exact ⟨v, hv, rfl⟩
  have h := meshTriangleBasis_subset_support M u (subset_convexHull ℝ _ hr)
  simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using h

theorem open_boundary_refined_vertex_fan (g : RiemannianMetric 2 S)
    (i : Bool × Bool) (k : Fin 3) (lines : List (Plane →ᵃ[ℝ] ℝ))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hused : ∃
      (u : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines lines).Triangle)
      (v : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines lines).Vertex),
      v ∈ u.1 ∧ B.coordinates i
        (((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines lines).position v) =
            ((B.face i).boundary k).map t) :
    meshVertexAngleContribution g (B.coordinates i)
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines lines)
      (((B.face i).boundary k).map t) = Real.pi := by
  obtain ⟨u, v, hv, heq⟩ := hused
  have hpos := (B.coordinates i).injOn
    (B.triangle_subset_source i (B.refined_vertex_mem_hull lines u v hv))
    (B.triangle_subset_source i (B.segment_mem_hull k ⟨ht.1.le, ht.2.le⟩))
    (by simpa only [B.boundary_map, Function.comp_apply] using heq)
  have hfan := single_refineByLines_open_edge_vertex_fan g (B.coordinates i)
    (rightTriangleBasis B.scale_pos) lines k (B.coordinates_smooth i)
    (B.coordinates_smooth_symm i) (B.triangle_subset_source i) u v hv (by
      rw [hpos, openSegment_eq_image_lineMap]
      exact ⟨t, ht, by simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]⟩)
  rwa [heq] at hfan

theorem open_first_side_mem_carrier_iff (i : Bool) (j : Bool × Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ((B.face (i, true)).boundary 2).map t ∈ (B.face j).carrier ↔ j.1 = i := by
  have hside : ((B.face (i, true)).boundary 2).map t ∈ P.firstSide (i, true) B.scale := by
    rw [← B.first_image]
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  have hzero : ((B.face (i, true)).boundary 2).map 0 = p := by
    rw [B.first_map _ 0 (by simp)]
    simpa only [zero_mul, Prod.zero_eq_mk] using P.sectorCoordinates_zero (i, true)
  have hne : ((B.face (i, true)).boundary 2).map t ≠ p := by
    intro he
    have he0 := B.boundary_injective (i, true) 2 ⟨ht.1.le, ht.2.le⟩
      (by simp : (0 : ℝ) ∈ Icc 0 1) (he.trans hzero.symm)
    linarith [ht.1]
  constructor
  · intro hj
    by_contra hji
    exact hne (P.firstSide_inter_opposite_sector (Ne.symm hji) B.scale_lt_width.le
      ⟨hside, B.carrier_subset_sector j hj⟩)
  · intro hji
    apply B.firstSide_subset_carrier j
    rwa [P.firstSide_eq_of_fst_eq (show (i, true).1 = j.1 from hji.symm) B.scale] at hside

theorem open_second_side_mem_carrier_iff (i : Bool) (j : Bool × Bool)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ((B.face (true, i)).boundary 1).map t ∈ (B.face j).carrier ↔ j.2 = i := by
  have hside : ((B.face (true, i)).boundary 1).map t ∈ P.secondSide (true, i) B.scale := by
    rw [← B.second_image]
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  have hzero : ((B.face (true, i)).boundary 1).map 0 = p := by
    rw [B.second_map _ 0 (by simp)]
    simpa only [zero_mul, Prod.zero_eq_mk] using P.sectorCoordinates_zero (true, i)
  have hne : ((B.face (true, i)).boundary 1).map t ≠ p := by
    intro he
    have he0 := B.boundary_injective (true, i) 1 ⟨ht.1.le, ht.2.le⟩
      (by simp : (0 : ℝ) ∈ Icc 0 1) (he.trans hzero.symm)
    linarith [ht.1]
  constructor
  · intro hj
    by_contra hji
    exact hne (P.secondSide_inter_opposite_sector (Ne.symm hji) B.scale_lt_width.le
      ⟨hside, B.carrier_subset_sector j hj⟩)
  · intro hji
    apply B.secondSide_subset_carrier j
    rwa [P.secondSide_eq_of_snd_eq (show (true, i).2 = j.2 from hji.symm) B.scale] at hside

theorem open_chord_refined_vertex_fan (g : RiemannianMetric 2 S) (i : Bool × Bool)
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hused : ∃
      (u : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines i)).Triangle)
      (v : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines i)).Vertex),
      v ∈ u.1 ∧ B.coordinates i
        (((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines i)).position v) =
            ((B.face i).boundary 0).map t) :
    (∑ j : Bool × Bool, meshVertexAngleContribution g (B.coordinates j)
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines j))
      (((B.face i).boundary 0).map t)) = Real.pi := by
  rw [Finset.sum_eq_single i]
  · exact B.open_boundary_refined_vertex_fan g i 0 (lines i) ht hused
  · intro j _ hji
    exact B.refined_contribution_eq_zero_of_not_mem_carrier g j (lines j)
      ((B.open_chord_mem_carrier_iff i j ht).not.mpr hji)
  · simp

theorem open_first_side_refined_vertex_fan (g : RiemannianMetric 2 S) (i : Bool)
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hused : ∀ j : Bool, ∃
      (u : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (i, j))).Triangle)
      (v : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (i, j))).Vertex),
      v ∈ u.1 ∧ B.coordinates (i, j)
        (((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (i, j))).position v) =
            ((B.face (i, true)).boundary 2).map t) :
    (∑ j : Bool × Bool, meshVertexAngleContribution g (B.coordinates j)
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines j))
      (((B.face (i, true)).boundary 2).map t)) = 2 * Real.pi := by
  have hfan (j : Bool) : meshVertexAngleContribution g (B.coordinates (i, j))
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (i, j)))
      (((B.face (i, true)).boundary 2).map t) = Real.pi := by
    have he := B.first_boundary_agreement (i := (i, true)) (j := (i, j)) rfl
      ⟨ht.1.le, ht.2.le⟩
    rw [he]
    apply B.open_boundary_refined_vertex_fan g (i, j) 2 (lines (i, j)) ht
    simpa only [he] using hused j
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp only [hfan, Fintype.sum_bool]
    ring
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro k _
    exact B.refined_contribution_eq_zero_of_not_mem_carrier g (j, k) (lines (j, k))
      ((B.open_first_side_mem_carrier_iff i (j, k) ht).not.mpr hji)
  · simp

theorem open_second_side_refined_vertex_fan (g : RiemannianMetric 2 S) (i : Bool)
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hused : ∀ j : Bool, ∃
      (u : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (j, i))).Triangle)
      (v : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (j, i))).Vertex),
      v ∈ u.1 ∧ B.coordinates (j, i)
        (((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (j, i))).position v) =
            ((B.face (true, i)).boundary 1).map t) :
    (∑ j : Bool × Bool, meshVertexAngleContribution g (B.coordinates j)
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines j))
      (((B.face (true, i)).boundary 1).map t)) = 2 * Real.pi := by
  have hfan (j : Bool) : meshVertexAngleContribution g (B.coordinates (j, i))
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (j, i)))
      (((B.face (true, i)).boundary 1).map t) = Real.pi := by
    have he := B.second_boundary_agreement (i := (true, i)) (j := (j, i)) rfl
      ⟨ht.1.le, ht.2.le⟩
    rw [he]
    apply B.open_boundary_refined_vertex_fan g (j, i) 1 (lines (j, i)) ht
    simpa only [he] using hused j
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single i]
  · simp only [hfan, Fintype.sum_bool]
    ring
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro k _
    exact B.refined_contribution_eq_zero_of_not_mem_carrier g (k, j) (lines (k, j))
      ((B.open_second_side_mem_carrier_iff i (k, j) ht).not.mpr hji)
  · simp

theorem interior_point_mem_carrier_iff (i j : Bool × Bool) {z : Plane}
    (hz : z ∈ interior (convexHull ℝ (range (rightTriangleBasis B.scale_pos)))) :
    B.coordinates i z ∈ (B.face j).carrier ↔ j = i := by
  have hi : B.coordinates i z ∈ (B.face i).carrier := by
    rw [B.carrier_eq]
    exact ⟨z, interior_subset hz, rfl⟩
  have hside (k : Fin 3) :
      B.coordinates i z ∉ ((B.face i).boundary k).map '' Icc (0 : ℝ) 1 := by
    rintro ⟨t, ht, he⟩
    rw [B.boundary_map] at he
    have hpos := (B.coordinates i).injOn
      (B.triangle_subset_source i (B.segment_mem_hull k ht))
      (B.triangle_subset_source i (interior_subset hz)) he
    have hfront := Euler.coordinate_edge_subset_frontier (rightTriangleBasis B.scale_pos) k
      (Euler.affineChartSegment_image _ _ ▸ mem_image_of_mem _ ht)
    rw [hpos] at hfront
    exact hfront.2 hz
  constructor
  · intro hj
    by_contra hji
    rcases B.carrier_subset_sector_sides i hi with h | h | h
    · exact disjoint_left.mp (P.sector_disjoint_closedSector (Ne.symm hji)) h
        (B.carrier_subset_sector j hj)
    · exact hside 2 (B.first_image i ▸ h)
    · exact hside 1 (B.second_image i ▸ h)
  · rintro rfl
    exact hi

theorem interior_refined_vertex_fan (g : RiemannianMetric 2 S) (i : Bool × Bool)
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ)) {z : Plane}
    (hz : z ∈ interior (convexHull ℝ (range (rightTriangleBasis B.scale_pos))))
    (hused : ∃
      (u : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines i)).Triangle)
      (v : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines i)).Vertex),
      v ∈ u.1 ∧ B.coordinates i
        (((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines i)).position v) =
            B.coordinates i z) :
    (∑ j : Bool × Bool, meshVertexAngleContribution g (B.coordinates j)
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines j))
      (B.coordinates i z)) = 2 * Real.pi := by
  obtain ⟨u, v, hv, heq⟩ := hused
  have hpos := (B.coordinates i).injOn
    (B.triangle_subset_source i (B.refined_vertex_mem_hull (lines i) u v hv))
    (B.triangle_subset_source i (interior_subset hz)) heq
  have hfan := single_refineByLines_interior_vertex_fan g (B.coordinates i)
    (rightTriangleBasis B.scale_pos) (lines i) (B.coordinates_smooth i)
    (B.coordinates_smooth_symm i) (B.triangle_subset_source i) u v hv (by
      simpa only [TriangleMesh.refineByLines_support, TriangleMesh.single_support, hpos] using hz)
  rw [heq] at hfan
  rw [Finset.sum_eq_single i]
  · exact hfan
  · intro j _ hji
    exact B.refined_contribution_eq_zero_of_not_mem_carrier g j (lines j)
      ((B.interior_point_mem_carrier_iff i j hz).not.mpr hji)
  · simp

theorem mem_carrier_nonvertex_cases (i : Bool × Bool) {q : S}
    (hq : q ∈ (B.face i).carrier)
    (hne : ∀ k : Fin 3, q ≠ B.coordinates i (rightTriangleBasis B.scale_pos k)) :
    (∃ z ∈ interior (convexHull ℝ (range (rightTriangleBasis B.scale_pos))),
      B.coordinates i z = q) ∨
    ∃ (k : Fin 3) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 ∧ ((B.face i).boundary k).map t = q := by
  rw [B.carrier_eq] at hq
  obtain ⟨z, hz, heq⟩ := hq
  by_cases hint : z ∈ interior (convexHull ℝ (range (rightTriangleBasis B.scale_pos)))
  · exact Or.inl ⟨z, hint, heq⟩
  right
  have hfront : z ∈ frontier (convexHull ℝ (range (rightTriangleBasis B.scale_pos))) :=
    ⟨subset_closure hz, hint⟩
  rw [frontier_convexHull_affineBasis_fin3_segments] at hfront
  obtain ⟨k, hk⟩ := mem_iUnion.mp hfront
  rw [← Euler.affineChartSegment_image] at hk
  obtain ⟨t, ht, htz⟩ := hk
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    simp only [affineChartSegment, zero_smul, add_zero] at htz
    exact hne _ (heq.symm.trans (congrArg (B.coordinates i) htz.symm))
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    simp only [affineChartSegment, one_smul, add_sub_cancel] at htz
    exact hne _ (heq.symm.trans (congrArg (B.coordinates i) htz.symm))
  refine ⟨k, t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩, ?_⟩
  rw [B.boundary_map]
  exact (congrArg (B.coordinates i) htz).trans heq

theorem refined_vertex_fan_away_from_original_vertices (g : RiemannianMetric 2 S)
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ)) {q : S}
    (hq : ∃ i, q ∈ (B.face i).carrier) (hcenter : q ≠ p)
    (hfirst : ∀ i, q ≠ B.firstOuterTip i)
    (hsecond : ∀ i, q ≠ B.secondOuterTip i)
    (hused : ∀ i, q ∈ (B.face i).carrier → ∃
      (u : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines i)).Triangle)
      (v : ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines i)).Vertex),
      v ∈ u.1 ∧ B.coordinates i
        (((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines i)).position v) = q) :
    (∑ j : Bool × Bool, meshVertexAngleContribution g (B.coordinates j)
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines j)) q) =
      if ∃ (i : Bool × Bool) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 ∧
        ((B.face i).boundary 0).map t = q then Real.pi else 2 * Real.pi := by
  split_ifs with hchord
  · obtain ⟨i, t, ht, heq⟩ := hchord
    have hi : q ∈ (B.face i).carrier := heq ▸
      (B.open_chord_mem_carrier_iff i i ht).mpr rfl
    have hfan := B.open_chord_refined_vertex_fan g i lines ht
      (by simpa only [heq] using hused i hi)
    simpa only [heq] using hfan
  · obtain ⟨i, hi⟩ := hq
    have hne (k : Fin 3) : q ≠ B.coordinates i (rightTriangleBasis B.scale_pos k) := by
      fin_cases k
      · change q ≠ B.coordinates i (rightTriangleBasis B.scale_pos 0)
        rw [B.coordinate_vertex_zero]
        exact hcenter
      · change q ≠ B.coordinates (i.1, i.2) (rightTriangleBasis B.scale_pos 1)
        rw [B.coordinate_first_outer_tip]
        exact hfirst i.1
      · change q ≠ B.coordinates (i.1, i.2) (rightTriangleBasis B.scale_pos 2)
        rw [B.coordinate_second_outer_tip]
        exact hsecond i.2
    rcases B.mem_carrier_nonvertex_cases i hi hne with ⟨z, hz, heq⟩ | ⟨k, t, ht, heq⟩
    · have hfan := B.interior_refined_vertex_fan g i lines hz
        (by simpa only [heq] using hused i hi)
      simpa only [heq] using hfan
    · fin_cases k
      · exact False.elim (hchord ⟨i, t, ht, heq⟩)
      · have he : ((B.face (true, i.2)).boundary 1).map t = q :=
          (B.second_boundary_agreement (i := (true, i.2)) (j := i) rfl
            ⟨ht.1.le, ht.2.le⟩).trans heq
        have hfan := B.open_second_side_refined_vertex_fan g i.2 lines ht (by
          intro j
          have hj : q ∈ (B.face (j, i.2)).carrier := he ▸
            (B.open_second_side_mem_carrier_iff i.2 (j, i.2) ht).mpr rfl
          simpa only [he] using hused (j, i.2) hj)
        simpa only [he] using hfan
      · have he : ((B.face (i.1, true)).boundary 2).map t = q :=
          (B.first_boundary_agreement (i := (i.1, true)) (j := i) rfl
            ⟨ht.1.le, ht.2.le⟩).trans heq
        have hfan := B.open_first_side_refined_vertex_fan g i.1 lines ht (by
          intro j
          have hj : q ∈ (B.face (i.1, j)).carrier := he ▸
            (B.open_first_side_mem_carrier_iff i.1 (i.1, j) ht).mpr rfl
          simpa only [he] using hused (i.1, j) hj)
        simpa only [he] using hfan

end PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces
