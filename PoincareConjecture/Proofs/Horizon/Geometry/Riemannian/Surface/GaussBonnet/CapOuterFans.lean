import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterCorners

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

theorem firstOuterTip_ne_center (i : Bool) : B.firstOuterTip i ≠ p := by
  intro h
  have hv := (B.coordinates (i, true)).injOn
    (B.triangle_subset_source _ (subset_convexHull ℝ _ (mem_range_self 1)))
    (B.triangle_subset_source _ (subset_convexHull ℝ _ (mem_range_self 0)))
    (h.trans (B.coordinate_vertex_zero (i, true)).symm)
  have hi := (rightTriangleBasis B.scale_pos).ind.injective hv
  exact (by decide : (1 : Fin 3) ≠ 0) hi

theorem secondOuterTip_ne_center (i : Bool) : B.secondOuterTip i ≠ p := by
  intro h
  have hv := (B.coordinates (true, i)).injOn
    (B.triangle_subset_source _ (subset_convexHull ℝ _ (mem_range_self 2)))
    (B.triangle_subset_source _ (subset_convexHull ℝ _ (mem_range_self 0)))
    (h.trans (B.coordinate_vertex_zero (true, i)).symm)
  have hi := (rightTriangleBasis B.scale_pos).ind.injective hv
  exact (by decide : (2 : Fin 3) ≠ 0) hi

theorem firstOuterTip_mem_firstSide (i j : Bool) :
    B.firstOuterTip i ∈ P.firstSide (i, j) B.scale := by
  have h := B.first_map (i, j) 1 (by simp)
  rw [B.boundary_map] at h
  have heq : B.firstOuterTip i = P.sectorCoordinates (i, j) (B.scale, 0) := by
    rw [← B.coordinate_first_outer_tip i j]
    simpa [affineChartSegment, Fin.succAbove, Fin.lt_def] using h
  exact ⟨B.scale, ⟨B.scale_pos.le, le_rfl⟩, heq.symm⟩

theorem secondOuterTip_mem_secondSide (i j : Bool) :
    B.secondOuterTip i ∈ P.secondSide (j, i) B.scale := by
  have h := B.second_map (j, i) 1 (by simp)
  rw [B.boundary_map] at h
  have heq : B.secondOuterTip i = P.sectorCoordinates (j, i) (0, B.scale) := by
    rw [← B.coordinate_second_outer_tip i j]
    simpa [affineChartSegment] using h
  exact ⟨B.scale, ⟨B.scale_pos.le, le_rfl⟩, heq.symm⟩

theorem firstOuterTip_mem_carrier_iff (i : Bool) (j : Bool × Bool) :
    B.firstOuterTip i ∈ (B.face j).carrier ↔ j.1 = i := by
  constructor
  · intro h
    by_contra hne
    exact B.firstOuterTip_ne_center i
      (P.firstSide_inter_opposite_sector (i := (i, true)) (Ne.symm hne)
        B.scale_lt_width.le
        ⟨B.firstOuterTip_mem_firstSide i true, B.carrier_subset_sector j h⟩)
  · rcases j with ⟨j, k⟩
    intro h
    dsimp at h
    subst j
    rw [B.carrier_eq]
    exact ⟨rightTriangleBasis B.scale_pos 1,
      subset_convexHull ℝ _ (mem_range_self 1), B.coordinate_first_outer_tip i k⟩

theorem secondOuterTip_mem_carrier_iff (i : Bool) (j : Bool × Bool) :
    B.secondOuterTip i ∈ (B.face j).carrier ↔ j.2 = i := by
  constructor
  · intro h
    by_contra hne
    exact B.secondOuterTip_ne_center i
      (P.secondSide_inter_opposite_sector (i := (true, i)) (Ne.symm hne)
        B.scale_lt_width.le
        ⟨B.secondOuterTip_mem_secondSide i true, B.carrier_subset_sector j h⟩)
  · rcases j with ⟨j, k⟩
    intro h
    dsimp at h
    subst k
    rw [B.carrier_eq]
    exact ⟨rightTriangleBasis B.scale_pos 2,
      subset_convexHull ℝ _ (mem_range_self 2), B.coordinate_second_outer_tip i j⟩

theorem refined_contribution_eq_zero_of_not_mem_carrier
    (g : RiemannianMetric 2 S) (i : Bool × Bool)
    (lines : List (Plane →ᵃ[ℝ] ℝ)) {q : S} (hq : q ∉ (B.face i).carrier) :
    meshVertexAngleContribution g (B.coordinates i)
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines lines) q = 0 := by
  classical
  let M := (TriangleMesh.single (rightTriangleBasis B.scale_pos)
    (rightTriangleBasis B.scale_pos).ind).refineByLines lines
  change meshVertexAngleContribution g (B.coordinates i) M q = 0
  unfold meshVertexAngleContribution
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro k _
  have hne : B.coordinates i (meshTriangleBasis M t k) ≠ q := by
    intro heq
    apply hq
    rw [B.carrier_eq]
    refine ⟨meshTriangleBasis M t k, ?_, heq⟩
    have hm := meshTriangleBasis_subset_support M t
      (subset_convexHull ℝ _ (mem_range_self k))
    simpa only [M, TriangleMesh.refineByLines_support, TriangleMesh.single_support] using hm
  simp only [if_neg hne]

theorem sum_refined_first_outer_contributions (g : RiemannianMetric 2 S) (i : Bool)
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ j : Bool, ∑ k : Bool,
      meshVertexAngleContribution g (B.coordinates (j, k))
        ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (j, k)))
        (B.firstOuterTip i)) =
    ∑ k : Bool, meshVertexAngleContribution g (B.coordinates (i, k))
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (i, k)))
      (B.firstOuterTip i) := by
  classical
  apply Finset.sum_eq_single i
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro k _
    exact B.refined_contribution_eq_zero_of_not_mem_carrier g (j, k) _
      ((B.firstOuterTip_mem_carrier_iff i (j, k)).not.mpr hji)
  · simp

theorem sum_refined_second_outer_contributions (g : RiemannianMetric 2 S) (i : Bool)
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ j : Bool, ∑ k : Bool,
      meshVertexAngleContribution g (B.coordinates (j, k))
        ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (j, k)))
        (B.secondOuterTip i)) =
    ∑ k : Bool, meshVertexAngleContribution g (B.coordinates (k, i))
      ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
        (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (k, i)))
      (B.secondOuterTip i) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_eq_single i
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro k _
    exact B.refined_contribution_eq_zero_of_not_mem_carrier g (k, j) _
      ((B.secondOuterTip_mem_carrier_iff i (k, j)).not.mpr hji)
  · simp

theorem sum_refined_first_outer_fan (g : RiemannianMetric 2 S) (i : Bool)
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ j : Bool, ∑ k : Bool,
      meshVertexAngleContribution g (B.coordinates (j, k))
        ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (j, k)))
        (B.firstOuterTip i)) +
    (∑ j : Bool, g.cornerAngle (B.firstOuterTip i)
      (B.firstOuterSpoke i) (B.firstOuterChord i j)) = 2 * Real.pi := by
  rw [B.sum_refined_first_outer_contributions]
  exact B.first_outer_refined_corner_pair g i (fun j => lines (i, j))

theorem sum_refined_second_outer_fan (g : RiemannianMetric 2 S) (i : Bool)
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ j : Bool, ∑ k : Bool,
      meshVertexAngleContribution g (B.coordinates (j, k))
        ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (j, k)))
        (B.secondOuterTip i)) +
    (∑ j : Bool, g.cornerAngle (B.secondOuterTip i)
      (B.secondOuterSpoke i) (B.secondOuterChord i j)) = 2 * Real.pi := by
  rw [B.sum_refined_second_outer_contributions]
  exact B.second_outer_refined_corner_pair g i (fun j => lines (j, i))

end PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces
