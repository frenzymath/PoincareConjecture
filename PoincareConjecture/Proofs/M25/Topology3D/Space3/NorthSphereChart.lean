import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereCoordinates

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

noncomputable def northSphereChart : OpenPartialHomeomorph UnitTwoSphere E2 where
  toFun := northSphereCoordinate
  invFun := northSpherePoint
  source := northSphereDomain
  target := univ
  map_source' _ _ := mem_univ _
  map_target' w _ := northSpherePoint_mem_domain w
  left_inv' _ hq := northSpherePoint_coordinate hq
  right_inv' w _ := northSphereCoordinate_point w
  open_source := northSphereDomain_isOpen
  open_target := isOpen_univ
  continuousOn_toFun := northSphereCoordinate_contMDiffOn.continuousOn
  continuousOn_invFun := northSpherePoint_contMDiff.continuous.continuousOn

theorem northSphereChart_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ northSphereChart northSphereChart.source :=
  northSphereCoordinate_contMDiffOn

theorem northSphereChart_symm_contMDiff :
    ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ northSphereChart.symm := northSpherePoint_contMDiff

theorem northSpherePoint_height_nonneg_iff (w : E2) :
    0 ≤ (heightCoordinates (northSpherePoint w : E3)).2 ↔ ‖w‖ ≤ 1 := by
  rw [northSpherePoint_coordinates]
  have hD : 0 < 1 + ‖w‖ ^ 2 := by positivity
  change 0 ≤ (1 - ‖w‖ ^ 2) / (1 + ‖w‖ ^ 2) ↔ ‖w‖ ≤ 1
  constructor
  · intro h
    have hn := (le_div_iff₀ hD).mp h
    nlinarith [norm_nonneg w]
  · intro h
    exact div_nonneg (by nlinarith [norm_nonneg w]) hD.le

theorem northSpherePoint_image_closedBall :
    northSpherePoint '' closedBall 0 1 =
      {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} := by
  ext q
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (northSpherePoint_height_nonneg_iff w).mpr (mem_closedBall_zero_iff.mp hw)
  · intro hq
    have hsrc : q ∈ northSphereDomain := by
      change -1 < (heightCoordinates (q : E3)).2
      exact lt_of_lt_of_le (by norm_num) hq
    refine ⟨northSphereCoordinate q, ?_, northSpherePoint_coordinate hsrc⟩
    apply mem_closedBall_zero_iff.mpr
    apply (northSpherePoint_height_nonneg_iff _).mp
    rwa [northSpherePoint_coordinate hsrc]

theorem northSpherePoint_equator (θ : UnitCircle) :
    heightCoordinates (northSpherePoint θ.1 : E3) = (θ.1, 0) := by
  rw [northSpherePoint_coordinates, norm_eq_of_mem_sphere θ]
  norm_num

theorem northern_hemisphere_subset_chart_source :
    {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} ⊆ northSphereChart.source := by
  intro q hq
  change -1 < (heightCoordinates (q : E3)).2
  exact lt_of_lt_of_le (by norm_num) hq

theorem northSphereChart_image_northern_hemisphere :
    northSphereChart '' {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} =
      closedBall 0 1 := by
  rw [← northSpherePoint_image_closedBall, image_image]
  change (fun w => northSphereCoordinate (northSpherePoint w)) '' closedBall 0 1 = _
  simp only [northSphereCoordinate_point, image_id']

end PoincareConjecture.M25.Topology3D
