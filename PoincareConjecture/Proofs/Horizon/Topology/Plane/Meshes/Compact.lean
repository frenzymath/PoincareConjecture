import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.Subdivision.Fine
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.Rectangle

set_option autoImplicit false
open Set Metric

namespace Poincare.Topology.Plane.Meshes

theorem exists_triangle_containing_bounded {C : Set Plane} (hC : Bornology.IsBounded C) :
    ∃ b : AffineBasis (Fin 3) ℝ Plane, C ⊆ convexHull ℝ (range b) := by
  obtain ⟨R, hR, hball⟩ := hC.subset_ball_lt 0 (0 : Plane)
  have hab : -3 * R < R := by linarith
  have hcd : -R < 7 * R := by linarith
  refine ⟨Poincare.Topology.Plane.Triangles.rectangleLowerBasis hab hcd, ?_⟩
  intro z hz
  have hn : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hball hz
  have hx : -R < z 0 ∧ z 0 < R := abs_lt.mp ((PiLp.norm_apply_le z 0).trans_lt hn)
  have hy : -R < z 1 ∧ z 1 < R := abs_lt.mp ((PiLp.norm_apply_le z 1).trans_lt hn)
  rw [Poincare.Topology.Plane.Triangles.mem_rectangleLowerBasis_convexHull]
  refine ⟨div_nonneg (by linarith) (by linarith), ?_, ?_⟩
  · rw [div_le_div_iff₀ (by linarith : 0 < 7 * R - -R) (by linarith : 0 < R - -3 * R)]
    nlinarith [mul_lt_mul_of_pos_right hx.1 hR, mul_lt_mul_of_pos_right hy.2 hR]
  · rw [div_le_iff₀ (by linarith : 0 < R - -3 * R)]
    linarith

theorem exists_triangleMesh_covering_compact_in_open {C U : Set Plane}
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ T : TriangleMesh, C ⊆ T.toPlaneComplex.support ∧ T.toPlaneComplex.support ⊆ U := by
  obtain ⟨b, hb⟩ := exists_triangle_containing_bounded hC.isBounded
  let K := TriangleMesh.single b b.ind
  have hCK : C ⊆ K.toPlaneComplex.support := by
    rw [TriangleMesh.single_support]
    exact hb
  obtain ⟨L⟩ := K.toPlaneComplex.exists_openSubmesh K.toPlaneComplex_isPure2 hC hCK hU hCU
  exact ⟨L.mesh, L.covers, L.contained⟩

end Poincare.Topology.Plane.Meshes
