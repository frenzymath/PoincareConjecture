import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereTangency

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]

theorem BallNeighborhoodChart.norm_symm_of_mem_boundary (B : BallNeighborhoodChart G F)
    {y : F} (hy : y ∈ B.boundary) : ‖B.chart.symm y‖ = 1 := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [B.chart.left_inv (B.closedBall_subset_source (sphere_subset_closedBall hx))]
  exact mem_sphere_zero_iff_norm.mp hx

theorem chartTransition_tangent (A : BallNeighborhoodChart E F)
    (B : BallNeighborhoodChart G F) (x v : E) (hx : ‖x‖ = 1)
    (hxt : A.chart x ∈ B.chart.target)
    (hpatch : ∀ᶠ z in 𝓝 x, ‖z‖ = 1 → A.chart z ∈ B.boundary)
    (hv : ⟪x, v⟫_ℝ = 0) :
    ⟪B.chart.symm (A.chart x),
      fderiv ℝ B.chart.symm (A.chart x) (fderiv ℝ A.chart x v)⟫_ℝ = 0 := by
  have hxs := A.closedBall_subset_source (mem_closedBall_zero_iff.mpr hx.le)
  have hA : DifferentiableAt ℝ A.chart x :=
    (A.smooth.contDiffAt (A.chart.open_source.mem_nhds hxs)).differentiableAt (by simp)
  have hB : DifferentiableAt ℝ B.chart.symm (A.chart x) :=
    (B.smooth_symm.contDiffAt (B.chart.open_target.mem_nhds hxt)).differentiableAt (by simp)
  have hnorm : ∀ᶠ z in 𝓝 x, ‖z‖ = 1 → ‖B.chart.symm (A.chart z)‖ = 1 := by
    filter_upwards [hpatch] with z hz hzs
    exact B.norm_symm_of_mem_boundary (hz hzs)
  have h := inner_fderiv_eq_zero_of_local_sphere (B.chart.symm ∘ A.chart)
    x v hx (hB.comp x hA) hnorm hv
  rw [fderiv_comp x hB hA] at h
  exact h

end PoincareConjecture.M25.Topology3D
