import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood

set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def BallNeighborhoodChart.isometryConjugate
    (B : BallNeighborhoodChart E E) (U : F ≃ₗᵢ[ℝ] E) : BallNeighborhoodChart F F where
  chart := (U.toHomeomorph.toOpenPartialHomeomorph.trans B.chart).trans
    U.symm.toHomeomorph.toOpenPartialHomeomorph
  closedBall_subset_source := by
    intro x hx
    refine ⟨⟨mem_univ _, B.closedBall_subset_source ?_⟩, mem_univ _⟩
    change U x ∈ closedBall (0 : E) 1
    simpa only [mem_closedBall_zero_iff, U.norm_map] using hx
  smooth := U.symm.contDiff.comp_contDiffOn
    (B.smooth.comp U.contDiff.contDiffOn (fun _ hx => hx.1.2))
  smooth_symm := U.symm.contDiff.comp_contDiffOn
    (B.smooth_symm.comp U.contDiff.contDiffOn (fun _ hy => hy.2.1))

@[simp] theorem BallNeighborhoodChart.isometryConjugate_apply
    (B : BallNeighborhoodChart E E) (U : F ≃ₗᵢ[ℝ] E) (x : F) :
    (B.isometryConjugate U).chart x = U.symm (B.chart (U x)) := rfl

end PoincareConjecture.M25.Topology3D
