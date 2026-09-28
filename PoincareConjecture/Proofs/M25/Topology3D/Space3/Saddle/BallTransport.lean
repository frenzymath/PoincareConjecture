import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

noncomputable def BallNeighborhoodChart.mapDiffeomorph
    (B : BallNeighborhoodChart E F)
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) : BallNeighborhoodChart E G where
  chart := B.chart.trans g.toHomeomorph.toOpenPartialHomeomorph
  closedBall_subset_source := fun _ hx => ⟨B.closedBall_subset_source hx, mem_univ _⟩
  smooth := g.contDiff.comp_contDiffOn (B.smooth.mono inter_subset_left)
  smooth_symm := B.smooth_symm.comp g.symm.contDiff.contDiffOn (fun _ hy => hy.2)

@[simp] theorem BallNeighborhoodChart.mapDiffeomorph_apply
    (B : BallNeighborhoodChart E F)
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) (x : E) :
    (B.mapDiffeomorph g).chart x = g (B.chart x) := rfl

theorem BallNeighborhoodChart.mapDiffeomorph_boundary
    (B : BallNeighborhoodChart E F)
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) :
    (B.mapDiffeomorph g).boundary = g '' B.boundary := by
  change (g ∘ B.chart) '' sphere 0 1 = g '' (B.chart '' sphere 0 1)
  exact image_comp _ _ _

theorem BallNeighborhoodChart.mapDiffeomorph_inside
    (B : BallNeighborhoodChart E F)
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) :
    (B.mapDiffeomorph g).inside = g '' B.inside := by
  change (g ∘ B.chart) '' ball 0 1 = g '' (B.chart '' ball 0 1)
  exact image_comp _ _ _

theorem BallNeighborhoodChart.mapDiffeomorph_closedRegion
    (B : BallNeighborhoodChart E F)
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) :
    (B.mapDiffeomorph g).closedRegion = g '' B.closedRegion := by
  change (g ∘ B.chart) '' closedBall 0 1 = g '' (B.chart '' closedBall 0 1)
  exact image_comp _ _ _

theorem exists_ball_of_diffeomorphic_image
    (g : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, G) F G ∞) (S : Set F)
    (B : BallNeighborhoodChart E G) (hB : B.boundary = g '' S) :
    ∃ B' : BallNeighborhoodChart E F, B'.boundary = S := by
  refine ⟨B.mapDiffeomorph g.symm, ?_⟩
  rw [B.mapDiffeomorph_boundary, hB]
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hzx⟩
    have hzx' : z = x := (g.symm_apply_apply z).symm.trans hzx
    exact hzx' ▸ hz
  · intro hx
    exact ⟨g x, ⟨x, hx, rfl⟩, g.symm_apply_apply x⟩

end PoincareConjecture.M25.Topology3D
