import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscRounding
import PoincareConjecture.Proofs.M25.Topology3D.Space3.StereographicCap

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem exists_boundary_disc_cap (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ))
    (hdim : 1 < Module.rank ℝ ((ℝ ∙ v)ᗮ))
    (hsphere : IsPreconnected (sphere (0 : E) 1)) :
    ∃ a : ℝ, a ∈ Ioo (1 / 2 : ℝ) 1 ∧
      ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ y, ‖F y‖ = ‖y‖) ∧
        F '' ((fun w => (stereoInvFun hv w : E)) '' D.closedRegion) =
          {y : E | ‖y‖ = 1 ∧ a ≤ ⟪-v, y⟫_ℝ} ∧
        ∃ C : Set E, IsCompact C ∧ ∀ y, y ∉ C → F y = y := by
  obtain ⟨r, hr, hr1, F, hFnorm, himage, C, hC, hfix⟩ :=
    exists_boundary_disc_round_image v hv D hdim hsphere
  refine ⟨stereographicCapHeight r, stereographicCapHeight_mem_Ioo hr hr1,
    F, hFnorm, ?_, C, hC, hfix⟩
  rw [himage, stereoInvFun_image_closedBall v hv hr hr1]

end PoincareConjecture.M25.Topology3D
