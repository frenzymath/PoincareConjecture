import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallRegionUniqueness

set_option autoImplicit false

open Set Metric
open scoped InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def normPreservingSphereHomeomorph (F : E ≃ₜ E)
    (hF : ∀ y, ‖F y‖ = ‖y‖) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
  F.subtype (fun y => by simp only [mem_sphere_zero_iff_norm, hF])

omit [InnerProductSpace ℝ E] in

theorem normPreservingSphereHomeomorph_apply (F : E ≃ₜ E)
    (hF : ∀ y, ‖F y‖ = ‖y‖) (q : sphere (0 : E) 1) :
    (normPreservingSphereHomeomorph F hF q : E) = F q := rfl

theorem radialStereo_supported_fixes_pole (v : E) (hv : ‖v‖ = 1)
    (f : E → E) {C : Set E} (hC : C ⊆ radialStereoTarget v)
    (hfix : ∀ y, y ∉ C → f y = y) : f v = v := by
  apply hfix
  intro hvC
  have hbad := hC hvC
  change ⟪v, v⟫_ℝ < ‖v‖ at hbad
  rw [real_inner_self_eq_norm_sq, hv] at hbad
  norm_num at hbad

noncomputable def sphereDiscChart (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ)) :
    OpenPartialHomeomorph ((ℝ ∙ v)ᗮ) (sphere (0 : E) 1) :=
  D.chart.trans (stereographic hv).symm

theorem sphereDiscChart_closedBall_subset_source (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ)) :
    closedBall 0 1 ⊆ (sphereDiscChart v hv D).source := by
  intro x hx
  exact ⟨D.closedBall_subset_source hx, mem_univ _⟩

theorem sphereDiscChart_apply (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ)) (x : (ℝ ∙ v)ᗮ) :
    sphereDiscChart v hv D x = stereoInvFun hv (D.chart x) := rfl

end PoincareConjecture.M25.Topology3D
