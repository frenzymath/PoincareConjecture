import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscRoundBoundary
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ScaledBallChart











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_boundary_disc_round_image (v : E) (hv : ‖v‖ = 1)
    (D : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ))
    (hdim : 1 < Module.rank ℝ ((ℝ ∙ v)ᗮ))
    (hsphere : IsPreconnected (sphere (0 : E) 1)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ y, ‖F y‖ = ‖y‖) ∧
        F '' ((fun w => (stereoInvFun hv w : E)) '' D.closedRegion) =
          (fun w => (stereoInvFun hv w : E)) '' closedBall 0 r ∧
        ∃ C : Set E, IsCompact C ∧ ∀ y, y ∉ C → F y = y := by
  obtain ⟨r, hr, hr1, F, hFnorm, hboundary, hpole, C, hC, hfix⟩ :=
    exists_boundary_disc_round_boundary v hv D
  let : PreconnectedSpace (sphere (0 : E) 1) := Subtype.preconnectedSpace hsphere
  let G := normPreservingSphereHomeomorph F.toHomeomorph hFnorm
  let B : BallNeighborhoodChart ((ℝ ∙ v)ᗮ) ((ℝ ∙ v)ᗮ) := scaledBallNeighborhoodChart r hr
  let e := (sphereDiscChart v hv D).trans G.toOpenPartialHomeomorph
  let f := sphereDiscChart v hv B
  have he_apply (x : (ℝ ∙ v)ᗮ) : (e x : E) = F (stereoInvFun hv (D.chart x) : E) := rfl
  have hf_apply (x : (ℝ ∙ v)ᗮ) : (f x : E) = (stereoInvFun hv (B.chart x) : E) := rfl
  have he : closedBall 0 1 ⊆ e.source := by
    intro x hx
    exact ⟨sphereDiscChart_closedBall_subset_source v hv D hx, mem_univ _⟩
  have hf : closedBall 0 1 ⊆ f.source := sphereDiscChart_closedBall_subset_source v hv B
  have hbd : e '' sphere 0 1 = f '' sphere 0 1 := by
    apply (Subtype.coe_injective : Function.Injective
      ((↑) : sphere (0 : E) 1 → E)).image_injective
    have hbd' : F '' ((fun w => (stereoInvFun hv w : E)) '' D.boundary) =
        (fun w => (stereoInvFun hv w : E)) '' B.boundary := by
      rw [scaledBallNeighborhoodChart_boundary r hr]
      exact hboundary
    simpa only [BallNeighborhoodChart.boundary, image_image, he_apply, hf_apply] using hbd'
  let q : sphere (0 : E) 1 := ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩
  have hqe : q ∉ e '' closedBall 0 1 := by
    rintro ⟨x, hx, heq⟩
    exact hpole x hx (congrArg Subtype.val heq)
  have hqf : q ∉ f '' closedBall 0 1 := by
    rintro ⟨x, _, heq⟩
    exact stereoInvFun_ne_north_pole hv (B.chart x) heq
  have hregions := compactChart_region_eq_of_boundary_eq e f hdim he hf hbd hqe hqf
  have hval := congrArg (fun s : Set (sphere (0 : E) 1) =>
    ((↑) : sphere (0 : E) 1 → E) '' s) hregions
  have hclosed : F '' ((fun w => (stereoInvFun hv w : E)) '' D.closedRegion) =
      (fun w => (stereoInvFun hv w : E)) '' B.closedRegion := by
    simpa only [BallNeighborhoodChart.closedRegion, image_image, he_apply, hf_apply] using hval
  rw [scaledBallNeighborhoodChart_closedRegion r hr] at hclosed
  exact ⟨r, hr, hr1, F, hFnorm, hclosed, C, hC, hfix⟩

end PoincareConjecture.M25.Topology3D
