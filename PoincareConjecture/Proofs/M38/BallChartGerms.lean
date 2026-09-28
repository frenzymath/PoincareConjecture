import PoincareConjecture.Proofs.M38.BallCoordinatePatch









set_option autoImplicit false

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}}


def surgeryBallTransitionDomain (B C : SurgeryBallEmbedding A) : Set StandardCapSpace :=
  Metric.ball 0 2 ∩ B.map ⁻¹' (C.map '' Metric.ball 0 2)


noncomputable def surgeryBallTransition (B C : SurgeryBallEmbedding A) :
    StandardCapSpace → StandardCapSpace := C.inverse ∘ B.map


theorem surgeryBallTransitionDomain_open (B C : SurgeryBallEmbedding A) :
    IsOpen (surgeryBallTransitionDomain B C) :=
  B.map_smooth.continuousOn.isOpen_inter_preimage Metric.isOpen_ball (surgeryBall_image_open C)


theorem surgeryBallTransition_smooth (B C : SurgeryBallEmbedding A) :
    ContDiffOn ℝ ∞ (surgeryBallTransition B C) (surgeryBallTransitionDomain B C) := by
  apply contMDiffOn_iff_contDiffOn.mp
  exact C.inverse_smooth.comp (B.map_smooth.mono Set.inter_subset_left) (fun _ hx => hx.2)


theorem surgeryBallTransition_left_inverse (B C : SurgeryBallEmbedding A)
    {x : StandardCapSpace} (hx : x ∈ surgeryBallTransitionDomain B C) :
    surgeryBallTransition C B (surgeryBallTransition B C x) = x := by
  change B.inverse (C.map (C.inverse (B.map x))) = x
  rw [C.right_inverse hx.2, B.left_inverse hx.1]


theorem surgeryBallTransition_mapsTo (B C : SurgeryBallEmbedding A) :
    Set.MapsTo (surgeryBallTransition B C) (surgeryBallTransitionDomain B C)
      (surgeryBallTransitionDomain C B) := by
  intro x hx
  refine ⟨surgeryBall_inverse_mem C hx.2, ?_⟩
  change C.map (C.inverse (B.map x)) ∈ B.map '' Metric.ball 0 2
  rw [C.right_inverse hx.2]
  exact Set.mem_image_of_mem B.map hx.1


theorem surgeryBallTransitionDomain_zero (B C : SurgeryBallEmbedding A)
    (hcenter : B.map 0 = C.map 0) :
    (0 : StandardCapSpace) ∈ surgeryBallTransitionDomain B C := by
  refine ⟨by simp, ?_⟩
  change B.map 0 ∈ C.map '' Metric.ball 0 2
  rw [hcenter]
  exact Set.mem_image_of_mem C.map (by simp)


theorem surgeryBallTransition_zero (B C : SurgeryBallEmbedding A)
    (hcenter : B.map 0 = C.map 0) : surgeryBallTransition B C 0 = 0 := by
  change C.inverse (B.map 0) = 0
  rw [hcenter, C.left_inverse (by simp)]


theorem surgeryBallTransition_derivative_comp (B C : SurgeryBallEmbedding A)
    (hcenter : B.map 0 = C.map 0) :
    (fderiv ℝ (surgeryBallTransition C B) 0).comp
        (fderiv ℝ (surgeryBallTransition B C) 0) =
      ContinuousLinearMap.id ℝ StandardCapSpace := by
  have hf := ((surgeryBallTransition_smooth B C).contDiffAt
    ((surgeryBallTransitionDomain_open B C).mem_nhds
      (surgeryBallTransitionDomain_zero B C hcenter))).differentiableAt (by simp)
  have hg := ((surgeryBallTransition_smooth C B).contDiffAt
    ((surgeryBallTransitionDomain_open C B).mem_nhds
      (surgeryBallTransitionDomain_zero C B hcenter.symm))).differentiableAt (by simp)
  have hg' : HasFDerivAt (surgeryBallTransition C B)
      (fderiv ℝ (surgeryBallTransition C B) 0) (surgeryBallTransition B C 0) := by
    rw [surgeryBallTransition_zero B C hcenter]
    exact hg.hasFDerivAt
  have heq : surgeryBallTransition C B ∘ surgeryBallTransition B C =ᶠ[𝓝 0] id := by
    filter_upwards [(surgeryBallTransitionDomain_open B C).mem_nhds
      (surgeryBallTransitionDomain_zero B C hcenter)] with x hx
    exact surgeryBallTransition_left_inverse B C hx
  exact (hg'.comp 0 hf.hasFDerivAt).unique
    ((hasFDerivAt_id (𝕜 := ℝ) 0).congr_of_eventuallyEq heq)


noncomputable def surgeryBallTransitionLinear (B C : SurgeryBallEmbedding A)
    (hcenter : B.map 0 = C.map 0) : StandardCapSpace ≃L[ℝ] StandardCapSpace :=
  ContinuousLinearEquiv.equivOfInverse' (fderiv ℝ (surgeryBallTransition B C) 0)
    (fderiv ℝ (surgeryBallTransition C B) 0)
    (surgeryBallTransition_derivative_comp C B hcenter.symm)
    (surgeryBallTransition_derivative_comp B C hcenter)


theorem surgeryBallTransitionLinear_coe (B C : SurgeryBallEmbedding A)
    (hcenter : B.map 0 = C.map 0) :
    (surgeryBallTransitionLinear B C hcenter : StandardCapSpace →L[ℝ] StandardCapSpace) =
      fderiv ℝ (surgeryBallTransition B C) 0 := rfl


theorem surgeryBallNormalizedInverse_derivative (B C : SurgeryBallEmbedding A)
    (hcenter : B.map 0 = C.map 0) :
    fderiv ℝ (fun x => surgeryBallTransitionLinear B C hcenter
      (surgeryBallTransition C B x)) 0 = ContinuousLinearMap.id ℝ StandardCapSpace := by
  have hg := ((surgeryBallTransition_smooth C B).contDiffAt
    ((surgeryBallTransitionDomain_open C B).mem_nhds
      (surgeryBallTransitionDomain_zero C B hcenter.symm))).differentiableAt (by simp)
  have hd := (surgeryBallTransitionLinear B C hcenter).hasFDerivAt.comp 0 hg.hasFDerivAt
  calc
    _ = (surgeryBallTransitionLinear B C hcenter :
        StandardCapSpace →L[ℝ] StandardCapSpace).comp
        (fderiv ℝ (surgeryBallTransition C B) 0) := hd.fderiv
    _ = ContinuousLinearMap.id ℝ StandardCapSpace := by
      rw [surgeryBallTransitionLinear_coe]
      exact surgeryBallTransition_derivative_comp C B hcenter.symm

end PoincareConjecture.M38
