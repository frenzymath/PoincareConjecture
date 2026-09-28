import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSourceNeck
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckPrecompactBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))

noncomputable def GeneralizedStrongNeck.rescaled_half_flow :
    RicciFlow 3 (strongNeckOpen S) (Icc (-(1 / 2 : ℝ)) 0) := by
  let q : ℝ := S.scale⁻¹ ^ 2
  let K := Proofs.M12.cylinderPhysicalInterval t q
    S.time_cylinder.scale_pos strongNeckBackwardInterval
  have hsub : Icc (-(1 / 2 : ℝ)) 0 ⊆
      (parabolicInterval q S.time_cylinder.scale_pos t K).domain := by
    intro s hs
    apply (mem_parabolicInterval_iff q S.time_cylinder.scale_pos t K s).2
    refine ⟨s, ?_, rfl⟩
    exact ⟨by linarith [hs.1], hs.2⟩
  exact Poincare.Geometry.RicciFlow.Harnack.restrictFlow H.rescaling.flow
    hsub ordConnected_Icc
    ⟨-(1 / 2 : ℝ), by norm_num, 0, by norm_num, by norm_num⟩

@[simp] theorem GeneralizedStrongNeck.rescaled_half_flow_metric (s : ℝ) :
    (GeneralizedStrongNeck.rescaled_half_flow S H).metric s =
      H.rescaling.flow.metric s := rfl

@[simp] theorem GeneralizedStrongNeck.rescaled_half_flow_connection (s : ℝ) :
    (GeneralizedStrongNeck.rescaled_half_flow S H).connection s =
      H.rescaling.flow.connection s := rfl

noncomputable def GeneralizedStrongNeck.rescaled_half_source_neck
    (hepsilon : epsilon < 1 / 2) :
    EpsilonNeck ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0) :=
  GeneralizedStrongNeck.rescaled_source_neck S hepsilon H

theorem GeneralizedStrongNeck.rescaled_half_source_neck_eq
    (hepsilon : epsilon < 1 / 2) :
    GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon =
      GeneralizedStrongNeck.rescaled_source_neck S hepsilon H := rfl

@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_epsilon
    (hepsilon : epsilon < 1 / 2) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).epsilon =
      epsilon := rfl

@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_scale
    (hepsilon : epsilon < 1 / 2) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).scale = 1 := rfl

@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_center
    (hepsilon : epsilon < 1 / 2) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).center =
      strongNeckSourceCenter S := rfl

@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_center_val
    (hepsilon : epsilon < 1 / 2) :
    ((GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).center :
      (F.slice t).carrier) = S.center := rfl

@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_connection
    (hepsilon : epsilon < 1 / 2) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).connection =
      (GeneralizedStrongNeck.rescaled_half_flow S H).connection 0 := rfl

@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_carrier
    (hepsilon : epsilon < 1 / 2) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).carrier =
      univ := rfl

theorem GeneralizedStrongNeck.rescaled_half_source_neck_coordinate_map_val
    (hepsilon : epsilon < 1 / 2) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ((GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).coordinate_map z :
      (F.slice t).carrier) = S.coordinate_map z := by
  exact strongNeckSourceMap_val_on_strip S z hz

theorem GeneralizedStrongNeck.rescaled_half_source_neck_coordinate_inverse
    (hepsilon : epsilon < 1 / 2) (x : strongNeckOpen S) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).coordinate_inverse x =
      S.coordinate_inverse (x : (F.slice t).carrier) := rfl

theorem GeneralizedStrongNeck.rescaled_half_scalar_at_center :
    ((GeneralizedStrongNeck.rescaled_half_flow S H).connection 0).scalarCurvature
      (strongNeckSourceCenter S) = 1 := by
  simpa only [GeneralizedStrongNeck.rescaled_half_flow_connection,
    strongNeckSourceCenter] using
    GeneralizedStrongNeck.rescaled_scalar_at_center S H

theorem GeneralizedStrongNeck.rescaled_half_center_ball_capture
    (hepsilon : epsilon < 1 / 2) :
    let N := GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon
    let K := N.coordinate_map ''
      (univ ×ˢ Icc (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2))
    IsCompact K ∧
      IsCompact (closure (((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).ball
        N.center (epsilon⁻¹ / 8))) ∧
      closure (((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).ball
        N.center (epsilon⁻¹ / 8)) ⊆ K := by
  let N := GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon
  let K : Set (strongNeckOpen S) := N.coordinate_map ''
    (univ ×ˢ Icc (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2))
  have hNepsilon : N.epsilon = epsilon := rfl
  have hNscale : N.scale = 1 := rfl
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hlo : -N.epsilon⁻¹ < -(N.epsilon⁻¹ / 2) := by linarith
  have hhi : N.epsilon⁻¹ / 2 < N.epsilon⁻¹ := by linarith
  have hK : IsCompact K := N.isCompact_coordinate_slab_intrinsic hlo hhi
  have hballK : ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).ball
      N.center (epsilon⁻¹ / 8) ⊆ K := by
    intro x hx
    have hmiddle := N.small_ball_subset_middle N.center_on_central_sphere
      (by simpa only [hNscale, hNepsilon, one_mul] using hx)
    exact ⟨N.coordinate_inverse x,
      ⟨mem_univ _, hmiddle.2.1.le, hmiddle.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hmiddle.1⟩
  refine ⟨hK, ?_, closure_minimal hballK hK.isClosed⟩
  simpa only [hNscale, hNepsilon, one_mul] using
    (N.precompact_ball_of_central_sphere N.center_on_central_sphere).1

end PoincareConjecture.M28
