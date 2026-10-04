import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.SourceGeometry.NeckGeometry.StrongNeckSourceNeck
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.NeckGeometry.NeckPrecompactBalls

/-!
# The half-window flow of one chosen original strong-neck rescaling

Definition 9.78 and Claims 10.3-10.11. Restrict the supplied raw M12/M13
rescaling itself, retaining its total metric and connection representatives.
Its existing normalized source neck then supplies an actual compact center
ball at time zero. See the claim10_4 exact-strong-neck-half-flow derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.M28

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))

/-- Restrict the supplied normalized source flow to its actual closed
half window, without selecting a second rescaling (Definition 9.78). -/
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

/-- Every total metric representative is literally the chosen H metric,
including at real times outside the restricted window (Definition 9.78). -/
@[simp] theorem GeneralizedStrongNeck.rescaled_half_flow_metric (s : ℝ) :
    (GeneralizedStrongNeck.rescaled_half_flow S H).metric s =
      H.rescaling.flow.metric s := rfl

/-- Restriction also keeps the same dependent connection representative
at every real time (Definition 9.78). -/
@[simp] theorem GeneralizedStrongNeck.rescaled_half_flow_connection (s : ℝ) :
    (GeneralizedStrongNeck.rescaled_half_flow S H).connection s =
      H.rescaling.flow.connection s := rfl

/-- The time-zero neck is the existing source neck for the SAME H;
the half-flow metric is definitionally unchanged (Definition 9.78). -/
noncomputable def GeneralizedStrongNeck.rescaled_half_source_neck
    (hepsilon : epsilon < 1 / 2) :
    EpsilonNeck ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0) :=
  GeneralizedStrongNeck.rescaled_source_neck S hepsilon H

/-- The half-flow constructor does not replace the source certificate. -/
theorem GeneralizedStrongNeck.rescaled_half_source_neck_eq
    (hepsilon : epsilon < 1 / 2) :
    GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon =
      GeneralizedStrongNeck.rescaled_source_neck S hepsilon H := rfl

/-- The normalized source retains the original epsilon (Definition 9.78). -/
@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_epsilon
    (hepsilon : epsilon < 1 / 2) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).epsilon =
      epsilon := rfl

/-- The actual source neck has normalization scale exactly one. -/
@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_scale
    (hepsilon : epsilon < 1 / 2) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).scale = 1 := rfl

/-- The center is the literal original center lifted into the source. -/
@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_center
    (hepsilon : epsilon < 1 / 2) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).center =
      strongNeckSourceCenter S := rfl

/-- Source inclusion sends the normalized center to the original center. -/
@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_center_val
    (hepsilon : epsilon < 1 / 2) :
    ((GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).center :
      (F.slice t).carrier) = S.center := rfl

/-- The source neck uses the half-flow's exact chosen connection. -/
@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_connection
    (hepsilon : epsilon < 1 / 2) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).connection =
      (GeneralizedStrongNeck.rescaled_half_flow S H).connection 0 := rfl

/-- The source neck's carrier is the whole open source manifold. -/
@[simp] theorem GeneralizedStrongNeck.rescaled_half_source_neck_carrier
    (hepsilon : epsilon < 1 / 2) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).carrier =
      univ := rfl

/-- On the genuine strip, the chosen half-flow neck has the literal
original coordinate map after source inclusion (Definition 9.78). -/
theorem GeneralizedStrongNeck.rescaled_half_source_neck_coordinate_map_val
    (hepsilon : epsilon < 1 / 2) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ((GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).coordinate_map z :
      (F.slice t).carrier) = S.coordinate_map z := by
  exact strongNeckSourceMap_val_on_strip S z hz

/-- The source inverse is the original inverse on the actual source
carrier; no exterior coordinate values are used (Definition 9.78). -/
theorem GeneralizedStrongNeck.rescaled_half_source_neck_coordinate_inverse
    (hepsilon : epsilon < 1 / 2) (x : strongNeckOpen S) :
    (GeneralizedStrongNeck.rescaled_half_source_neck S H hepsilon).coordinate_inverse x =
      S.coordinate_inverse (x : (F.slice t).carrier) := rfl

/-- Actual M12/M13 normalization gives scalar one at the same lifted
center for the chosen half flow (Definition 9.78). -/
theorem GeneralizedStrongNeck.rescaled_half_scalar_at_center :
    ((GeneralizedStrongNeck.rescaled_half_flow S H).connection 0).scalarCurvature
      (strongNeckSourceCenter S) = 1 := by
  simpa only [GeneralizedStrongNeck.rescaled_half_flow_connection,
    strongNeckSourceCenter] using
    GeneralizedStrongNeck.rescaled_scalar_at_center S H

/-- The normalized center ball at radius epsilon inverse over eight has
compact closure captured in the actual middle coordinate slab. The metric
is the source half-flow metric, without an ambient-distance substitution
(Claim 10.3 and Appendix A.1). -/
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

end PoincareMT.M28
