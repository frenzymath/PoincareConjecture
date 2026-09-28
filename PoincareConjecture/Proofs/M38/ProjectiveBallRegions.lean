import PoincareConjecture.Proofs.M38.BallPuncture
import PoincareConjecture.Proofs.M38.ChartBall
import PoincareConjecture.Proofs.M38.OpenRegionEquivalences
import PoincareConjecture.Proofs.M38.ProjectiveModel
import PoincareConjecture.Proofs.M38.PuncturedProjectiveSmooth










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

attribute [local instance] projectiveChartedSpace projective_isManifold projective_t2
  projectiveLiftChartedSpace projective_lift_isManifold


def projectiveLiftPunctureOpen (p : RealProjectiveThree) :
    TopologicalSpace.Opens projectiveCarrier.{u}.carrier :=
  ⟨({ULift.up p} : Set projectiveCarrier.{u}.carrier)ᶜ, isClosed_singleton.isOpen_compl⟩


noncomputable def projectiveLiftPuncturePoint (p : RealProjectiveThree) :
    projectiveLiftPunctureOpen.{u} p := by
  let q := (punctured_projective_connected p).nonempty.choose
  have hq : q ≠ p := (punctured_projective_connected p).nonempty.choose_spec
  refine ⟨ULift.up q, ?_⟩
  intro heq
  exact hq (congrArg ULift.down heq)


noncomputable def projectivePunctureLiftDiffeomorph (p : RealProjectiveThree) :
    (projectiveLiftPunctureOpen.{u} p) ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ (projectivePunctureOpen p) where
  toFun := fun x => ⟨x.val.down, fun h => x.property (ULift.ext _ _ h)⟩
  invFun := fun x => ⟨ULift.up x.val, fun h => x.property (congrArg ULift.down h)⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (projectivePunctureOpen p) _).mp
    exact projective_down_contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (projectiveLiftPunctureOpen p) _).mp
    exact projective_up_contMDiff.comp contMDiff_subtype_val

variable (A : GeneralizedSliceCarrier.{u}) {p : RealProjectiveThree} {U : Set A.carrier}


noncomputable def liftedPuncturedProjectiveDiffeomorph
    (C : StandardPuncturedProjectiveCover A.carrier p U) :
    (projectiveLiftPunctureOpen.{u} p) ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ (puncturedProjectiveCoverOpen C) :=
  (projectivePunctureLiftDiffeomorph p).trans (puncturedProjectiveCoverDiffeomorph C)


noncomputable def puncturedProjectiveRegionEquivalence
    (C : StandardPuncturedProjectiveCover A.carrier p U) :
    SurgeryRegionEquivalence projectiveCarrier.{u} A
      ({ULift.up p} : Set projectiveCarrier.{u}.carrier)ᶜ U :=
  openDiffeomorphRegions (projectiveLiftPunctureOpen p) (puncturedProjectiveCoverOpen C)
    (liftedPuncturedProjectiveDiffeomorph A C) (projectiveLiftPuncturePoint p)


theorem puncturedProjectiveRegionEquivalence_apply
    (C : StandardPuncturedProjectiveCover A.carrier p U)
    (x : projectiveCarrier.{u}.carrier) (hx : x.down ≠ p) :
    (puncturedProjectiveRegionEquivalence A C).map x =
      (puncturedProjectiveCoverDiffeomorph C ⟨x.down, hx⟩).val := by
  have hxl : x ∈ projectiveLiftPunctureOpen p := fun heq => hx (congrArg ULift.down heq)
  calc
    (puncturedProjectiveRegionEquivalence A C).map x =
        (liftedPuncturedProjectiveDiffeomorph A C ⟨x, hxl⟩).val :=
      openDiffeomorphRegions_apply (projectiveLiftPunctureOpen p)
        (puncturedProjectiveCoverOpen C) (liftedPuncturedProjectiveDiffeomorph A C)
        (projectiveLiftPuncturePoint p) x hxl
    _ = (puncturedProjectiveCoverDiffeomorph C ⟨x.down, hx⟩).val := rfl



noncomputable def projectiveBallRegionEquivalence
    (C : StandardPuncturedProjectiveCover A.carrier p U)
    (B : SurgeryBallEmbedding projectiveCarrier.{u}) (hcenter : B.map 0 = ULift.up p) :
    SurgeryRegionEquivalence projectiveCarrier.{u} A B.closedBallᶜ U := by
  have e := surgeryBallPunctureEquivalence B
  rw [hcenter] at e
  exact composeRegions e (puncturedProjectiveRegionEquivalence A C)



theorem exists_projective_ball_region
    (C : StandardPuncturedProjectiveCover A.carrier p U)
    (O : Set projectiveCarrier.{u}.carrier) (hO : IsOpen O) (hp : ULift.up p ∈ O) :
    ∃ B : SurgeryBallEmbedding projectiveCarrier.{u}, B.map 0 = ULift.up p ∧
      B.map '' Metric.ball 0 2 ⊆ O ∧ B.closedBall ⊆ O ∧
      Nonempty (SurgeryRegionEquivalence projectiveCarrier.{u} A B.closedBallᶜ U) := by
  obtain ⟨B, hcenter, himage, hclosed⟩ :=
    exists_surgeryBall_in_open projectiveCarrier (ULift.up p) hO hp
  exact ⟨B, hcenter, himage, hclosed, ⟨projectiveBallRegionEquivalence A C B hcenter⟩⟩

end PoincareConjecture.M38
