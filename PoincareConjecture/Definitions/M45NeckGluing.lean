import PoincareConjecture.Definitions.Ch15.SurgeryFlow

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

structure M45CylinderPatch (S : GeneralizedSliceCarrier.{u})
    (length : ℝ) (center : S.carrier) where
  length_pos : 0 < length
  carrier : Set S.carrier
  carrier_open : IsOpen carrier
  coordinate : RoundCylinderSpace → S.carrier
  inverse : S.carrier → RoundCylinderSpace
  coordinate_image : coordinate '' (Set.univ ×ˢ Set.Ioo (-length) length) = carrier
  coordinate_left_inverse : Set.LeftInvOn inverse coordinate
    (Set.univ ×ˢ Set.Ioo (-length) length)
  coordinate_right_inverse : Set.LeftInvOn coordinate inverse carrier
  inverse_domain : ∀ x ∈ carrier, (inverse x).2 ∈ Set.Ioo (-length) length
  coordinate_smooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    coordinate (Set.univ ×ˢ Set.Ioo (-length) length)
  inverse_smooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ inverse carrier
  center_sphere : ∃ z : UnitTwoSphere, coordinate (z, 0) = center

structure M45NeckGluingInput (epsilon beta : ℝ) where
  recent_duration : ℝ
  older_duration : ℝ
  recent_duration_pos : 0 < recent_duration
  durations_ordered : recent_duration < older_duration
  recent_carrier : GeneralizedSliceCarrier.{u}
  older_carrier : GeneralizedSliceCarrier.{u}
  recent_flow : RicciFlow 3 recent_carrier.carrier (Set.Icc (-recent_duration) 0)
  older_flow : RicciFlow 3 older_carrier.carrier
    (Set.Ioc (-older_duration) (-recent_duration))
  center : recent_carrier.carrier
  final_scalar_one : (recent_flow.connection 0).scalarCurvature center = 1
  recent_patch : M45CylinderPatch recent_carrier (beta * epsilon)⁻¹ center
  recent_comparison : RoundCylinderFamilyClose (beta * epsilon)
    (Set.Icc (-recent_duration) 0)
    (fun t => roundCylinderPullback (recent_flow.metric t) recent_patch.coordinate)
  older_neck : SurgeryOrdinaryStrongNeck older_carrier older_flow
    (-recent_duration) (beta * epsilon / 2)
  identify : recent_carrier.carrier → older_carrier.carrier
  identify_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ identify recent_patch.carrier
  identify_injective : Set.InjOn identify recent_patch.carrier
  identify_image : identify '' recent_patch.carrier ⊆ older_neck.neck.carrier
  identify_center : identify center = older_neck.neck.center
  joining_metric : ∀ x ∈ recent_patch.carrier,
    ∀ v w : TangentSpace (𝓡 3) x,
      (older_flow.metric (-recent_duration)).inner (identify x)
        (mfderiv (𝓡 3) (𝓡 3) identify x v)
        (mfderiv (𝓡 3) (𝓡 3) identify x w) =
          (recent_flow.metric (-recent_duration)).inner x v w

noncomputable def M45NeckGluingInput.piecewiseTensor
    {epsilon beta : ℝ} (I : M45NeckGluingInput.{u} epsilon beta)
    (coordinate : RoundCylinderSpace → I.recent_carrier.carrier) :
    ℝ → RoundCylinderTwoTensor :=
  fun t => if -I.recent_duration ≤ t then
    roundCylinderPullback (I.recent_flow.metric t) coordinate
  else
    roundCylinderPullback (I.older_flow.metric t) (I.identify ∘ coordinate)

structure M45NeckGluingConclusion {epsilon beta : ℝ}
    (I : M45NeckGluingInput.{u} epsilon beta) where
  patch : M45CylinderPatch I.recent_carrier epsilon⁻¹ I.center
  coordinate_eq : patch.coordinate = I.recent_patch.coordinate
  inverse_eq : patch.inverse = I.recent_patch.inverse
  recent_subset : patch.carrier ⊆ I.recent_patch.carrier
  older_survival : ∀ t ∈ Set.Ioc (-1 : ℝ) 0, t < -I.recent_duration →
    t ∈ Set.Ioc (-I.older_duration) (-I.recent_duration)
  comparison : RoundCylinderFamilyClose epsilon (Set.Ioc (-1 : ℝ) 0)
    (I.piecewiseTensor patch.coordinate)
  joint_smooth : ∀ (q : UnitTwoSphere) (a b : Fin 3),
    ContDiffOn ℝ ∞
      (fun p : ℝ × RoundCylinderCoordinates =>
        roundCylinderTensorCoefficient (I.piecewiseTensor patch.coordinate p.1)
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p.2 a b)
      (Set.Ioc (-1 : ℝ) 0 ×ˢ
        ((chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
          Set.Ioo (-epsilon⁻¹) epsilon⁻¹))

def M45NeckGluingProperty (epsilon beta : ℝ) : Prop :=
  ∀ I : M45NeckGluingInput.{u} epsilon beta, Nonempty (M45NeckGluingConclusion I)

end PoincareConjecture
