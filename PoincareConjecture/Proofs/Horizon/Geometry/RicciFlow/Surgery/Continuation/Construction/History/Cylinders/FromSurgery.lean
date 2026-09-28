import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Realization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Cylinders.LiftedBoxes
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Cylinders.LocalEmbedding









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Surgery.RegularHistory

open Cylinders

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)
  (L : ∀ t, t ∈ F.surgery_times → t ∈ W.interval →
    RicciFlowLocalTheory 3 (F.slice t).carrier)
  {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {J : Set ℝ} {U : Set C.carrier}
  (e : SurgeryFlowCylinder F C origin scale J U)
  (htime : ∀ s ∈ J, origin + s / scale ∈ W.interval)
  (hguard : ∀ s hs, e.forward s hs '' U ⊆ m33RegularRegion F (origin + s / scale))

include hguard


def fromSurgeryCylinder : GeneralizedFlowCylinder (generalized W L) C origin scale J U where
  scale_pos := e.scale_pos
  forward := liftedForward W e htime
  inverse := liftedInverse W e
  forward_smooth := liftedForward_smooth W e htime hguard
  inverse_smooth := liftedInverse_smooth W e htime hguard
  left_inverse := lifted_left_inverse W e htime hguard
  right_inverse := lifted_right_inverse W e htime hguard
  embedding := GeneralizedRicciFlowData.isEmbedding_of_local_box
    (G := generalized W L) (origin := origin) (scale := scale) (J := J) (X := U)
    e.scale_pos htime
    (fun s hs (x : U) => liftedForward W e htime s hs x.val)
    (exists_lifted_box W L e htime hguard)
  vertical_compatibility := lifted_vertical_compatibility W L e htime hguard

theorem fromSurgeryCylinder_forward (s : ℝ) (hs : s ∈ J) (x : C.carrier) (hx : x ∈ U) :
    (realization W L).forward (origin + s / scale) (htime s hs)
      ((fromSurgeryCylinder W L e htime hguard).forward s hs x) = e.forward s hs x :=
  ambient_liftedForward W e htime hguard s hs x hx

theorem fromSurgeryCylinder_pullbackInner (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ J) (x : C.carrier) (hx : x ∈ U)
    (v w : TangentSpace (𝓡 3) x) :
    (fromSurgeryCylinder W L e htime hguard).pullbackInner s hs x v w =
      e.pullbackInner s hs x v w :=
  lifted_pullbackInner W e htime hguard hU s hs x hx v w


theorem cylinders_from_surgery (hU : IsOpen U) :
    ∃ d : GeneralizedFlowCylinder (generalized W L) C origin scale J U,
      (∀ s hs x, x ∈ U →
        (realization W L).forward (origin + s / scale) (htime s hs) (d.forward s hs x) =
          e.forward s hs x) ∧
      (∀ s hs x, x ∈ U → ∀ v w : TangentSpace (𝓡 3) x,
        d.pullbackInner s hs x v w = e.pullbackInner s hs x v w) := by
  exact ⟨fromSurgeryCylinder W L e htime hguard,
    fromSurgeryCylinder_forward W L e htime hguard,
    fromSurgeryCylinder_pullbackInner W L e htime hguard hU⟩

end PoincareConjecture.Surgery.RegularHistory
