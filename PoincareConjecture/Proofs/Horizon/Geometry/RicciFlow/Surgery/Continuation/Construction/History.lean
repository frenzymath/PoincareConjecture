import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Cylinders.FromSurgery
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Cylinders.ToSurgery

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Surgery.RegularHistory

variable {F : SurgeryFlowData.{u}} (W : M33RegularHistoryWindow F)
  (L : ∀ t, t ∈ F.surgery_times → t ∈ W.interval →
    RicciFlowLocalTheory 3 (F.slice t).carrier)

def data : M33RegularHistoryData W where
  generalized := generalized W L
  interval_eq := rfl
  history := realization W L
  regular_range := regular_range W
  scalar_pullback t _ := scalar_pullback W t
  curvature_norm_pullback t _ := curvature_norm_pullback W t
  negative_part_pullback t _ := negative_part_pullback W t
  volume_image t _ := volume_image W t
  regular_distance := regular_distance W
  cylinders_to_surgery _C _origin _scale _J _U hJ hU htime e :=
    (realization W L).cylinders_to_surgery W rfl e hJ htime (regular_range W) hU
  cylinders_from_surgery _C _origin _scale _J _U hU htime e hguard :=
    cylinders_from_surgery W L e htime hguard hU

end PoincareConjecture.Surgery.RegularHistory
