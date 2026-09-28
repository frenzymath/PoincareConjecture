import PoincareConjecture.Definitions.M33BranchContinuation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure M33RegularHistoryWindow (F : SurgeryFlowData.{u}) where
  interval : Set ℝ
  interval_connected : interval.OrdConnected
  interval_nontrivial : interval.Nontrivial
  zero_mem : 0 ∈ interval
  time_subset : interval ⊆ F.time_domain
  slice_nonempty : ∀ t ∈ interval, Nonempty (F.slice t).carrier
  events_finite : (F.surgery_times ∩ interval).Finite

def m33RegularRegion (F : SurgeryFlowData.{u}) (t : ℝ) : Set (F.slice t).carrier :=
  {x | ∀ hT : t ∈ F.surgery_times,
    x ∈ interior (@SurgeryFlowData.event F t hT ⟨x⟩).retained_post}

structure M33RegularHistoryData {F : SurgeryFlowData.{u}}
    (W : M33RegularHistoryWindow F) where
  generalized : GeneralizedRicciFlowData.{u}
  interval_eq : generalized.interval = W.interval
  history : M33RegularHistoryRealization generalized F
  regular_range : ∀ t ht,
    Set.range (history.forward t ht) = m33RegularRegion F t
  scalar_pullback : ∀ t ht x,
    (F.connection t).scalarCurvature (history.forward t ht x) =
      (generalized.connection t).scalarCurvature x
  curvature_norm_pullback : ∀ t ht x,
    (F.connection t).curvatureTensorNorm (history.forward t ht x) =
      (generalized.connection t).curvatureTensorNorm x
  negative_part_pullback : ∀ t ht x,
    (F.connection t).negativeCurvaturePart (history.forward t ht x) =
      (generalized.connection t).negativeCurvaturePart x
  volume_image : ∀ t ht (U : Set (generalized.slice t).carrier),
    calibratedMetricVolume (F.metric t) (history.forward t ht '' U) =
      calibratedMetricVolume (generalized.metric t) U
  regular_distance : ∀ t ht, t ∉ F.surgery_times →
    ∀ x y : (generalized.slice t).carrier,
      (F.metric t).edist (history.forward t ht x) (history.forward t ht y) =
        (generalized.metric t).edist x y
  cylinders_to_surgery : ∀ (C : GeneralizedSliceCarrier.{u})
    (origin scale : ℝ) (J : Set ℝ) (U : Set C.carrier),
    J.OrdConnected → IsOpen U →
    ∀ htime : ∀ s ∈ J, origin + s / scale ∈ generalized.interval,
    ∀ e : GeneralizedFlowCylinder generalized C origin scale J U,
      ∃ d : SurgeryFlowCylinder F C origin scale J U,
        (∀ s hs x, x ∈ U → d.forward s hs x =
          history.forward (origin + s / scale) (htime s hs) (e.forward s hs x)) ∧
        (∀ s hs x, x ∈ U → ∀ v w : TangentSpace (𝓡 3) x,
          d.pullbackInner s hs x v w = e.pullbackInner s hs x v w)
  cylinders_from_surgery : ∀ (C : GeneralizedSliceCarrier.{u})
    (origin scale : ℝ) (J : Set ℝ) (U : Set C.carrier),
    IsOpen U →
    ∀ htime : ∀ s ∈ J, origin + s / scale ∈ generalized.interval,
    ∀ e : SurgeryFlowCylinder F C origin scale J U,
    (∀ s hs, e.forward s hs '' U ⊆ m33RegularRegion F (origin + s / scale)) →
      ∃ d : GeneralizedFlowCylinder generalized C origin scale J U,
        (∀ s hs x, x ∈ U →
          history.forward (origin + s / scale) (htime s hs) (d.forward s hs x) =
            e.forward s hs x) ∧
        (∀ s hs x, x ∈ U → ∀ v w : TangentSpace (𝓡 3) x,
          d.pullbackInner s hs x v w = e.pullbackInner s hs x v w)

end PoincareConjecture
