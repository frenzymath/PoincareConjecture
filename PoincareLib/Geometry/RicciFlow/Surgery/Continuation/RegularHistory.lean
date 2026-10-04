import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Branch

/-!
Adapted from Mapher `PoincareMT/Definitions/M33RegularHistory.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# The actual regular part of a finite surgery history

Morgan--Tian Lemma 14.11 and Proposition 14.12, pp. 349-350. The input
window is primitive data on the actual surgery flow. The generalized flow,
its exact regular-slice images and both cylinder transports are outputs.
No canonical, analytic or noncollapsing estimate is assumed or produced.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Primitive observation guards. The interval may have an excluded endpoint;
finiteness concerns only its included old surgery times. -/
structure M33RegularHistoryWindow (F : SurgeryFlowData.{u}) where
  interval : Set ℝ
  interval_connected : interval.OrdConnected
  interval_nontrivial : interval.Nontrivial
  zero_mem : 0 ∈ interval
  time_subset : interval ⊆ F.time_domain
  slice_nonempty : ∀ t ∈ interval, Nonempty (F.slice t).carrier
  events_finite : (F.surgery_times ∩ interval).Finite

/-- At an old surgery retain precisely its continuing interior. The point
itself supplies nonemptiness for the event; at other times the set is univ. -/
def m33RegularRegion (F : SurgeryFlowData.{u}) (t : ℝ) : Set (F.slice t).carrier :=
  {x | ∀ hT : t ∈ F.surgery_times,
    x ∈ interior (@SurgeryFlowData.event F t hT ⟨x⟩).retained_post}

/-- The maximal regular generalized subset on the specified window. All
identifications concern this one selected flow and the actual historical
maps. Metric statements about cylinders are restricted to their open U. -/
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

end PoincareMT
