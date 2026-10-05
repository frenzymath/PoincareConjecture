import PoincareLib.Geometry.RicciFlow.Surgery.Control.Basic

/-!
Adapted from Mapher `PoincareMT/Definitions/M49VolumeLoss.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M49 repaired surgery volume-loss data

Selected losses are lower bounds on the terminal volume decrease. Genuine
cap/neck events have positive loss; deletion-only events may use zero. The
M49 control boundary also records the event-history/domain facts needed for
the left limit and the zero-cap component alternative.
Vanishing events have empty post-volume without an imposed value for their
left-limit volume. Both the selected losses and the uniform observed count
use the actual raw flow, without equality to a selected M36 operation record.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-! The two pre-interval predicates follow from the raw flow's order-connected
domain and event times; M51's EventIntervals helpers supply them. The zero-cap
discarded-component predicate remains a separate geometric obligation. -/
def RepairedNonemptyEventPreInterval (F : SurgeryFlowData.{u}) : Prop :=
  ∀ (T : ℝ) (hT : T ∈ F.surgery_times),
    ∀ [Nonempty (F.slice T).carrier],
      Set.Ico (F.event T hT).tMinus T ⊆ F.time_domain

def RepairedVanishingEventPreInterval (F : SurgeryFlowData.{u}) : Prop :=
  ∀ (T : ℝ) (hT : T ∈ F.surgery_times),
    ∀ [IsEmpty (F.slice T).carrier],
      Set.Ico (F.vanishing_event T hT).tMinus T ⊆ F.time_domain

def RepairedZeroCapDiscard (F : SurgeryFlowData.{u}) : Prop :=
  ∀ (T : ℝ) (hT : T ∈ F.surgery_times),
    ∀ [Nonempty (F.slice T).carrier],
      (F.event T hT).cap_count = 0 →
        ∃ x : (F.slice (F.event T hT).tMinus).carrier,
          connectedComponent x ⊆ (F.event T hT).retained_preᶜ ∧
          0 < calibratedMetricVolume
            ((F.event T hT).pre_flow.metric (F.event T hT).tMinus)
            (connectedComponent x)

structure RepairedVolumeLossControls
    (F : SurgeryFlowData.{u}) : Prop where
  admissible : SurgeryFlowAdmissible F
  pinched : SurgeryFlowPinched F
  nonempty_pre_interval : RepairedNonemptyEventPreInterval F
  vanishing_pre_interval : RepairedVanishingEventPreInterval F
  zero_cap_discard : RepairedZeroCapDiscard F

/-- The pinching and actual event geometry used in Lemma 17.12, restricted
to the observed interval. The other seven surgery assumptions, including
normalized initial data, are fields of the same raw `F`. -/
structure RepairedObservedVolumeControls
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F) : Prop where
  pinched : ∀ t ∈ surgeryObservationInterval O,
    SurgeryPinchedAt (F.connection t) t
  strong_boundaries : ∀ (T : ℝ) (hT : T ∈ F.surgery_times),
    T ∈ surgeryObservationInterval O →
    ∀ [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count),
      Nonempty (SurgeryTerminalStrongNeck F T hT i)
  strong_disappearing : ∀ (T : ℝ) (hT : T ∈ F.surgery_times),
    T ∈ surgeryObservationInterval O →
    ∀ [Nonempty (F.slice T).carrier],
      ∀ t : Set.Ico (F.event T hT).tMinus T,
        (F.event T hT).disappearing_start ≤ t.1 →
        ∀ x : (F.slice (F.event T hT).tMinus).carrier,
          x ∉ interior (F.event T hT).retained_pre →
          SurgeryCanonicalControl F t.1 ((F.event T hT).pre_identify t x)
            F.parameters.epsilon F.parameters.C
  strong_vanishing : ∀ (T : ℝ) (hT : T ∈ F.surgery_times),
    T ∈ surgeryObservationInterval O →
    ∀ [IsEmpty (F.slice T).carrier],
      ∀ t : Set.Ico (F.vanishing_event T hT).tMinus T,
        (F.vanishing_event T hT).disappearing_start ≤ t.1 →
        ∀ x : (F.slice (F.vanishing_event T hT).tMinus).carrier,
          SurgeryCanonicalControl F t.1 ((F.vanishing_event T hT).pre_identify t x)
            F.parameters.epsilon F.parameters.C
  nonempty_pre_interval : RepairedNonemptyEventPreInterval F
  vanishing_pre_interval : RepairedVanishingEventPreInterval F
  zero_cap_discard : RepairedZeroCapDiscard F

structure RepairedSurgeryEventLossData
    (F : SurgeryFlowData.{u})
    (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] where
  loss : ℝ≥0∞
  /-- The scalar limit of the total pre-surgery volume need not equal the
      volume of the regular-limit manifold. Exhaustion gives the inequality
      below, which connects the actual terminal metric to volume evolution. -/
  left_limit_volume : ℝ≥0∞
  left_limit_volume_ne_top : left_limit_volume ≠ ⊤
  left_limit_volume_tendsto :
    Filter.Tendsto (fun t => calibratedMetricVolume (F.metric t) Set.univ)
      (nhdsWithin T (F.time_domain ∩ Set.Iio T)) (𝓝 left_limit_volume)
  regular_limit_volume_le_left_limit :
    calibratedMetricVolume (F.event T hT).limit_metric Set.univ ≤
      left_limit_volume
  retained_volume_transport :
    calibratedMetricVolume (F.metric T)
        (F.event T hT).retained_post =
      calibratedMetricVolume
        (F.event T hT).limit_metric
          ((F.event T hT).limit_identify.map ''
            (F.event T hT).retained_pre)
  terminal_volume_drop :
    calibratedMetricVolume (F.metric T) Set.univ + loss ≤
      calibratedMetricVolume (F.event T hT).limit_metric Set.univ
  /-- Zero is a chosen lower bound for a deletion-only event, not a claim
      that its actual terminal volume decrease is zero. The discarded neck
      region is the positive half, as in Lemma 17.12, p. 410. -/
  event_case :
    (∃ i : Fin (F.event T hT).cap_count,
      0 < loss ∧
      calibratedMetricVolume (F.metric T)
          ((F.event T hT).caps i).carrier + loss ≤
        calibratedMetricVolume (F.event T hT).limit_metric
          (((F.event T hT).necks i).neck.region 0
            ((F.event T hT).necks i).neck.epsilon⁻¹)) ∨
    ((F.event T hT).cap_count = 0 ∧ loss = 0 ∧
      ∃ x : (F.slice (F.event T hT).tMinus).carrier,
      connectedComponent x ⊆ (F.event T hT).retained_preᶜ ∧
      0 < calibratedMetricVolume
        ((F.event T hT).pre_flow.metric (F.event T hT).tMinus)
        (connectedComponent x))

structure RepairedVanishingVolumeData
    (F : SurgeryFlowData.{u})
    (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier] where
  post_volume_zero : calibratedMetricVolume (F.metric T) Set.univ = 0
  volume_drop : calibratedMetricVolume (F.metric T) Set.univ ≤
    (F.vanishing_event T hT).left_limit_volume

structure RepairedVolumeLossData
    (F : SurgeryFlowData.{u})
    (C : RepairedVolumeLossControls F) where
  initial_volume_ne_top : calibratedMetricVolume (F.metric 0) Set.univ ≠ ⊤
  event_loss : ∀ (T : ℝ) (hT : T ∈ F.surgery_times),
    ∀ [Nonempty (F.slice T).carrier],
      RepairedSurgeryEventLossData F T hT
  vanishing_volume : ∀ (T : ℝ) (hT : T ∈ F.surgery_times),
    ∀ [IsEmpty (F.slice T).carrier],
      RepairedVanishingVolumeData F T hT
  /-- Weighted volume is nonincreasing across regular evolution and surgery.
      This is a produced M49 estimate, not an assumption on the raw flow. -/
  volume_growth : ∀ a b : ℝ,
    a ∈ F.time_domain → b ∈ F.time_domain → a ≤ b →
      calibratedMetricVolume (F.metric b) Set.univ ≤
        ENNReal.ofReal (Real.exp (6 * (b - a))) *
          calibratedMetricVolume (F.metric a) Set.univ
  /-- Positive dimensional constant in the corrected cap/neck loss estimate.
      It is supplied by the certificate, rather than imposed as an arbitrary
      universally quantified control parameter. -/
  loss_scale_factor : ℝ
  loss_scale_factor_pos : 0 < loss_scale_factor
  /-- The corrected `h^3 / delta` estimate applies to horn/2-sphere events.
      Component-discard events use the explicit positive component witness
      above and therefore are not forced into this uniform scale estimate. -/
  horn_loss_lower_bound : ∀ H : ℝ, 0 ≤ H →
    ∃ sigma : ℝ, 0 < sigma ∧
      ∀ (T : ℝ) (hT : T ∈ F.surgery_times), T ∈ Set.Icc 0 H →
        ∀ [Nonempty (F.slice T).carrier],
          0 < (F.event T hT).cap_count →
            ENNReal.ofReal sigma ≤ (event_loss T hT).loss ∧
              ENNReal.ofReal
                  (loss_scale_factor *
                    (F.parameters.h T ^ 3 / F.parameters.delta T)) ≤
                (event_loss T hT).loss
  /-- A separate finite bound records deletion-only events, whose terminal
      volume loss may be zero. -/
  component_event_count_bound : ∀ H : ℝ, 0 ≤ H →
    ∃ n : ℕ, ∀ S : Finset ℝ,
      (↑S : Set ℝ) ⊆ {T ∈ F.surgery_times ∩ Set.Icc 0 H |
        ∃ hT : T ∈ F.surgery_times,
          IsEmpty (F.slice T).carrier ∨
            ∃ hN : Nonempty (F.slice T).carrier,
              letI := hN
              (F.event T hT).cap_count = 0} →
      S.card ≤ n

end PoincareMT
