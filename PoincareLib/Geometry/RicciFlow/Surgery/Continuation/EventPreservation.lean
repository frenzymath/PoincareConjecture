import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Geometry

/-!
Adapted from Mapher `PoincareMT/Definitions/M33EventPreservation.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# Literal preservation of old surgery data

MT Definition 15.8, p. 362, attaches a new ordinary segment to the old
spacetime. These M33 output conditions retain exactly the old geometric
data needed to transport its terminal-event policy. They do not assert
policy, component history or a noncollapse estimate.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- The old terminal geometry is copied literally despite the changed
full slice and metric families indexing the rebuilt event. -/
structure M33NonemptyEventDataPreservation
    {g₀ g₁ : StandardInitialMetric} {K₀ K₁ : MetricSurgeryConstants}
    {P₀ P₁ : SurgeryParameters} {slice₀ slice₁ : ℝ → GeneralizedSliceCarrier.{u}}
    {metric₀ : ∀ t, RiemannianMetric 3 (slice₀ t).carrier}
    {metric₁ : ∀ t, RiemannianMetric 3 (slice₁ t).carrier} {T : ℝ}
    (A : SurgeryEventData g₀ K₀ P₀ slice₀ metric₀ T)
    (B : SurgeryEventData g₁ K₁ P₁ slice₁ metric₁ T) : Prop where
  terminal_eq : B.terminal = A.terminal
  limit_metric_heq : HEq B.limit_metric A.limit_metric
  limit_connection_heq : HEq B.limit_connection A.limit_connection
  cap_count_eq : B.cap_count = A.cap_count
  necks_heq : HEq (fun i : Fin B.cap_count => (B.necks i).neck)
    (fun i : Fin A.cap_count => (A.necks i).neck)
  retained_image_heq : HEq (B.limit_identify.map '' B.retained_pre)
    (A.limit_identify.map '' A.retained_pre)

/-- Literal pre-flow preservation transports the strict pointwise scalar
margin of an old vanishing event. -/
structure M33VanishingEventDataPreservation
    {P₀ P₁ : SurgeryParameters} {slice₀ slice₁ : ℝ → GeneralizedSliceCarrier.{u}}
    {metric₀ : ∀ t, RiemannianMetric 3 (slice₀ t).carrier}
    {metric₁ : ∀ t, RiemannianMetric 3 (slice₁ t).carrier} {T : ℝ}
    (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    (B : SurgeryVanishingEventData P₁ slice₁ metric₁ T) : Prop where
  reference_eq : B.tMinus = A.tMinus
  pre_carrier_eq : slice₁ B.tMinus = slice₀ A.tMinus
  pre_flow_heq : HEq B.pre_flow A.pre_flow

/-- Extra output of the M33 construction, indexed by its actual extension.
No condition is imposed on the policy of the input flow's events. -/
structure M33OldEventDataPreservation
    {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F) : Prop where
  nonempty : ∀ T hT [Nonempty (F.slice T).carrier]
    [Nonempty (E.extended.slice T).carrier], ∀ hT' : T ∈ E.extended.surgery_times,
      M33NonemptyEventDataPreservation (F.event T hT) (E.extended.event T hT')
  vanishing : ∀ T hT [IsEmpty (F.slice T).carrier]
    [IsEmpty (E.extended.slice T).carrier], ∀ hT' : T ∈ E.extended.surgery_times,
      M33VanishingEventDataPreservation
        (F.vanishing_event T hT) (E.extended.vanishing_event T hT')

end PoincareMT
