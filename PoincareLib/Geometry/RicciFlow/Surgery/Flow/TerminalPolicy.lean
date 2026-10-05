import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic

/-!
Adapted from Mapher `PoincareMT/Definitions/Ch15/SurgeryEndPolicy.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# Terminal policy for constructed surgeries

These are outputs of M33's Definition 15.8 construction (MT, pp. 361-362).
The raw flow class does not assert this policy for arbitrary earlier events.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

/-- The terminal components meeting the actual scalar sublevel set Omega_rho. -/
def SurgeryTerminalCoreComponents {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (rho : ℝ) : Set M :=
  {x | ∃ y, D.scalarCurvature y ≤ rho⁻¹ ^ 2 ∧ x ∈ connectedComponent y}

/-- The proper ambient end beyond a selected neck sphere. Its identification
from the selected horn is part of M33's construction, not a raw event premise. -/
structure SurgeryEndCut {g : RiemannianMetric 3 M} (N : EpsilonNeck g) where
  point : M
  point_positive : point ∈ N.region 0 N.epsilon⁻¹
  tail : Set M
  component_eq : tail = connectedComponentIn N.central_sphereᶜ point
  frontier_eq : frontier tail = N.central_sphere
  escapes_compact : ∀ K : Set M, IsCompact K → ¬ tail ⊆ K
  positive_subset : N.region 0 N.epsilon⁻¹ ⊆ tail
  negative_disjoint : Disjoint (N.region (-N.epsilon⁻¹) 0) tail

/-- The continuing terminal region is exactly Omega_big with the chosen
unbounded ends removed, using the actual event metric, necks and parameters. -/
structure SurgeryEventTerminalPolicy
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T) where
  cuts : ∀ i : Fin E.cap_count, SurgeryEndCut (E.necks i).neck
  retained_eq : E.limit_identify.map '' E.retained_pre =
    SurgeryTerminalCoreComponents E.limit_connection (P.delta T * P.r T) \
      ⋃ i, (cuts i).tail

/-- At every pre-flow point of a constructed vanishing event the scalar
curvature eventually exceeds a pointwise strict margin above rho^-2. -/
def SurgeryVanishingEventTerminalPolicy
    {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (V : SurgeryVanishingEventData P slice metric T) : Prop :=
  ∀ x : (slice V.tMinus).carrier,
    ∃ L : ℝ, (P.delta T * P.r T)⁻¹ ^ 2 < L ∧
      ∃ s ∈ Set.Ico V.tMinus T,
        ∀ t ∈ Set.Ico s T, L < (V.pre_flow.connection t).scalarCurvature x

/-! The raw `SurgeryFlowData` deliberately remains broad. The following
predicate is the source-faithful policy boundary used when an induction
argument is restricted to the Definition 15.8 construction. Its interval is
explicit so an observation need not claim policy for an unobserved future.
The nonempty branch carries the data-bearing policy through `Nonempty`; the
vanishing branch is already a proposition. -/

/-- Every surgery event in `J` carries the terminal policy produced by the
Definition 15.8 construction, including the strict vanishing policy for
empty terminal slices. This is a restriction on a given flow, not a theorem
that creates policy for arbitrary raw events. -/
structure SurgeryFlowTerminalPolicyOn
    (F : SurgeryFlowData.{u}) (J : Set ℝ) : Prop where
  nonempty : ∀ T ∈ J, ∀ hT : T ∈ F.surgery_times,
    ∀ [_hT_nonempty : Nonempty (F.slice T).carrier],
      Nonempty (SurgeryEventTerminalPolicy (F.event T hT))
  vanishing : ∀ T ∈ J, ∀ hT : T ∈ F.surgery_times,
    ∀ [_hT_empty : IsEmpty (F.slice T).carrier],
      SurgeryVanishingEventTerminalPolicy (F.vanishing_event T hT)

/-- Restrict a terminal-policy certificate to a smaller observed interval. -/
theorem SurgeryFlowTerminalPolicyOn.restrict
    {F : SurgeryFlowData.{u}} {J K : Set ℝ}
    (hJK : J ⊆ K) (policy : SurgeryFlowTerminalPolicyOn F K) :
    SurgeryFlowTerminalPolicyOn F J :=
  { nonempty := fun T hT hTsurgery => policy.nonempty T (hJK hT) hTsurgery
    vanishing := fun T hT hTsurgery => policy.vanishing T (hJK hT) hTsurgery }

end PoincareMT
