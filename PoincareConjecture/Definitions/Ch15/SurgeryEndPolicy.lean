import PoincareConjecture.Definitions.Ch15.SurgeryFlow

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

def SurgeryTerminalCoreComponents {g : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (rho : ℝ) : Set M :=
  {x | ∃ y, D.scalarCurvature y ≤ rho⁻¹ ^ 2 ∧ x ∈ connectedComponent y}

structure SurgeryEndCut {g : RiemannianMetric 3 M} (N : EpsilonNeck g) where
  point : M
  point_positive : point ∈ N.region 0 N.epsilon⁻¹
  tail : Set M
  component_eq : tail = connectedComponentIn N.central_sphereᶜ point
  frontier_eq : frontier tail = N.central_sphere
  escapes_compact : ∀ K : Set M, IsCompact K → ¬ tail ⊆ K
  positive_subset : N.region 0 N.epsilon⁻¹ ⊆ tail
  negative_disjoint : Disjoint (N.region (-N.epsilon⁻¹) 0) tail

structure SurgeryEventTerminalPolicy
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T) where
  cuts : ∀ i : Fin E.cap_count, SurgeryEndCut (E.necks i).neck
  retained_eq : E.limit_identify.map '' E.retained_pre =
    SurgeryTerminalCoreComponents E.limit_connection (P.delta T * P.r T) \
      ⋃ i, (cuts i).tail

def SurgeryVanishingEventTerminalPolicy
    {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (V : SurgeryVanishingEventData P slice metric T) : Prop :=
  ∀ x : (slice V.tMinus).carrier,
    ∃ L : ℝ, (P.delta T * P.r T)⁻¹ ^ 2 < L ∧
      ∃ s ∈ Set.Ico V.tMinus T,
        ∀ t ∈ Set.Ico s T, L < (V.pre_flow.connection t).scalarCurvature x

structure SurgeryFlowTerminalPolicyOn
    (F : SurgeryFlowData.{u}) (J : Set ℝ) : Prop where
  nonempty : ∀ T ∈ J, ∀ hT : T ∈ F.surgery_times,
    ∀ [_hT_nonempty : Nonempty (F.slice T).carrier],
      Nonempty (SurgeryEventTerminalPolicy (F.event T hT))
  vanishing : ∀ T ∈ J, ∀ hT : T ∈ F.surgery_times,
    ∀ [_hT_empty : IsEmpty (F.slice T).carrier],
      SurgeryVanishingEventTerminalPolicy (F.vanishing_event T hT)

theorem SurgeryFlowTerminalPolicyOn.restrict
    {F : SurgeryFlowData.{u}} {J K : Set ℝ}
    (hJK : J ⊆ K) (policy : SurgeryFlowTerminalPolicyOn F K) :
    SurgeryFlowTerminalPolicyOn F J :=
  { nonempty := fun T hT hTsurgery => policy.nonempty T (hJK hT) hTsurgery
    vanishing := fun T hT hTsurgery => policy.vanishing T (hJK hT) hTsurgery }

end PoincareConjecture
