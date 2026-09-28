import PoincareConjecture.Definitions.M33EventPreservation
import PoincareConjecture.Definitions.Ch15.SurgeryEndPolicy

set_option autoImplicit false

universe u

namespace PoincareConjecture

private theorem cuts_of_literal_data
    {S0 S1 : GeneralizedSliceCarrier.{u}}
    {g0 : RiemannianMetric 3 S0.carrier}
    {g1 : RiemannianMetric 3 S1.carrier}
    {D0 : LeviCivitaData g0} {D1 : LeviCivitaData g1}
    {n0 n1 : Nat}
    {N0 : Fin n0 -> EpsilonNeck g0}
    {N1 : Fin n1 -> EpsilonNeck g1}
    {R0 : Set S0.carrier} {R1 : Set S1.carrier}
    (rho : Real)
    (hS : S1 = S0) (hg : HEq g1 g0) (hD : HEq D1 D0)
    (hn : n1 = n0) (hN : HEq N1 N0) (hR : HEq R1 R0)
    (h : exists cuts : forall i, SurgeryEndCut (N0 i),
      R0 = SurgeryTerminalCoreComponents D0 rho \
        (Set.iUnion fun i => (cuts i).tail)) :
    exists cuts : forall i, SurgeryEndCut (N1 i),
      R1 = SurgeryTerminalCoreComponents D1 rho \
        (Set.iUnion fun i => (cuts i).tail) := by
  cases hS
  have hg' : g1 = g0 := eq_of_heq hg
  subst g1
  have hD' : D1 = D0 := eq_of_heq hD
  subst D1
  cases hn
  have hN' : N1 = N0 := eq_of_heq hN
  subst N1
  have hR' : R1 = R0 := eq_of_heq hR
  subst R1
  exact h

theorem M33NonemptyEventDataPreservation.transportPolicy
    {g0 g1 : StandardInitialMetric} {K0 K1 : MetricSurgeryConstants}
    {P0 P1 : SurgeryParameters}
    {slice0 slice1 : Real -> GeneralizedSliceCarrier.{u}}
    {metric0 : forall t, RiemannianMetric 3 (slice0 t).carrier}
    {metric1 : forall t, RiemannianMetric 3 (slice1 t).carrier} {T : Real}
    {A : SurgeryEventData g0 K0 P0 slice0 metric0 T}
    {B : SurgeryEventData g1 K1 P1 slice1 metric1 T}
    (H : M33NonemptyEventDataPreservation A B) (hP : P1 = P0)
    (hA : Nonempty (SurgeryEventTerminalPolicy A)) :
    Nonempty (SurgeryEventTerminalPolicy B) := by
  obtain ⟨policy⟩ := hA
  obtain ⟨cuts, hcuts⟩ := cuts_of_literal_data
    (P0.delta T * P0.r T)
    H.terminal_eq H.limit_metric_heq H.limit_connection_heq
    H.cap_count_eq H.necks_heq H.retained_image_heq
    ⟨policy.cuts, policy.retained_eq⟩
  refine ⟨{ cuts := cuts, retained_eq := ?_ }⟩
  simpa only [hP] using hcuts

private theorem vanishing_margin_congr
    (C₀ C₁ : GeneralizedSliceCarrier.{u}) (a₀ a₁ T q : ℝ)
    (X₀ : RicciFlow 3 C₀.carrier (Set.Ico a₀ T))
    (X₁ : RicciFlow 3 C₁.carrier (Set.Ico a₁ T))
    (hC : C₁ = C₀) (ha : a₁ = a₀) (hX : HEq X₁ X₀)
    (h : ∀ x : C₀.carrier, ∃ L : ℝ, q < L ∧
      ∃ s ∈ Set.Ico a₀ T, ∀ t ∈ Set.Ico s T,
        L < (X₀.connection t).scalarCurvature x) :
    ∀ x : C₁.carrier, ∃ L : ℝ, q < L ∧
      ∃ s ∈ Set.Ico a₁ T, ∀ t ∈ Set.Ico s T,
        L < (X₁.connection t).scalarCurvature x := by
  subst C₁ a₁
  have hflow : X₁ = X₀ := eq_of_heq hX
  subst X₁
  exact h

theorem M33VanishingEventDataPreservation.transportPolicy
    {P₀ P₁ : SurgeryParameters} {slice₀ slice₁ : ℝ → GeneralizedSliceCarrier.{u}}
    {metric₀ : ∀ t, RiemannianMetric 3 (slice₀ t).carrier}
    {metric₁ : ∀ t, RiemannianMetric 3 (slice₁ t).carrier} {T : ℝ}
    {A : SurgeryVanishingEventData P₀ slice₀ metric₀ T}
    {B : SurgeryVanishingEventData P₁ slice₁ metric₁ T}
    (H : M33VanishingEventDataPreservation A B) (hP : P₁ = P₀)
    (policy : SurgeryVanishingEventTerminalPolicy A) :
    SurgeryVanishingEventTerminalPolicy B := by
  have h := vanishing_margin_congr (slice₀ A.tMinus) (slice₁ B.tMinus)
    A.tMinus B.tMinus T ((P₀.delta T * P₀.r T)⁻¹ ^ 2)
    A.pre_flow B.pre_flow H.pre_carrier_eq H.reference_eq H.pre_flow_heq policy
  simpa only [SurgeryVanishingEventTerminalPolicy, hP] using h

theorem M33OldEventDataPreservation.transportPolicy
    {F : SurgeryFlowData.{u}} {E : SurgeryFlowExtension F}
    (H : M33OldEventDataPreservation E) {J : Set Real}
    (hJ : J ⊆ F.time_domain) (policy : SurgeryFlowTerminalPolicyOn F J) :
    SurgeryFlowTerminalPolicyOn E.extended J := by
  classical
  constructor
  · intro T hTJ hT' hpost
    have hTF := hJ hTJ
    have hT := (E.old_surgery_times T hTF).mp hT'
    let : Nonempty (F.slice T).carrier :=
      ⟨(E.identify T hTF).symm (Classical.choice hpost)⟩
    exact (H.nonempty T hT hT').transportPolicy E.parameters_eq
      (policy.nonempty T hTJ hT)
  · intro T hTJ hT' hempty
    have hTF := hJ hTJ
    have hT := (E.old_surgery_times T hTF).mp hT'
    let : IsEmpty (F.slice T).carrier :=
      ⟨fun x => isEmptyElim (E.identify T hTF x)⟩
    exact (H.vanishing T hT hT').transportPolicy E.parameters_eq
      (policy.vanishing T hTJ hT)

end PoincareConjecture
