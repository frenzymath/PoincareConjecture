import PoincareConjecture.Definitions.M67InitialClass
import PoincareConjecture.Statements.M61Width
import PoincareConjecture.Statements.M65
import PoincareConjecture.Statements.M66



































set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


structure M67RegularPiece
    (hM61 : M61RawWidthCore.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b T : ℝ}
    (actual_flow : RicciFlow 3 M (Set.Icc a b))
    (global_width : Set.Icc (0 : ℝ) T → ℝ)
    (events : Set ℝ) where
  ordered : a < b
  inside : 0 ≤ a ∧ b ≤ T
  no_event : Disjoint events (Set.Ioc a b)
  input : M65RawFlowInput M a b
  input_flow_eq : input.flow = actual_flow
  class_data : M66ClassData input
  predecessors : M66Predecessors hM61 hM65 input class_data
  conclusion : M66Conclusion hM61 hM65 input class_data predecessors
  interval : Set.Icc a b → Set.Icc (0 : ℝ) T
  interval_time : ∀ s, (interval s).1 = s.1
  width_agreement : ∀ s,
    global_width (interval s) = m66Width input s

structure M67ChangingWidthPath
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (W : RepairedEventChildWitness D.flow)
    {T : ℝ} (P : RepairedComponentPath D.flow T W)
    (K : RepairedComparisonMapData D)
    (C : RepairedComparisonHomotopyData D K)
    (H : RepairedAncestryTransportInput D W P K C)
    (B : M59HigherBasepointTransportService)
    (A : RepairedAncestryTransportData D W P K C H B)
    (q : M59SphereQuotient)
    (hM61 : M61RawWidthCore.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64) where
  terminal_nonnegative : 0 ≤ T
  slice : ∀ s : Set.Icc (0 : ℝ) T,
    M67WidthSlice q (P.component s)
  ambient_metric_eq : ∀ s,
    (slice s).ambient_metric = D.flow.metric s.1


  regular_flow : ∀ {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T),
    Disjoint D.flow.surgery_times (Set.Ioc a b) →
      RicciFlow 3
        (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).carrier.carrier
        (Set.Icc a b)




  regular_flow_metric_calibration : ∀ {a b : ℝ}
      (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
      (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b))
      (s : Set.Icc a b) (x v w),
    ((regular_flow ha hab hb hJ).metric s.1).inner x v w =
      ((D.flow.regular_slabs a b hab
        (fun _u hu => P.time_subset
          ⟨ha.trans hu.1, hu.2.trans hb⟩) hJ).flow.metric s.1).inner
        ((P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).inclusion x)
        (mfderiv (𝓡 3) (𝓡 3)
          (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).inclusion x v)
        (mfderiv (𝓡 3) (𝓡 3)
          (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).inclusion x w)


  regular_flow_scalar_calibration : ∀ {a b : ℝ}
      (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
      (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b))
      (s : Set.Icc a b) (x),
    ((regular_flow ha hab hb hJ).connection s.1).scalarCurvature x =
      ((D.flow.regular_slabs a b hab
        (fun _u hu => P.time_subset
          ⟨ha.trans hu.1, hu.2.trans hb⟩) hJ).flow.connection s.1).scalarCurvature
        ((P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).inclusion x)
  width : Set.Icc (0 : ℝ) T → ℝ
  width_eq_based : ∀ s,
    width s = m61BasedClassWidth q (slice s).metric
      (P.component s).basepoint (slice s).alpha
  scalar_infimum : Set.Icc (0 : ℝ) T → ℝ
  scalar_infimum_eq : ∀ s,
    scalar_infimum s = sInf (Set.range (fun x : (P.component s).carrier.carrier =>
      (slice s).connection.scalarCurvature x))
  scalar_lower_bound : ∀ s,
    -6 / (1 + 4 * s.1) ≤ scalar_infimum s
  chronology : M67FiniteChronology
    (↑P.surgery_times : Set ℝ) 0 T

  regular_piece : ∀ {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T),
    ∀ hJ : Disjoint D.flow.surgery_times (Set.Ioc a b),
    Nonempty (M67RegularPiece (M :=
          (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).carrier.carrier)
        hM61 hM65 (actual_flow := regular_flow ha hab hb hJ) width
        D.flow.surgery_times (a := a) (b := b) (T := T))



  event_transport : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
      ∀ hdelta : D.flow.parameters.delta S.1 <
        repairedComparisonDeltaBound D.flow.local_constants,
      ∀ hh : D.flow.parameters.h S.1 <
        repairedComparisonHeightBound D.flow.local_constants,
      ∀ (eta : ℝ) (heta : 0 < eta),
        M67EventTransportFamily B A q S hS hpost hdelta hh eta heta

structure M67Conclusion
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65) where
  width_nonnegative : ∀ s, 0 ≤ X.width s
  forward_difference : ∀ s : Set.Icc (0 : ℝ) T,
    s.1 < T → ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
      ∀ t : Set.Icc (0 : ℝ) T, s.1 < t.1 → t.1 < s.1 + delta →
        (X.width t - X.width s) / (t.1 - s.1) ≤
          -2 * Real.pi - X.scalar_infimum s / 2 * X.width s + epsilon
  continuous_at_regular : ∀ s : Set.Icc (0 : ℝ) T,
    s.1 ∉ (↑P.surgery_times : Set ℝ) →
      ContinuousAt X.width s
  surgery_lower_limit : ∀ s : Set.Icc (0 : ℝ) T,
    s.1 ∈ (↑P.surgery_times : Set ℝ) → ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ t : Set.Icc (0 : ℝ) T,
          s.1 - delta < t.1 → t.1 < s.1 → X.width s ≤ X.width t + epsilon
  right_continuous_after_event : ∀ s : Set.Icc (0 : ℝ) T,
    s.1 ∈ (↑P.surgery_times : Set ℝ) → ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ t : Set.Icc (0 : ℝ) T,
          s.1 ≤ t.1 → t.1 < s.1 + delta → |X.width t - X.width s| < epsilon




structure M67ClassCoherence
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65) : Prop where
  regular_transport : ∀ {a b : ℝ}
      (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
      (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b)),
      M67AlphaTransport B
        (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).basepoint
        (P.component ⟨b, ⟨ha.trans hab.le, hb⟩⟩).basepoint
        (repairedDiffeomorphContinuousMap
          (P.regular_transport
            ⟨a, ⟨ha, hab.le.trans hb⟩⟩
            ⟨b, ⟨ha.trans hab.le, hb⟩⟩ hab hJ))
        (X.slice ⟨a, ⟨ha, hab.le.trans hb⟩⟩).alpha
        (X.slice ⟨b, ⟨ha.trans hab.le, hb⟩⟩).alpha
  event_transport : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
      ∀ hdelta : D.flow.parameters.delta S.1 <
        repairedComparisonDeltaBound D.flow.local_constants,
      ∀ hh : D.flow.parameters.h S.1 <
        repairedComparisonHeightBound D.flow.local_constants,
      ∀ (eta : ℝ) (heta : 0 < eta),
      ∀ s : Set.Icc (0 : ℝ) T,
        ∀ hnear : S.1 - (X.event_transport S hS hpost hdelta hh eta heta).delta < s.1,
        ∀ hbefore : s.1 < S.1,
        ∀ hafter : (D.flow.event S.1 hS).tMinus < s.1,
        ∀ hJ : Disjoint D.flow.surgery_times
          (Set.Ioc (D.flow.event S.1 hS).tMinus s.1),
        let E := (X.event_transport S hS hpost hdelta hh eta heta).transport
          s hnear hbefore hafter hJ
        And (HEq E.pre.alpha (X.slice s).alpha)
          (And (HEq E.post.alpha (X.slice S).alpha)
            (M59HigherBasepointTransport.map
              (B.transport 2) E.loop_basepoint_path.loop
              (surgeryHomotopyMap (n := 2) E.loop.map
                (E.loop.map_based (rfl :
                  E.f (P.component s).basepoint =
                    E.f (P.component s).basepoint)) E.pre.alpha) =
                E.post.alpha))



structure M67AnchoredConclusion
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow} {T : ℝ}
    {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    (S : M59IdentificationSystem.{u})
    {hM61 : M61RawWidthCore.{u}} {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    (initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0))
    (X : M67ChangingWidthPath D W P K C H B A S.quotient hM61 hM65) : Prop where
  estimate : M67Conclusion X
  class_coherence : M67ClassCoherence X
  initial_metric_eq : (X.slice (m67InitialTime P)).metric = initial.metric
  initial_class_eq : (X.slice (m67InitialTime P)).alpha = initial.alpha
  identification_eq : ∀ s,
    (X.slice s).loop_pi_three =
      (S.core (P.component s).compact (P.component s).connected
        (P.component s).basepoint (X.slice s).pi_two_trivial).pi_two_pi_three

def M67SurgeryWidthTheory : Prop :=
  ∀ {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (W : RepairedEventChildWitness D.flow)
    {T : ℝ} (P : RepairedComponentPath D.flow T W)
    (_hcomparison : M67EventComparisonBounds D.flow (Set.Icc 0 T))
    (_hscalar : M67ScalarLowerBound D.flow (Set.Icc 0 T))
    (K : RepairedComparisonMapData D)
    (C : RepairedComparisonHomotopyData D K)
    (H : RepairedAncestryTransportInput D W P K C)
    (B : M59HigherBasepointTransportService)
    (A : RepairedAncestryTransportData D W P K C H B)
    (S : M59IdentificationSystem.{u})
    (initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0))
    (hM61 : M61WidthTheory.{u} S.quotient)
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61.toM61RawWidthCore hM64)
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    (_hM66 : M66SmoothTimeTheory hM61.toM61RawWidthCore hM58 hM65),
    Nonempty {X : M67ChangingWidthPath D W P K C H B A S.quotient
        hM61.toM61RawWidthCore hM65 //
      M67AnchoredConclusion S initial X}

end PoincareConjecture
