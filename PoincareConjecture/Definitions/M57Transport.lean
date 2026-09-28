import PoincareConjecture.Definitions.M40ComparisonHomotopy
import PoincareConjecture.Definitions.M56Ancestry
import PoincareConjecture.Definitions.M59BasepointTransport













set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

noncomputable def repairedDiffeomorphContinuousMap
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) A]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) B]
    [IsManifold (𝓡 3) ∞ A] [IsManifold (𝓡 3) ∞ B]
    (f : Diffeomorph (𝓡 3) (𝓡 3) A B ∞) : ContinuousMap A B :=
  ⟨f, f.continuous⟩








structure RepairedAncestryTransportInput
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (W : RepairedEventChildWitness D.flow)
    {T : ℝ} (P : RepairedComponentPath D.flow T W)
    (K : RepairedComparisonMapData D)
    (C : RepairedComparisonHomotopyData D K) where
  event_input : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    RepairedComparisonHomotopyInput D S.1 hS
  event_parent_path : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    HEq (event_input S hS hpost).parent
      (P.component ⟨(D.flow.event S.1 hS).tMinus,
        ⟨(D.flow.event S.1 hS).tMinus_nonnegative,
          (D.flow.event S.1 hS).tMinus_lt.le.trans S.2.2⟩⟩)
  event_child_path : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    HEq (event_input S hS hpost).child
      (P.component ⟨S.1, ⟨S.2.1, S.2.2⟩⟩)
  event_topology_path : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    (event_input S hS hpost).topology.conclusion = W.topology S.1 hS hpost
  event_survivor_region_path : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    (W.topology S.1 hS hpost).survivor_region
      (P.event_survivor_index S hS hpost) =
      Set.range (P.component S).inclusion
  event_child_range : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    Set.range (event_input S hS hpost).child.inclusion =
      Set.range (P.component S).inclusion
  event_parent_basepoint_path : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    HEq (event_input S hS hpost).parent.basepoint
      (P.component ⟨(D.flow.event S.1 hS).tMinus,
        ⟨(D.flow.event S.1 hS).tMinus_nonnegative,
          (D.flow.event S.1 hS).tMinus_lt.le.trans S.2.2⟩⟩).basepoint
  event_child_basepoint_path : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    HEq (event_input S hS hpost).child.basepoint
      (P.component S).basepoint
  event_target_basepoint_bridge : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    ∀ hdelta : D.flow.parameters.delta S.1 <
        repairedComparisonDeltaBound D.flow.local_constants,
      ∀ hh : D.flow.parameters.h S.1 <
        repairedComparisonHeightBound D.flow.local_constants,
      ∃ y : (P.component S).carrier.carrier,
        HEq y (Classical.choice (C.transport S.1 hS
          (event_input S hS hpost) hdelta hh)).val.comparison.target_basepoint ∧
        Nonempty (Path y (P.component S).basepoint)
  regular_basepoint_bridge : ∀ (a b : Set.Icc (0 : ℝ) T)
      (hab : a.1 < b.1)
      (hdisjoint : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1)),
    Nonempty (Path
      (repairedDiffeomorphContinuousMap (P.regular_transport a b hab hdisjoint)
        (P.component a).basepoint)
      (P.component b).basepoint)






structure RepairedAncestryTransportData
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (W : RepairedEventChildWitness D.flow)
    {T : ℝ} (P : RepairedComponentPath D.flow T W)
    (K : RepairedComparisonMapData D)
    (C : RepairedComparisonHomotopyData D K)
    (H : RepairedAncestryTransportInput D W P K C)
    (B : M59HigherBasepointTransportService) where
  event_output : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    ∀ _hdelta : D.flow.parameters.delta S.1 <
        repairedComparisonDeltaBound D.flow.local_constants,
      ∀ _hh : D.flow.parameters.h S.1 <
        repairedComparisonHeightBound D.flow.local_constants,
      RepairedComparisonHomotopyConclusion
        (H.event_input S hS hpost)
  event_output_eq_provider : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    ∀ hdelta : D.flow.parameters.delta S.1 <
        repairedComparisonDeltaBound D.flow.local_constants,
      ∀ hh : D.flow.parameters.h S.1 <
        repairedComparisonHeightBound D.flow.local_constants,
      event_output S hS hpost hdelta hh =
        (Classical.choice (C.transport S.1 hS
          (H.event_input S hS hpost) hdelta hh)).val
  event_nonzero_transport : ∀ (S : Set.Icc (0 : ℝ) T)
      (hS : S.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice S.1).carrier),
    letI := hpost
    ∀ hdelta : D.flow.parameters.delta S.1 <
        repairedComparisonDeltaBound D.flow.local_constants,
      ∀ hh : D.flow.parameters.h S.1 <
        repairedComparisonHeightBound D.flow.local_constants,
      ∀ alpha : HomotopyGroup.Pi 3
          (H.event_input S hS hpost).parent.carrier.carrier
          (H.event_input S hS hpost).parent.basepoint,
        alpha ≠ 1 →
        surgeryHomotopyMap (n := 3)
          (event_output S hS hpost hdelta hh).comparison.map
          (event_output S hS hpost hdelta hh).comparison.based alpha ≠ 1
  regular_nonzero_transport : ∀ (a b : Set.Icc (0 : ℝ) T)
      (hab : a.1 < b.1)
      (hdisjoint : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1)),
    ∀ alpha : HomotopyGroup.Pi 3
        (P.component a).carrier.carrier (P.component a).basepoint,
      alpha ≠ 1 →
      ∀ y : (P.component b).carrier.carrier,
        ∀ p : Path (repairedDiffeomorphContinuousMap
            (P.regular_transport a b hab hdisjoint)
            (P.component a).basepoint) y,
          M59HigherBasepointTransport.map (B.transport 3) p
            (surgeryHomotopyMap (n := 3)
              (repairedDiffeomorphContinuousMap
                (P.regular_transport a b hab hdisjoint)) (rfl :
                  repairedDiffeomorphContinuousMap
                    (P.regular_transport a b hab hdisjoint)
                    (P.component a).basepoint =
                  repairedDiffeomorphContinuousMap
                    (P.regular_transport a b hab hdisjoint)
                    (P.component a).basepoint) alpha) ≠ 1

end PoincareConjecture
