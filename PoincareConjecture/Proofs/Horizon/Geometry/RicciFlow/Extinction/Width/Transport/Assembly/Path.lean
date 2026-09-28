import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Regular.Agreement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Chronology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Slice.Metric

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

noncomputable def m67ChangingWidthPathOfSlices
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (W : RepairedEventChildWitness D.flow) {T : ℝ}
    (P : RepairedComponentPath D.flow T W)
    (K : RepairedComparisonMapData D) (C : RepairedComparisonHomotopyData D K)
    (H : RepairedAncestryTransportInput D W P K C)
    (B : M59HigherBasepointTransportService.{u})
    (A : RepairedAncestryTransportData D W P K C H B)
    (S : M59IdentificationSystem.{u}) (hM61 : M61WidthTheory.{u} S.quotient)
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61.toM61RawWidthCore hM64)
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    (hM66 : M66SmoothTimeTheory hM61.toM61RawWidthCore hM58 hM65)
    (hscalar : M67ScalarLowerBound D.flow (Set.Icc 0 T))
    (slice : ∀ s, M67WidthSlice S.quotient (P.component s))
    (hambient : ∀ s, (slice s).ambient_metric = D.flow.metric s.1)
    (hclass : ∀ (a b : Set.Icc (0 : ℝ) T) (hab : a.1 < b.1)
      (hJ : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1)),
      M67AlphaTransport B (P.component a).basepoint (P.component b).basepoint
        (repairedDiffeomorphContinuousMap (P.regular_transport a b hab hJ))
        (slice a).alpha (slice b).alpha)
    (events : ∀ (t : Set.Icc (0 : ℝ) T) (ht : t.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice t.1).carrier)
      (hd : D.flow.parameters.delta t.1 < repairedComparisonDeltaBound D.flow.local_constants)
      (hh : D.flow.parameters.h t.1 < repairedComparisonHeightBound D.flow.local_constants)
      (eta : ℝ) (heta : 0 < eta),
      M67EventTransportFamily B A S.quotient t ht hpost hd hh eta heta) :
    M67ChangingWidthPath D W P K C H B A S.quotient hM61.toM61RawWidthCore hM65 where
  terminal_nonnegative := D.flow.time_domain_nonnegative P.terminal_mem
  slice := slice
  ambient_metric_eq := hambient
  regular_flow := repairedRegularFlow D P
  regular_flow_metric_calibration := repairedRegularFlow_metric D P
  regular_flow_scalar_calibration := repairedRegularFlow_scalarCurvature D P
  width := fun s => m61BasedClassWidth S.quotient (slice s).metric
    (P.component s).basepoint (slice s).alpha
  width_eq_based := fun _ => rfl
  scalar_infimum := fun s => sInf (Set.range (slice s).connection.scalarCurvature)
  scalar_infimum_eq := fun _ => rfl
  scalar_lower_bound := by
    intro s
    apply le_csInf (show (Set.range (slice s).connection.scalarCurvature).Nonempty from
      ⟨_, (P.component s).basepoint, rfl⟩)
    rintro _ ⟨x, rfl⟩
    have heq := (slice s).connection.scalarCurvature_eq_of_local_isometry
      (D.flow.connection s.1) isOpen_univ (P.component s).inclusion_smooth.contMDiffOn
      (fun y _ v w => ?_) (Set.mem_univ x)
    · rw [heq]
      exact hscalar s.1 s.2 (P.time_subset s.2) _
    · rw [← hambient s]
      exact ((slice s).metric_pullback y v w).symm
  chronology := repairedComponentPathChronology (g₀ := g₀) P
  regular_piece := by
    intro a b ha hab hb hJ
    exact m67_regular_piece_of_actual_slice
      (P.component ⟨a, ha, hab.le.trans hb⟩) S (slice ⟨a, ha, hab.le.trans hb⟩)
      hM61.toM61RawWidthCore hM65 hM58 hM66 (repairedRegularFlow D P ha hab hb hJ)
      _ D.flow.surgery_times ha hab hb hJ
      (m67_regular_width_agreement D P S B hM61 slice hambient hclass ha hab hb hJ)
  event_transport := events

end PoincareConjecture
