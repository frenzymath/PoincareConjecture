import PoincareConjecture.Proofs.M47.TerminalCommonIntervalStopped
import PoincareConjecture.Proofs.M47.BlowupControlsSourceSearch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem terminalCommonInterval_search_window
    {C : MetricSurgeryConstants} (p : SurgeryParameterPrefix C)
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F) {base Q T : ℝ}
    (hbase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hT : 0 ≤ T) (hQ : 64 * (T + 1) ≤ Q) :
    Icc (base - T / Q) base ⊆ F.time_domain := by
  have hQpos : 0 < Q := by linarith
  have hshort : T / Q ≤ 1 / 64 := (div_le_iff₀ hQpos).mpr (by linarith)
  have hepoch : 1 / 32 ≤ surgeryEpochStart p.i :=
    div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (by norm_num)
  intro s hs
  exact O.interval_subset ⟨by linarith [hbase.1, hs.1], hs.2.trans_lt hbase.2⟩

private theorem scalar_eq_of_heq {F : SurgeryFlowData.{u}} {s t : ℝ}
    {x : (F.slice s).carrier} {y : (F.slice t).carrier} (hst : s = t) (hxy : HEq x y) :
    (F.connection s).scalarCurvature x = (F.connection t).scalarCurvature y := by
  cases hst
  cases hxy
  rfl

theorem terminalCommonInterval_exists_bounded_search
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    {K : ℝ} (hK : 1 ≤ K) (p : SurgeryParameterPrefix S.constants)
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    (hInitial : F.standard_initial = S.setup.standard_initial)
    (hConstants : F.local_constants = S.constants) (hC : F.parameters.C = S.setup.C)
    {base Q r eta : ℝ} (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hScale : 64 * (2 * terminalCommonIntervalDuration S B K + 1) ≤ Q)
    (hLarge : B.curvature_threshold ≤ Q) (hThreshold : r⁻¹ ^ 2 ≤ Q)
    (hPinched : SurgeryFlowPinched F)
    (hEarlier : SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r)
    (hOverlap : ∀ t ∈ surgeryObservationInterval O ∩
        Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants)
    (P : M46Predecessors.{u}) (U : Set (F.slice base).carrier)
    (hU : IsOpen U) (hne : U.Nonempty)
    (hTerminal : ∀ x ∈ U, (F.connection base).scalarCurvature x ≤ (2 * K) * Q)
    (heta : 0 < eta) (hPinchingScale : blowupPinchingThreshold (8 * K) eta ≤ Q) :
    ∃ (b : ℝ) (hb : b ∈ Icc (-2 * terminalCommonIntervalDuration S B K) 0),
      ∃ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc b 0) U,
        (∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x) ∧
        (∀ s (hs : s ∈ Icc b 0), ∀ x ∈ U,
          (F.connection (base + s / Q)).scalarCurvature (e.forward s hs x) ≤ (8 * K) * Q ∧
          |(F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs x)| ≤
            (13 * max (8 * K) 1) * Q ∧
          (F.connection (base + s / Q)).negativeCurvaturePart (e.forward s hs x) ≤ eta * Q) ∧
        (b < -terminalCommonIntervalDuration S B K ∨
          b ∈ Icc (-terminalCommonIntervalDuration S B K) 0 ∧
            ∃ hT : base + b / Q ∈ F.surgery_times,
              ∀ [Nonempty (F.slice (base + b / Q)).carrier],
                ∃ i : Fin (F.event (base + b / Q) hT).cap_count,
                  (e.forward b ⟨le_rfl, hb.2⟩ '' U ∩
                    ((F.event (base + b / Q) hT).caps i).carrier).Nonempty) := by
  have hd := (terminalCommonInterval_duration_bounds S B hK).1
  have hT : 0 ≤ 2 * terminalCommonIntervalDuration S B K := by positivity
  have hQ : 0 < Q := by linarith
  have hwindow : Icc (base + (-2 * terminalCommonIntervalDuration S B K) / Q) base ⊆
      F.time_domain := by
    rw [show base + (-2 * terminalCommonIntervalDuration S B K) / Q =
      base - 2 * terminalCommonIntervalDuration S B K / Q by ring]
    exact terminalCommonInterval_search_window p O hBase hT hScale
  obtain ⟨b, hb, e, hbased, hstop⟩ := exists_normalized_open_region_search F hQ
    (by linarith only [hd]) hwindow U hU hne
  have hceiling : ∀ x ∈ U, (F.connection (base + 0 / Q)).scalarCurvature
      (e.forward 0 ⟨hb.2, le_rfl⟩ x) ≤ (2 * K) * Q := by
    intro x hx
    rw [scalar_eq_of_heq (by simp) (hbased _ x hx)]
    exact hTerminal x hx
  refine ⟨b, hb, e, hbased,
    terminalCommonInterval_stopped_curvature S B hK p O hInitial hConstants hC
      hBase hScale hLarge hThreshold hPinched hEarlier hOverlap P e hb hceiling
      heta hPinchingScale, ?_⟩
  by_cases hlong : b < -terminalCommonIntervalDuration S B K
  · exact Or.inl hlong
  · refine Or.inr ⟨⟨le_of_not_gt hlong, hb.2⟩, hstop.resolve_left ?_⟩
    intro heq
    apply hlong
    rw [heq]
    linarith only [hd]

end PoincareConjecture.M47
