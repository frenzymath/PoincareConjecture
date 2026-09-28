import PoincareConjecture.Proofs.M47.BlowupControlsFirstFailureCylinder
import PoincareConjecture.Proofs.M47.TerminalSourceCharts
import PoincareConjecture.Proofs.M47.TerminalSourceRealizationHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalSourceJetsG4_on_chart
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants)
    {F₀ : SurgeryFlowData.{u}} (O : SurgeryObservation F₀)
    (hInitial : F₀.standard_initial = S.setup.standard_initial)
    (hConstants : F₀.local_constants = S.constants)
    (hC : F₀.parameters.C = S.setup.C)
    {base τ r Q₀ : ℝ}
    (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hτ₀ : 0 ≤ τ)
    (hScale : 64 * (τ + 1) ≤ Q₀)
    (hLarge : B.curvature_threshold ≤ Q₀)
    (hThreshold : r⁻¹ ^ 2 ≤ Q₀)
    (hPinched : SurgeryFlowPinched F₀)
    (hEarlier : SurgeryCanonicalOn
      F₀ (surgeryObservationInterval O ∩ Iio base) r)
    (hOverlap : ∀ u ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H,
      F₀.parameters.delta u ≤ B.delta S.setup.standard_initial S.constants)
    (P : M46Predecessors.{u})
    {W : M33RegularHistoryWindow F₀}
    (H : M33RegularHistoryData W)
    {C₀ : GeneralizedSliceCarrier.{u}}
    (hτ : 0 < τ)
    (U : TopologicalSpace.Opens C₀.carrier)
    (e : GeneralizedFlowCylinder H.generalized C₀ base Q₀
      (Icc (-τ) 0) (U : Set C₀.carrier))
    (F : RicciFlow 3 U (Icc (-τ) 0))
    (htime : ∀ s ∈ Icc (-τ) 0,
      base + s / Q₀ ∈ H.generalized.interval)
    (hnorm : ∀ (s : ℝ) (hs : s ∈ Icc (-τ) 0) (x : U),
      (F.connection s).curvatureTensorNorm x =
        (H.generalized.connection (base + s / Q₀)).curvatureTensorNorm
          (e.forward s hs x.val) / Q₀)
    {R L eta : ℝ} (hL : 1 ≤ L)
    (hTerminal : ∀ x : C₀.carrier, x ∈ (U : Set C₀.carrier) →
      normalizedCylinderScalar e x 0 ≤ L)
    (hShort : blowupAnalyticConstant S B * L * τ ≤ 1 / 4)
    (heta : 0 < eta)
    (hPinchingScale : blowupPinchingThreshold (4 * L / 3) eta ≤ Q₀)
    (C : TerminalSourceChart (F.metric 0) R) :
    (∀ s ∈ Icc (-τ) 0, base + s / Q₀ ∈ H.generalized.interval) ∧
      ∀ s ∈ Icc (-τ) 0, ∀ y ∈ C.chart '' Metric.ball 0 R,
        (F.connection s).curvatureTensorNorm y ≤
          13 * max (4 * L / 3) 1 := by
  have hτpos : 0 < τ := lt_of_le_of_ne hτ₀ (Ne.symm (ne_of_gt hτ))
  refine ⟨htime, ?_⟩
  intro s hs y hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hx : (C.chart z).val ∈ (U : Set C₀.carrier) := (C.chart z).property
  have hraw := first_failure_cylinder_curvature_bounds S B p O
    hInitial hConstants hC hBase hτpos.le hScale hLarge hThreshold hPinched
    hEarlier hOverlap P H e hx hL (hTerminal (C.chart z).val hx) hShort
    heta hPinchingScale s hs
  have hcurv :
      |(H.generalized.connection (base + s / Q₀)).curvatureTensorNorm
          (e.forward s hs (C.chart z).val)| ≤
        (13 * max (4 * L / 3) 1) * Q₀ := by
    simpa only [GeneralizedRicciFlowData.curvatureNorm,
      GeneralizedFlowCylinder.pointMap] using hraw.1
  rw [hnorm s hs (C.chart z)]
  apply (div_le_iff₀ e.scale_pos).2
  exact (le_abs_self _).trans hcurv

theorem terminalSourceJetsG4_realized
    (P₄₇ : M47Predecessors.{u})
    (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants)
    {F₀ : SurgeryFlowData.{u}} (O : SurgeryObservation F₀)
    (hInitial : F₀.standard_initial = S.setup.standard_initial)
    (hConstants : F₀.local_constants = S.constants)
    (hC : F₀.parameters.C = S.setup.C)
    {base τ r Q₀ : ℝ}
    (hBase : base ∈ Ico (surgeryEpochStart p.i) O.H)
    (hτ₀ : 0 ≤ τ)
    (hScale : 64 * (τ + 1) ≤ Q₀)
    (hLarge : B.curvature_threshold ≤ Q₀)
    (hThreshold : r⁻¹ ^ 2 ≤ Q₀)
    (hPinched : SurgeryFlowPinched F₀)
    (hEarlier : SurgeryCanonicalOn
      F₀ (surgeryObservationInterval O ∩ Iio base) r)
    (hOverlap : ∀ u ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H,
      F₀.parameters.delta u ≤ B.delta S.setup.standard_initial S.constants)
    (P : M46Predecessors.{u})
    {W : M33RegularHistoryWindow F₀}
    (H : M33RegularHistoryData W)
    {C₀ : GeneralizedSliceCarrier.{u}}
    (hτ : 0 < τ)
    (U : TopologicalSpace.Opens C₀.carrier)
    (hne : (U : Set C₀.carrier).Nonempty)
    (e : GeneralizedFlowCylinder H.generalized C₀ base Q₀
      (Icc (-τ) 0) (U : Set C₀.carrier))
    {R L eta : ℝ} (hL : 1 ≤ L)
    (hTerminal : ∀ x : C₀.carrier, x ∈ (U : Set C₀.carrier) →
      normalizedCylinderScalar e x 0 ≤ L)
    (hShort : blowupAnalyticConstant S B * L * τ ≤ 1 / 4)
    (heta : 0 < eta)
    (hPinchingScale : blowupPinchingThreshold (4 * L / 3) eta ≤ Q₀) :
    ∃ F : RicciFlow 3 U (Icc (-τ) 0),
      (∀ s ∈ Icc (-τ) 0,
        base + s / Q₀ ∈ H.generalized.interval) ∧
        ∀ C : TerminalSourceChart (F.metric 0) R,
          ∀ s ∈ Icc (-τ) 0, ∀ y ∈ C.chart '' Metric.ball 0 R,
            (F.connection s).curvatureTensorNorm y ≤
              13 * max (4 * L / 3) 1 := by
  obtain ⟨F, htime, hread⟩ := terminalSourceRealization_regular_history
    P₄₇ H hτ U hne e
  refine ⟨F, htime, ?_⟩
  intro C s hs y hy
  have h := terminalSourceJetsG4_on_chart S B p O hInitial hConstants hC
    hBase hτ₀ hScale hLarge hThreshold hPinched hEarlier hOverlap P H hτ U e F
    htime (fun s hs x => (hread s hs x).1.2.2) hL hTerminal hShort heta
    hPinchingScale C
  exact h.2 s hs y hy

end PoincareConjecture.M47
