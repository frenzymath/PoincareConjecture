import PoincareConjecture.Proofs.M48.ContinuationInput
import PoincareConjecture.Proofs.M48.TerminalReference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

def m48TerminalCore {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
    {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (H : SingularTimeAssumptions G T M) (horn : RepairedHornSelectionData H)
    (rho : ℝ) : Set M :=
  {y | y ∈ H.reference.regularLimitSet ∧
    ∃ z : (horn.limit.extension.extended.slice T).carrier,
      horn.limit.terminal_source z = y ∧ horn.limit.terminal_scalar z ≤ rho⁻¹ ^ 2}

namespace M48AnalyticCalibration

variable {S : RepairedControlledSchedulesData.{u}} (A : M48AnalyticCalibration S)
  {p : SurgeryParameterPrefix S.constants} {F : SurgeryFlowData.{u}}
  {O : SurgeryObservation F} (hp : S.SeedCompatible p)
  (old : SurgeryPrefixControls p F O)
  {Q : SurgeryNoncollapseExtension.{u} p} {N : SurgeryCanonicalExtension p Q}
  (controls : SurgeryEpochContinuationControls p F O Q N)
  (hstart : surgeryEpochStart p.i ≤ O.H)
  (hend : O.H < surgeryEpochStart (p.i + 1))
  (hdomain : F.time_domain = Ico 0 O.H)
  {L : RepairedPreterminalSlab F O.H} {R : M48RegularSpacetimeData L}
  (reference : M48RegularReferenceData L R.history)
  (H : SingularTimeAssumptions R.history.generalized O.H (F.slice L.start).carrier)
  (href : H.reference = reference.reference)
  (hr : H.r₀ = A.historyRadius N.rNext)
  (he : H.epsilon = S.setup.epsilon) (hC : H.constant = S.setup.C)
  (hA : H.analytic_constant = S.calibration.analytic_constant)
  (limit : RepairedSingularRegularLimitData H) (horn : RepairedHornSelectionData H)
  (hlimit : horn.limit = limit)

noncomputable def terminalBridge :
    RepairedContinuationLimitBridge H limit horn
      (A.continuationInput hp old controls hstart hend hdomain L
        (m48TerminalCore H horn (F.parameters.delta O.H * F.parameters.r O.H))) := by
  let D : M48RegularReferenceData L R.history := {
    reference := H.reference
    start_inside := by rw [href]; exact reference.start_inside
    metric_eq := by rw [href]; exact reference.metric_eq
    connection_eq := by rw [href]; exact reference.connection_eq
    history_eq := by simpa only [href] using reference.history_eq }
  let I := A.continuationInput hp old controls hstart hend hdomain L
    (m48TerminalCore H horn (F.parameters.delta O.H * F.parameters.r O.H))
  have hstd : F.standard_initial = S.standard_initial :=
    old.standard_initial_eq.trans
      ((congrArg SurgeryControlSetup.standard_initial hp.setup_eq).trans
        S.setup_standard_initial_eq)
  refine {
    appendixA := S.calibration.appendixA
    appendixA_accuracy := by simpa only [he] using S.setup_appendixA_accuracy
    constant_one_le := by rw [hC]; exact S.setup.C_large
    history := R.history.history
    reference_start_lt := D.start_inside
    reference_identify := D.identify
    history_reference := D.history_identify
    reference_metric_pullback := D.metric_pullback
    reference_scalar_pullback := D.scalar_pullback
    reference_transport_compatibility := D.transport_compatibility
    limit_extension_eq := congrArg SingularLimitConclusion.extension hlimit
    rho_lt_r₀ := by rw [hr]; exact I.rho_lt_r₀
    core_map := id
    core_map_eq_reference := fun x => (D.identify_slab _ x).symm
    core_map_image := by exact Set.image_id _
    core_status_iff := Iff.rfl
    parameter_epsilon_eq := he.trans
      (old.epsilon_eq.trans (congrArg SurgeryControlSetup.epsilon hp.setup_eq)).symm
    parameter_constant_eq := hC.trans
      (old.C_eq.trans (congrArg SurgeryControlSetup.C hp.setup_eq)).symm
    parameter_r₀_eq := hr
    surgery_operation := ?_
    deep_horn_application := ?_ }
  · have hK : S.cap_persistence.metric_surgery.constants = F.local_constants :=
      S.cap_constants_eq.trans old.local_constants_eq.symm
    have operation : ∀ J : MetricSurgeryInput F.local_constants
        (horn.limit.extension.extended.metric O.H),
        Nonempty (MetricSurgeryResult S.standard_initial J) :=
      hK ▸ (S.cap_persistence.metric_surgery.operation
        (g := horn.limit.extension.extended.metric O.H))
    simpa only [hstd] using operation
  · intro actual_horn hboundary
    have hh : F.parameters.h O.H = S.calibration.horn_selector.h
        (F.parameters.delta O.H * F.parameters.r O.H) (F.parameters.delta O.H) := by
      simpa only [hp.setup_eq, S.calibration.selector_eq] using
        controls.next_h O.H ⟨hstart, hend⟩
    exact S.calibration.horn_selector.deep_horn _ _ _ I.rho_pos
      (F.parameters.delta_pos O.H O.H_pos.le) (F.parameters.h_pos O.H O.H_pos.le)
      hh.le H (by rw [hr]; exact I.rho_lt_r₀) he hC hA horn.limit actual_horn hboundary

end M48AnalyticCalibration

end PoincareConjecture
