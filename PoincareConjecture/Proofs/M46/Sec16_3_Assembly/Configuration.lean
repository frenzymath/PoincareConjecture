import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Thm8_1_StableConfiguration
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_1_Prefix

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

theorem configuration_from_producers (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {taubar l0 V : ℝ} (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (D : NoncollapseTest F O)
    (history : HalfRadiusHistory D) (rho A eta theta : ℝ)
    (time_new : surgeryEpochStart p.i ≤ D.time)
    (radius_large : rho ≤ D.radius)
    (cap_persistence : OverlapCapControl p O old A eta theta)
    (cap_avoidance : surgeryEpochStart p.i ≤ D.time → rho ≤ D.radius →
      OverlapCapControl p O old A eta theta →
      ∃ confinement : ActionConfinement history.spacetime.geometry.toLGeometry
        D.time (surgeryEpochStart (p.i - 1))
        ((history.spacetime.geometry.sliceIdentification D.time).identification
          history.center).val, confinement.barrier = actionBudget p)
    (minimizers : ∀ confinement : ActionConfinement history.spacetime.geometry.toLGeometry
        D.time (surgeryEpochStart (p.i - 1))
        ((history.spacetime.geometry.sliceIdentification D.time).identification
          history.center).val,
      confinement.barrier = actionBudget p →
      surgeryEpochStart p.i ≤ D.time → rho ≤ D.radius →
      Nonempty (MinimizingRegion history.spacetime.geometry.toLGeometry
        D.time (surgeryEpochStart (p.i - 1))
        ((history.spacetime.geometry.sliceIdentification D.time).identification
          history.center).val confinement))
    (positive_propagation : PositiveAncestorExclusion history)
    (stable_set : ∀ confinement : ActionConfinement history.spacetime.geometry.toLGeometry
        D.time (surgeryEpochStart (p.i - 1))
        ((history.spacetime.geometry.sliceIdentification D.time).identification
          history.center).val,
      confinement.barrier = actionBudget p →
      MinimizingRegion history.spacetime.geometry.toLGeometry
        D.time (surgeryEpochStart (p.i - 1))
        ((history.spacetime.geometry.sliceIdentification D.time).identification
          history.center).val confinement →
      PositiveAncestorExclusion history → Nonempty (StableSource history taubar l0 V)) :
    ENNReal.ofReal (configurationKappa p U * D.radius ^ 3) ≤
      calibratedMetricVolume (F.metric D.time) ((F.metric D.time).ball D.center D.radius) := by
  obtain ⟨confinement, hbudget⟩ := cap_avoidance time_new radius_large cap_persistence
  obtain ⟨region⟩ := minimizers confinement hbudget time_new radius_large
  obtain ⟨source⟩ := stable_set confinement hbudget region positive_propagation
  exact source.volume P p U

structure ObservedInputs {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    (rNext cutoff : ℝ) (F : SurgeryFlowData.{u}) (O : SurgeryObservation F) : Prop where
  next_epoch : SurgeryObservationIsNextEpoch p O
  old : SurgeryPrefixControls p F O
  admissible : SurgeryFlowAdmissible F
  pinched : SurgeryFlowPinched F
  terminal_policy : SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O)
  scales : SurgeryPostPrefixScales p F O rNext cutoff
  canonical : SurgeryCanonicalOn F (surgeryObservationInterval O) rNext
  overlap : ∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
    F.parameters.delta t ≤ cutoff

def CapAvoidanceProducer {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) (rNext cutoff rho A eta theta : ℝ) : Prop :=
  ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
    (inputs : ObservedInputs p rNext cutoff F O),
    ∀ (D : NoncollapseTest F O) (H : HalfRadiusHistory D),
      surgeryEpochStart p.i ≤ D.time → rho ≤ D.radius →
      OverlapCapControl p O inputs.old A eta theta →
      ∃ C : ActionConfinement H.spacetime.geometry.toLGeometry
        D.time (surgeryEpochStart (p.i - 1))
        ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val,
        C.barrier = actionBudget p

def MinimizingRegionProducer {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) (rNext cutoff rho : ℝ) : Prop :=
  ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
    ObservedInputs p rNext cutoff F O →
    ∀ (D : NoncollapseTest F O) (H : HalfRadiusHistory D),
      surgeryEpochStart p.i ≤ D.time → rho ≤ D.radius →
      ∀ C : ActionConfinement H.spacetime.geometry.toLGeometry
        D.time (surgeryEpochStart (p.i - 1))
        ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val,
        C.barrier = actionBudget p →
        Nonempty (MinimizingRegion H.spacetime.geometry.toLGeometry
          D.time (surgeryEpochStart (p.i - 1))
          ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val C)

def StableSourceProducer {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) (taubar l0 V : ℝ) : Prop :=
  ∀ (rNext cutoff : ℝ) (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
    ObservedInputs p rNext cutoff F O →
    ∀ (D : NoncollapseTest F O) (H : HalfRadiusHistory D),
      surgeryEpochStart p.i ≤ D.time →
      ∀ C : ActionConfinement H.spacetime.geometry.toLGeometry
        D.time (surgeryEpochStart (p.i - 1))
        ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val,
        C.barrier = actionBudget p →
        MinimizingRegion H.spacetime.geometry.toLGeometry
          D.time (surgeryEpochStart (p.i - 1))
          ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val C →
        PositiveAncestorExclusion H → Nonempty (StableSource H taubar l0 V)

theorem volume_of_stableSourceProducer (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {taubar l0 V : ℝ} (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    (produce : StableSourceProducer.{u} p taubar l0 V)
    (rNext cutoff : ℝ) {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    (D : NoncollapseTest F O) (H : HalfRadiusHistory D)
    (time_new : surgeryEpochStart p.i ≤ D.time)
    (C : ActionConfinement H.spacetime.geometry.toLGeometry
      D.time (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val)
    (budget : C.barrier = actionBudget p)
    (region : MinimizingRegion H.spacetime.geometry.toLGeometry
      D.time (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val C)
    (positive : PositiveAncestorExclusion H) :
    ENNReal.ofReal (configurationKappa p U * D.radius ^ 3) ≤
      calibratedMetricVolume (F.metric D.time) ((F.metric D.time).ball D.center D.radius) := by
  obtain ⟨Q⟩ := produce rNext cutoff F O inputs D H time_new C budget region positive
  exact Q.volume P p U

theorem volume_of_reviewed_producers (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {taubar l0 V : ℝ} (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    (stable : StableSourceProducer.{u} p taubar l0 V)
    (rNext cutoff rho A eta theta : ℝ)
    (avoid : CapAvoidanceProducer.{u} p rNext cutoff rho A eta theta)
    (minimize : MinimizingRegionProducer.{u} p rNext cutoff rho)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O)
    (D : NoncollapseTest F O) (H : HalfRadiusHistory D)
    (time_new : surgeryEpochStart p.i ≤ D.time) (radius_large : rho ≤ D.radius)
    (caps : OverlapCapControl p O inputs.old A eta theta)
    (positive : PositiveAncestorExclusion H) :
    ENNReal.ofReal (configurationKappa p U * D.radius ^ 3) ≤
      calibratedMetricVolume (F.metric D.time) ((F.metric D.time).ball D.center D.radius) := by
  obtain ⟨C, budget⟩ := avoid F O inputs D H time_new radius_large caps
  obtain ⟨region⟩ := minimize F O inputs D H time_new radius_large C budget
  exact volume_of_stableSourceProducer P p U stable rNext cutoff inputs
    D H time_new C budget region positive

def TestConclusion {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {taubar l0 V : ℝ} (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    (rNext rho : ℝ) {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (D : NoncollapseTest F O) : Prop :=
  (rNext⁻¹ ^ 2 ≤ (F.connection D.time).scalarCurvature D.center ∧
    ENNReal.ofReal (configurationKappa p U * D.radius ^ 3) ≤
      calibratedMetricVolume (F.metric D.time) ((F.metric D.time).ball D.center D.radius)) ∨
    ((F.connection D.time).scalarCurvature D.center < rNext⁻¹ ^ 2 ∧
      D.radius < rho ∧
      ENNReal.ofReal (configurationKappa p U * D.radius ^ 3) ≤
        calibratedMetricVolume (F.metric D.time)
          ((F.metric D.time).ball D.center D.radius)) ∨
    ∃ H : HalfRadiusHistory D, Nonempty (StableSource H taubar l0 V)

theorem induction_of_uniform_sources (P : M46Predecessors.{u})
    (S : RepairedControlledSchedulesData.{u})
    (produce : ∀ (p : SurgeryParameterPrefix S.constants), S.SeedCompatible p →
      ∃ taubar l0 V : ℝ, ∃ U : M15GeneralizedUniformData.{u} 3 taubar l0 V,
        ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
          ∃ rho : ℝ, 0 < rho ∧ rho ≤ rNext ∧
          ∃ delta : ℝ, 0 < delta ∧ delta ≤ p.Delta (Fin.last p.i) ∧
            ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
              ObservedInputs p rNext delta F O →
              ∀ D : NoncollapseTest F O, surgeryEpochStart p.i ≤ D.time →
                TestConclusion p U rNext rho D) :
    Nonempty (RepairedNoncollapseInductionData.{u} S) := by
  classical
  refine ⟨⟨fun p hp => ?_⟩⟩
  obtain ⟨taubar, l0, V, U, hU⟩ := produce p hp
  let rho : ℝ → ℝ := fun rNext =>
    if hr : 0 < rNext ∧ rNext ≤ p.r (Fin.last p.i) then
      Classical.choose (hU rNext hr.1 hr.2) else 1
  have rho_spec (rNext : ℝ) (hr : 0 < rNext)
      (hle : rNext ≤ p.r (Fin.last p.i)) :
      0 < rho rNext ∧ rho rNext ≤ rNext ∧
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          ObservedInputs p rNext delta F O →
          ∀ D : NoncollapseTest F O, surgeryEpochStart p.i ≤ D.time →
            TestConclusion p U rNext (rho rNext) D := by
    have hallowed : 0 < rNext ∧ rNext ≤ p.r (Fin.last p.i) := ⟨hr, hle⟩
    simpa only [rho, dif_pos hallowed] using
      Classical.choose_spec (hU rNext hr hle)
  let cutoff : ℝ → ℝ := fun rNext =>
    if hr : 0 < rNext ∧ rNext ≤ p.r (Fin.last p.i) then
      Classical.choose (rho_spec rNext hr.1 hr.2).2.2 else 1
  have cutoff_spec (rNext : ℝ) (hr : 0 < rNext)
      (hle : rNext ≤ p.r (Fin.last p.i)) :
      0 < cutoff rNext ∧ cutoff rNext ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          ObservedInputs p rNext (cutoff rNext) F O →
          ∀ D : NoncollapseTest F O, surgeryEpochStart p.i ≤ D.time →
            TestConclusion p U rNext (rho rNext) D := by
    have hallowed : 0 < rNext ∧ rNext ≤ p.r (Fin.last p.i) := ⟨hr, hle⟩
    simpa only [cutoff, dif_pos hallowed] using
      Classical.choose_spec (rho_spec rNext hr hle).2.2
  refine ⟨{
    kappaNew := configurationKappa p U
    cutoff := cutoff
    kappa_pos := configurationKappa_pos p U
    kappa_le_last := configurationKappa_le_last p U
    cutoff_bounds := fun r hr hle =>
      ⟨(cutoff_spec r hr hle).1, (cutoff_spec r hr hle).2.1⟩
    noncollapsed := ?_
  }⟩
  intro rNext hr hle F O hepoch old hadm hpin hpolicy hscales hcan hoverlap
    t ht htF x hpositive r hradius hrle e hbase hcurv
  let D : NoncollapseTest F O :=
    ⟨t, ht, htF, x, hpositive, r, hradius, hrle, e, hbase, hcurv⟩
  by_cases hnew : surgeryEpochStart p.i ≤ t
  swap
  · exact prefix_noncollapsed old (configurationKappa_le_last p U)
      t ⟨ht, ht.1, lt_of_not_ge hnew⟩ htF x hpositive r hradius hrle e hbase hcurv
  rcases (cutoff_spec rNext hr hle).2.2 F O
    ⟨hepoch, old, hadm, hpin, hpolicy, hscales, hcan, hoverlap⟩ D hnew with
      h | h | ⟨H, source⟩
  · exact h.2
  · exact h.2.2
  · obtain ⟨Q⟩ := source
    exact Q.volume P p U

end PoincareConjecture.Proofs.M46
