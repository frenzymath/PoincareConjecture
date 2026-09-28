import PoincareConjecture.Definitions.Ch16.ControlledSurgery
import PoincareConjecture.Definitions.Ch15.SurgeryEndPolicy

set_option autoImplicit false

universe u

namespace PoincareConjecture


structure SurgeryPostPrefixScales {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) (F : SurgeryFlowData.{u})
    (O : SurgeryObservation F) (rNext deltaNext : ℝ) : Prop where
  r_eq : ∀ t ∈ surgeryObservationInterval O ∩ Set.Ici (surgeryEpochStart p.i),
    F.parameters.r t = rNext
  delta_le : ∀ t ∈ surgeryObservationInterval O ∩ Set.Ici (surgeryEpochStart p.i),
    F.parameters.delta t ≤ deltaNext
  h_eq : ∀ t ∈ surgeryObservationInterval O ∩ Set.Ici (surgeryEpochStart p.i),
    F.parameters.h t = p.setup.selector.h
      (F.parameters.delta t * F.parameters.r t) (F.parameters.delta t)

def SurgeryObservationIsNextEpoch {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {F : SurgeryFlowData.{u}}
    (O : SurgeryObservation F) : Prop :=
  surgeryEpochStart p.i < O.H ∧ O.H ≤ surgeryEpochStart (p.i + 1)






def SurgeryObservationIsMaximalNextEpoch {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {F : SurgeryFlowData.{u}}
    (O : SurgeryObservation F) : Prop :=
  SurgeryObservationIsNextEpoch p O ∧ F.time_domain = Set.Ico 0 O.H



structure SurgeryNoncollapseExtension {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) where
  kappaNew : ℝ
  cutoff : ℝ → ℝ
  kappa_pos : 0 < kappaNew
  kappa_le_last : kappaNew ≤ p.kappa ⟨p.i, Nat.lt_succ_self _⟩
  cutoff_bounds : ∀ rNext, 0 < rNext → rNext ≤ p.r ⟨p.i, Nat.lt_succ_self _⟩ →
    0 < cutoff rNext ∧ cutoff rNext ≤ p.Delta ⟨p.i, Nat.lt_succ_self _⟩
  noncollapsed : ∀ rNext, 0 < rNext → rNext ≤ p.r ⟨p.i, Nat.lt_succ_self _⟩ →
    ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      SurgeryObservationIsNextEpoch p O →
      SurgeryPrefixControls p F O →
      SurgeryFlowAdmissible F →
      SurgeryFlowPinched F →
      SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
      SurgeryPostPrefixScales p F O rNext (cutoff rNext) →
      SurgeryCanonicalOn F (surgeryObservationInterval O) rNext →
      (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
        F.parameters.delta t ≤ cutoff rNext) →
      SurgeryNoncollapsedOn F (surgeryObservationInterval O) kappaNew





def SurgeryVolumeControlOn (F : SurgeryFlowData.{u})
    (J : Set ℝ) (kappa : ℝ)
    (center_ok : ∀ (t : ℝ), (F.slice t).carrier → Prop) : Prop :=
  ∀ t ∈ J, t ∈ F.time_domain → ∀ x : (F.slice t).carrier,
    center_ok t x →
    ∀ r : ℝ, 0 < r → r ≤ F.parameters.epsilon →
    ∀ e : SurgeryFlowCylinder F (F.slice t) t 1
      (Set.Icc (-r ^ 2) 0) ((F.metric t).ball x r),
      (∀ (h : (0 : ℝ) ∈ Set.Icc (-r ^ 2) 0) y,
        y ∈ (F.metric t).ball x r → HEq (e.forward 0 h y) y) →
      (∀ s hs y, y ∈ (F.metric t).ball x r →
        (F.connection (t + s / 1)).curvatureTensorNorm (e.forward s hs y) ≤
          r⁻¹ ^ 2) →
      ENNReal.ofReal (kappa * r ^ 3) ≤
        calibratedMetricVolume (F.metric t) ((F.metric t).ball x r)


def SurgeryTestedVolumeOn (F : SurgeryFlowData.{u})
    (J : Set ℝ) (kappa rBase B : ℝ) : Prop :=
  SurgeryVolumeControlOn F J kappa (fun t x =>
    ¬ SurgeryPositiveComponentAt F t x ∧
      (F.connection t).scalarCurvature x ≤ B * rBase⁻¹ ^ 2)

end PoincareConjecture
