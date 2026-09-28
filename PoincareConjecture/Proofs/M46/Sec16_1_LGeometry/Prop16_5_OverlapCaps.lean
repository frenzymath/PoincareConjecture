import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Configuration

set_option autoImplicit false

universe u

namespace PoincareConjecture.Proofs.M46

theorem redecorateTo_standard_flow {K : MetricSurgeryConstants}
    {p : SurgeryParameterPrefix K} {F : SurgeryFlowData.{u}}
    (O : SurgeryObservation F)
    (hstandard : F.standard_initial = p.setup.standard_initial) :
    HEq (O.redecorateTo hstandard).standard_flow p.setup.standard_flow := by
  exact eqRec_heq _ _

theorem exists_overlapCapCutoff {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {K : MetricSurgeryConstants}
    (hconstants : P.metric_surgery.constants = K)
    (p : SurgeryParameterPrefix K)
    (hstandard : p.setup.standard_initial = g0)
    (rNext : ℝ) (hr : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (A eta theta : ℝ) (hA : 0 < A) (heta : 0 < eta)
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryObservationIsNextEpoch p O →
        ∀ old : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O rNext cutoff →
          SurgeryCanonicalOn F (surgeryObservationInterval O) rNext →
          (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta t ≤ cutoff) →
          OverlapCapControl p O old A eta theta := by
  subst K
  obtain ⟨deltaBar, hdelta, persistence⟩ :=
    P.proposition_16_5 p rNext hstandard hr hrLast A eta theta
      hA heta htheta hthetaOne
  refine ⟨min (p.Delta (Fin.last p.i)) deltaBar,
    lt_min (p.Delta_pos _) hdelta, min_le_left _ _, ?_⟩
  intro F O hO old hadmissible hpinched next hcanonical overlap
  have nextBar : SurgeryPostPrefixScales p F O rNext deltaBar := {
    r_eq := next.r_eq
    delta_le := fun t ht => (next.delta_le t ht).trans (min_le_right _ _)
    h_eq := next.h_eq
  }
  have overlapBar : ∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
      F.parameters.delta t ≤ deltaBar :=
    fun t ht => (overlap t ht).trans (min_le_right _ _)
  have scales := old.capPersistenceScales hO.2 hrLast nextBar overlapBar
  have modelScales : SurgeryFixedScalesOn p.setup F
      (O.redecorateTo old.standard_initial_eq)
      (surgeryEpochStart (p.i - 1)) rNext deltaBar := {
    standard_initial_eq := scales.standard_initial_eq
    local_constants_eq := scales.local_constants_eq
    epsilon_eq := scales.epsilon_eq
    C_eq := scales.C_eq
    r_lower := scales.r_lower
    delta_le := scales.delta_le
    h_eq := scales.h_eq
  }
  intro t hT _ ht hstart j
  have hdelta_t : F.parameters.delta t ≤ deltaBar :=
    scales.delta_le t ⟨ht, hstart⟩
  exact persistence F (O.redecorateTo old.standard_initial_eq)
    (redecorateTo_standard_flow O old.standard_initial_eq)
    modelScales hadmissible hpinched hcanonical t hT ht hstart hdelta_t j

theorem exists_seedCompatibleOverlapCapCutoff
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (rNext : ℝ) (hr : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i))
    (A eta theta : ℝ) (hA : 0 < A) (heta : 0 < eta)
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryObservationIsNextEpoch p O →
        ∀ old : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O rNext cutoff →
          SurgeryCanonicalOn F (surgeryObservationInterval O) rNext →
          (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta t ≤ cutoff) →
          OverlapCapControl p O old A eta theta := by
  apply exists_overlapCapCutoff S.cap_persistence S.cap_constants_eq p
    (by simpa only [hp.setup_eq] using S.setup_standard_initial_eq) rNext hr hrLast
    A eta theta hA heta htheta hthetaOne

end PoincareConjecture.Proofs.M46
