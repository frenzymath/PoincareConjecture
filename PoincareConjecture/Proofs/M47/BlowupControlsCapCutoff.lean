import PoincareConjecture.Proofs.M47.PrefixMonotone
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_5_OverlapCaps

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M47

theorem exists_overlapCapCutoff_upperHorizon {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {K : MetricSurgeryConstants}
    (hconstants : P.metric_surgery.constants = K)
    (p : SurgeryParameterPrefix K) (hstandard : p.setup.standard_initial = g0)
    (r : ℝ) (hr : 0 < r) (hrLast : r ≤ p.r (Fin.last p.i))
    (A eta theta : ℝ) (hA : 0 < A) (heta : 0 < eta)
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        O.H ≤ surgeryEpochStart (p.i + 1) →
        ∀ old : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O r cutoff →
          SurgeryCanonicalOn F (surgeryObservationInterval O) r →
          (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta t ≤ cutoff) →
          Proofs.M46.OverlapCapControl p O old A eta theta := by
  subst K
  obtain ⟨deltaBar, hdelta, persistence⟩ :=
    P.proposition_16_5 p r hstandard hr hrLast A eta theta
      hA heta htheta hthetaOne
  refine ⟨min (p.Delta (Fin.last p.i)) deltaBar,
    lt_min (p.Delta_pos _) hdelta, min_le_left _ _, ?_⟩
  intro F O hH old hadmissible hpinched next hcanonical overlap
  have nextBar := next.mono_delta (min_le_right (p.Delta (Fin.last p.i)) deltaBar)
  have overlapBar : ∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
      F.parameters.delta t ≤ deltaBar :=
    fun t ht => (overlap t ht).trans (min_le_right _ _)
  have scales := old.capPersistenceScales hH hrLast nextBar overlapBar
  have modelScales : SurgeryFixedScalesOn p.setup F
      (O.redecorateTo old.standard_initial_eq)
      (surgeryEpochStart (p.i - 1)) r deltaBar := {
    standard_initial_eq := scales.standard_initial_eq
    local_constants_eq := scales.local_constants_eq
    epsilon_eq := scales.epsilon_eq
    C_eq := scales.C_eq
    r_lower := scales.r_lower
    delta_le := scales.delta_le
    h_eq := scales.h_eq }
  intro t hT _ ht hstart i
  exact persistence F (O.redecorateTo old.standard_initial_eq)
    (Proofs.M46.redecorateTo_standard_flow O old.standard_initial_eq)
    modelScales hadmissible hpinched hcanonical t hT ht hstart
    (scales.delta_le t ⟨ht, hstart⟩) i

theorem exists_first_failure_capCutoff
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (r : ℝ) (hr : 0 < r) (hrLast : r ≤ p.r (Fin.last p.i))
    (A eta theta : ℝ) (hA : 0 < A) (heta : 0 < eta)
    (htheta : 0 < theta) (hthetaOne : theta < 1) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        O.H ≤ surgeryEpochStart (p.i + 1) →
        ∀ old : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O r cutoff →
          (∀ t ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta t ≤ cutoff) →
          ∀ (base : ℝ) (hbase : 0 < base) (hbaseH : base ≤ O.H),
            SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r →
            let short := O.restrictTo base hbase hbaseH
            let oldShort : SurgeryPrefixControls p F short :=
              old.restrictObservation hbaseH
            Proofs.M46.OverlapCapControl p short oldShort A eta theta := by
  obtain ⟨cutoff, hcutoff, hcutoffLast, persistence⟩ :=
    exists_overlapCapCutoff_upperHorizon S.cap_persistence S.cap_constants_eq p
      (by simpa only [hp.setup_eq] using S.setup_standard_initial_eq)
      r hr hrLast A eta theta hA heta htheta hthetaOne
  refine ⟨cutoff, hcutoff, hcutoffLast, ?_⟩
  intro F O hH old hadmissible hpinched next overlap base hbase hbaseH hcanonical
  let short := O.restrictTo base hbase hbaseH
  let oldShort : SurgeryPrefixControls p F short := old.restrictObservation hbaseH
  have hsubset : surgeryObservationInterval short ⊆
      surgeryObservationInterval O ∩ Iio base :=
    fun _ ht => ⟨⟨ht.1, ht.2.trans_le hbaseH⟩, ht.2⟩
  exact persistence F short (hbaseH.trans hH) oldShort hadmissible hpinched
    (next.restrictObservation hbaseH) (hcanonical.restrict hsubset)
    (fun t ht => overlap t ⟨(hsubset ht.1).1, ht.2⟩)

end PoincareConjecture.M47
