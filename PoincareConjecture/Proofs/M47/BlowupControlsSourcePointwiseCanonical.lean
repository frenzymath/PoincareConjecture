import PoincareConjecture.Proofs.M47.BlowupControlsSourceCanonicalCap
import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourceStandardSplit
import PoincareConjecture.Proofs.M47.PrefixMonotone
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_5_OverlapCaps










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem exists_source_standard_canonical_neighborhood_of_initial
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {theta v : ℝ} (htheta : theta < 1) (hv : v ∈ Icc 0 theta)
    (z : StandardCapSpace)
    (initial_neighborhood :
      ∀ N : StandardEvolvingNeck S.cap_persistence.standard_cap.atlas
        S.cap_persistence.standard_cap.flow v (S.calibration.beta * S.setup.epsilon / 3) z
        (Icc (-v * (S.cap_persistence.standard_cap.flow.connection v).scalarCurvature z) 0),
        Disjoint N.patch.carrier {y | S.standard_initial.metric.edist 0 y ≤
          ENNReal.ofReal (S.standard_initial.cylindrical_end.radius + 4)} →
        v * (S.cap_persistence.standard_cap.flow.connection v).scalarCurvature z <
          1 + S.calibration.beta * S.setup.epsilon / 3 →
      ∃ A0 eta0 nearTime Q0 : ℝ, ∃ V : Set StandardCapSpace,
        0 < A0 ∧ 0 < eta0 ∧ 0 < nearTime ∧ 0 < Q0 ∧ IsOpen V ∧ z ∈ V ∧
        ∀ A : ℝ, A0 ≤ A → ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
        ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
          ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
          ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
            O.H ≤ surgeryEpochStart (p.i + 1) →
          ∀ prior : SurgeryPrefixControls p F O,
            SurgeryFlowAdmissible F → SurgeryFlowPinched F →
            SurgeryPostPrefixScales p F O rNext cutoff →
            (∀ b ∈ surgeryObservationInterval O ∩ overlapInterval p,
              F.parameters.delta b ≤ cutoff) →
          ∀ (t : ℝ) (hT : t ∈ F.surgery_times),
          ∀ [Nonempty (F.slice t).carrier], ∀ (i : Fin (F.event t hT).cap_count)
            (J : Set ℝ)
            (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
              ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
            (initial : SurgeryCapInitialComparison F t hT i A),
            SurgeryCapFamilyComparison F
              (O.redecorateTo prior.standard_initial_eq).standard_flow A eta e initial.chart →
          ∀ hzero : (0 : ℝ) ∈ J,
            (∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
              HEq (e.forward 0 hzero y) y) →
            0 < F.parameters.h t →
          ∀ (s : ℝ) (hs : s ∈ J), s ∈ Icc 0 theta → Icc 0 s ⊆ J →
            |s - v| < nearTime → ∀ z' ∈ V,
            let base := t + s / ((F.parameters.h t)⁻¹ ^ 2)
            let x := e.forward s hs (initial.chart z')
            let Q := (F.connection base).scalarCurvature x
            base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → rNext⁻¹ ^ 2 ≤ Q →
            SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
            Q * (base - t) ∈ Icc 0 1 →
            SurgeryCanonicalControl F base x S.setup.epsilon S.setup.C) :
    ∃ A0 eta0 nearTime Q0 : ℝ, ∃ V : Set StandardCapSpace,
      0 < A0 ∧ 0 < eta0 ∧ 0 < nearTime ∧ 0 < Q0 ∧ IsOpen V ∧ z ∈ V ∧
      ∀ A : ℝ, A0 ≤ A → ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          O.H ≤ surgeryEpochStart (p.i + 1) →
        ∀ prior : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O rNext cutoff →
          (∀ b ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta b ≤ cutoff) →
        ∀ (t : ℝ) (hT : t ∈ F.surgery_times),
        ∀ [Nonempty (F.slice t).carrier], ∀ (i : Fin (F.event t hT).cap_count)
          (J : Set ℝ)
          (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
            ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
          (initial : SurgeryCapInitialComparison F t hT i A),
          SurgeryCapFamilyComparison F
            (O.redecorateTo prior.standard_initial_eq).standard_flow A eta e initial.chart →
        ∀ hzero : (0 : ℝ) ∈ J,
          (∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
            HEq (e.forward 0 hzero y) y) →
          0 < F.parameters.h t →
        ∀ (s : ℝ) (hs : s ∈ J), s ∈ Icc 0 theta → Icc 0 s ⊆ J →
          |s - v| < nearTime → ∀ z' ∈ V,
          let base := t + s / ((F.parameters.h t)⁻¹ ^ 2)
          let x := e.forward s hs (initial.chart z')
          let Q := (F.connection base).scalarCurvature x
          base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → rNext⁻¹ ^ 2 ≤ Q →
          SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
          Q * (base - t) ∈ Icc 0 1 →
          SurgeryCanonicalControl F base x S.setup.epsilon S.setup.C := by
  rcases standard_source_alternative_split S htheta hv z with hcap | hneck | hN
  · obtain ⟨N⟩ := hcap
    obtain ⟨A0, eta0, nearTime, V, hA0, heta0, hnearTime, hV, hzV, transfer⟩ :=
      exists_source_standard_cap_canonical_neighborhood S htheta hv N
    refine ⟨A0, eta0, nearTime, 1, V, hA0, heta0, hnearTime, zero_lt_one, hV, hzV, ?_⟩
    intro A hA eta heta hetaSmall rNext _hrNext _hrLast
    refine ⟨p.Delta (Fin.last p.i), p.Delta_pos _, le_rfl, ?_⟩
    intro F O _hH prior _hadmissible _hpinch _next _overlap t hT hn i J e initial
      comparison _hzero _based hh s hs hst _hJ hnear z' hz'
    dsimp only
    intro _hbase _hlarge _hthreshold _hearlier _hage
    have hinitial : F.standard_initial = S.standard_initial := by
      rw [prior.standard_initial_eq, hp.setup_eq]
      exact S.setup_standard_initial_eq
    have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
      rw [hp.setup_eq]
      exact S.setup_standard_flow_eq
    have hmodel := (Proofs.M46.redecorateTo_standard_flow O prior.standard_initial_eq).trans hpflow
    exact transfer A hA F hinitial _ hmodel t hT hn i J _ e initial eta heta hetaSmall
      comparison hh s hs hst.2 hnear z' hz'
  · obtain ⟨N⟩ := hneck
    have he := S.setup.epsilon_pos
    have hsmall : S.setup.epsilon ≤ 1 / 200 :=
      S.setup.epsilon_le.trans (min_le_left _ _)
    have hge : S.calibration.beta * S.setup.epsilon / 3 < S.setup.epsilon := by
      nlinarith only [he, mul_lt_mul_of_pos_right S.calibration.beta_lt_half he]
    obtain ⟨A0, eta0, nearTime, V, hA0, heta0, hnearTime, hV, hzV, transfer⟩ :=
      exists_source_standard_evolving_neck_canonical_neighborhood
        S.cap_persistence.standard_cap S.setup.C htheta hv N hge (by linarith)
    refine ⟨A0, eta0, nearTime, 1, V, hA0, heta0, hnearTime, zero_lt_one, hV, hzV, ?_⟩
    intro A hA eta heta hetaSmall rNext _hrNext _hrLast
    refine ⟨p.Delta (Fin.last p.i), p.Delta_pos _, le_rfl, ?_⟩
    intro F O _hH prior _hadmissible _hpinch _next _overlap t hT hn i J e initial
      comparison _hzero _based hh s hs hst hJ hnear z' hz'
    dsimp only
    intro _hbase _hlarge _hthreshold _hearlier _hage
    have hinitial : F.standard_initial = S.standard_initial := by
      rw [prior.standard_initial_eq, hp.setup_eq]
      exact S.setup_standard_initial_eq
    have hpflow : HEq p.setup.standard_flow S.cap_persistence.standard_cap.flow := by
      rw [hp.setup_eq]
      exact S.setup_standard_flow_eq
    have hmodel := (Proofs.M46.redecorateTo_standard_flow O prior.standard_initial_eq).trans hpflow
    exact transfer A hA F hinitial _ hmodel t hT hn i J _ e initial eta heta hetaSmall
      comparison hh s hs hst.2 hJ hnear z' hz'
  · obtain ⟨N, hdisjoint, hage, _hscalar⟩ := hN
    exact initial_neighborhood N hdisjoint hage

end PoincareConjecture.M47
