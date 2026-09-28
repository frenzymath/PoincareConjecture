import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourcePointwiseCanonical









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M47



theorem exists_source_standard_canonical_neighborhood
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {theta v : ℝ} (htheta : theta < 1) (hv : v ∈ Icc 0 theta)
    (z : StandardCapSpace) :
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
  exact exists_source_standard_canonical_neighborhood_of_initial S p hp htheta hv z
    (fun N hdisjoint hshort =>
      exists_source_standard_initial_neck_canonical_neighborhood
        P S B p hp htheta hv N hdisjoint hshort)

end PoincareConjecture.M47
