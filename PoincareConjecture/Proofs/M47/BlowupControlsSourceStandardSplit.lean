import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialInterval
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialScalar
import PoincareConjecture.Definitions.M45ControlledSchedules










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M47



theorem standard_source_alternative_split (S : RepairedControlledSchedulesData.{u})
    {theta s : ℝ} (htheta : theta < 1) (hs : s ∈ Icc 0 theta) (z : StandardCapSpace) :
    Nonempty (StandardCapNeighborhood S.cap_persistence.standard_cap.atlas
      S.cap_persistence.standard_cap.flow s (S.calibration.beta * S.setup.epsilon / 3)
      S.calibration.Cstandard z) ∨
    Nonempty (StandardEvolvingNeck S.cap_persistence.standard_cap.atlas
      S.cap_persistence.standard_cap.flow s (S.calibration.beta * S.setup.epsilon / 3) z
      (Ioc (-(1 + S.calibration.beta * S.setup.epsilon / 3)) 0)) ∨
    ∃ N : StandardEvolvingNeck S.cap_persistence.standard_cap.atlas
        S.cap_persistence.standard_cap.flow s (S.calibration.beta * S.setup.epsilon / 3) z
        (Icc (-s * (S.cap_persistence.standard_cap.flow.connection s).scalarCurvature z) 0),
      Disjoint N.patch.carrier {y | S.standard_initial.metric.edist 0 y ≤
        ENNReal.ofReal (S.standard_initial.cylindrical_end.radius + 4)} ∧
      s * (S.cap_persistence.standard_cap.flow.connection s).scalarCurvature z <
        1 + S.calibration.beta * S.setup.epsilon / 3 ∧
      (S.cap_persistence.standard_cap.flow.connection s).scalarCurvature z < 4 := by
  have hlife : s ∈ Ico 0 S.cap_persistence.standard_cap.flow.base.lifetime := by
    rw [S.cap_persistence.standard_cap.lifetime_one]
    exact ⟨hs.1, hs.2.trans_lt htheta⟩
  have hsmall : S.setup.epsilon ≤ 1 / 200 := S.setup.epsilon_le.trans (min_le_left _ _)
  have hgamma : S.calibration.beta * S.setup.epsilon / 3 ≤ 1 / 200 := by
    have h := mul_le_mul S.calibration.beta_lt_half.le hsmall S.setup.epsilon_pos.le
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith only [h]
  rcases S.calibration.canonical_source s hlife z with N | ⟨N, hdisjoint⟩ | N
  · exact Or.inl ⟨N⟩
  · by_cases hlong : 1 + S.calibration.beta * S.setup.epsilon / 3 ≤
        s * (S.cap_persistence.standard_cap.flow.connection s).scalarCurvature z
    · exact Or.inr (Or.inl ⟨standardInitialNeckExtended N hlong⟩)
    · have hshort := lt_of_not_ge hlong
      exact Or.inr (Or.inr ⟨N, hdisjoint, hshort,
        (standard_initial_neck_birth_scale_lt_four N hgamma hdisjoint hshort).2⟩)
  · exact Or.inr (Or.inl ⟨N⟩)

end PoincareConjecture.M47
