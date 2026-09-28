import PoincareConjecture.Definitions.M45ControlledSchedules
import PoincareConjecture.Proofs.M45.KappaConstants
import PoincareConjecture.Proofs.M28.Sec10_1_Pinching








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RepairedControlledSchedulesData

variable (S : RepairedControlledSchedulesData.{u})




theorem appendixA_accuracy {epsilon : ℝ}
    (he : epsilon ≤ S.calibration.common_epsilon) :
    terminalAccuracyFactor * epsilon ≤ S.calibration.appendixA.epsilon₀ :=
  (mul_le_mul_of_nonneg_left he terminalAccuracyFactor_pos.le).trans
    S.calibration.terminal_common_epsilon_le_appendixA

theorem setup_appendixA_accuracy :
    terminalAccuracyFactor * S.setup.epsilon ≤ S.calibration.appendixA.epsilon₀ := by
  apply S.appendixA_accuracy
  linarith [S.calibration.two_epsilon_le_common, S.setup.epsilon_pos]



theorem boundedDistanceDoubled (a : ℝ) (ha : 0 ≤ a) :
    ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
      ∀ F : GeneralizedRicciFlowData.{u},
        F.interval ⊆ Set.Ici 0 → generalizedHamiltonIveyPinched F →
        ∀ t, t ∈ F.interval → ∀ x : (F.slice t).carrier,
          D₀ ≤ F.scalar ⟨t, x⟩ →
          generalizedEarlierStrongCanonicalNeighborhoods F
            (2 * S.setup.epsilon) (2 * S.setup.C) t x →
          RepairedBoundedDistanceEstimate F a D t x := by
  exact S.calibration.bounded_distance (2 * S.setup.epsilon)
    (mul_pos (by norm_num) S.setup.epsilon_pos)
    S.calibration.two_epsilon_le_bounded_distance (2 * S.setup.C)
    (mul_pos (by norm_num) S.setup.C_pos) a ha



theorem boundedDistanceDoubledDense (a : ℝ) (ha : 0 ≤ a) :
    ∃ D₀ D : ℝ, 0 < D₀ ∧ 0 < D ∧
      ∀ F : GeneralizedRicciFlowData.{u},
        F.interval ⊆ Set.Ici 0 → generalizedHamiltonIveyPinched F →
        ∀ t, t ∈ F.interval → ∀ x : (F.slice t).carrier,
          D₀ ≤ F.scalar ⟨t, x⟩ →
          generalizedEarlierDenseStrongCanonicalNeighborhoods F
            (2 * S.setup.epsilon) (2 * S.setup.C) t x →
          RepairedBoundedDistanceEstimate F a D t x := by
  obtain ⟨D₀, D, hD₀, hD, estimate⟩ :=
    S.calibration.bounded_distance_dense (2 * S.setup.epsilon)
      (mul_pos (by norm_num) S.setup.epsilon_pos)
      S.calibration.two_epsilon_le_bounded_distance (2 * S.setup.C)
      (mul_pos (by norm_num) S.setup.C_pos) a ha
  refine ⟨D₀, D, hD₀, hD, ?_⟩
  intro F _hinterval hpinched t ht x hx hcanonical
  exact estimate F hpinched.weak t ht x hx hcanonical

section Ancient

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]


theorem kappaCanonical (K : AncientKappaSolution 3 M)
    (hK : ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K))
    (eta : ℝ) (heta : eta = S.setup.epsilon ∨ eta = 2 * S.setup.epsilon)
    (t : ℝ) (ht : t ≤ 0) (x : M) :
    M27StrongCanonicalNeighborhood K t x eta S.setup.C := by
  apply (S.calibration.kappa_canonical K hK eta heta t ht x).mono_constant
  rw [S.calibration.setup_C_eq]
  exact le_max_left _ _


theorem kappaDerivatives (K : AncientKappaSolution 3 M) :
    M27ScalarDerivativeBounds K S.setup.C := by
  apply (S.calibration.kappa_derivatives K).mono_constant
  rw [S.calibration.setup_C_eq]
  exact le_max_left _ _

end Ancient


theorem selector_deep_horn (rho delta : ℝ) (hr : 0 < rho) (hd : 0 < delta) :
    S.setup.selector.h rho delta ≤ min (rho * delta) (rho / (2 * S.setup.C)) := by
  rw [S.calibration.selector_eq]
  exact le_min (S.calibration.horn_selector.h_le rho delta hr hd)
    (S.calibration.horn_selector.h_upper rho delta hr hd)


theorem standard_canonical_source : ∃ beta Cstd : ℝ,
    0 < beta ∧ beta < 1 / 2 ∧ 0 < Cstd ∧ Cstd ≤ S.setup.C ∧
      ∀ t ∈ Set.Ico 0 S.cap_persistence.standard_cap.flow.base.lifetime,
        ∀ x : StandardCapSpace,
          StandardCanonicalAlternative S.cap_persistence.standard_cap.atlas
            S.cap_persistence.standard_cap.flow t x
            (beta * S.setup.epsilon / 3) Cstd := by
  refine ⟨S.calibration.beta, S.calibration.Cstandard,
    S.calibration.beta_pos, S.calibration.beta_lt_half,
    S.calibration.Cstandard_pos, ?_, S.calibration.canonical_source⟩
  rw [S.calibration.setup_C_eq]
  exact (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 from zero_le_one)).trans
    (le_max_right _ _)


theorem standardCanonical (t : ℝ)
    (ht : t ∈ Set.Ico 0 S.cap_persistence.standard_cap.flow.base.lifetime)
    (x : StandardCapSpace) :
    M45StandardCanonicalAlternative S.cap_persistence.standard_cap.atlas
      S.cap_persistence.standard_cap.flow t x
      (S.calibration.beta * S.setup.epsilon / 3) S.setup.C := by
  have hC : S.calibration.Cstandard + 1 ≤ S.setup.C := by
    rw [S.calibration.setup_C_eq]
    exact le_max_right _ _
  cases S.calibration.canonical_source t ht x with
  | cap N =>
    obtain ⟨R⟩ := S.calibration.cap_refinement t x N
    exact .cap R.cap R.epsilon_eq (R.constant_eq.le.trans hC)
      R.connection_eq R.model_eq R.contains
  | initial_neck N hdisjoint => exact .initial_neck N hdisjoint
  | evolving_neck N => exact .evolving_neck N

end PoincareConjecture.RepairedControlledSchedulesData
