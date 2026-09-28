import PoincareConjecture.Proofs.M51.EpochIndex
import PoincareConjecture.Proofs.M51.NumericalSchedule

set_option autoImplicit false

universe u

namespace PoincareConjecture
namespace GlobalSurgerySchedule

variable {K : MetricSurgeryConstants} (S : GlobalSurgerySchedule K)

noncomputable def parameters (delta : ℝ → ℝ)
    (hmono : AntitoneOn delta (Set.Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < delta t) : SurgeryParameters where
  epsilon := S.setup.epsilon
  C := S.setup.C
  epsilon_pos := S.setup.epsilon_pos
  epsilon_le := S.setup.epsilon_le.trans (min_le_left _ _)
  C_pos := S.setup.C_pos
  r := fun t => S.r (M51Numerical.epochIndex t)
  delta := delta
  h := fun t => S.setup.selector.h (delta t * S.r (M51Numerical.epochIndex t)) (delta t)
  kappa := fun t => S.kappa (M51Numerical.epochIndex t)
  r_pos := fun t _ => S.r_pos _
  delta_pos := hpos
  h_pos := fun t ht => S.setup.selector.h_pos _ _
    (mul_pos (hpos t ht) (S.r_pos _)) (hpos t ht)
  kappa_pos := fun t _ => S.kappa_pos _
  r_antitone := fun _ _ _ _ hst => S.r_antitone (M51Numerical.epochIndex_monotone hst)
  delta_antitone := hmono
  h_antitone := by
    intro s hs t ht hst
    have hd := hmono hs ht hst
    have hr := S.r_antitone (M51Numerical.epochIndex_monotone hst)
    have hprod := mul_le_mul hd hr (S.r_pos _).le (hpos s hs).le
    exact (S.setup.selector.h_mono_delta _ (mul_pos (hpos t ht) (S.r_pos _)).le
      (hpos t ht).le (hpos s hs).le hd).trans
      (S.setup.selector.h_mono_rho _ (hpos s hs).le
        (mul_pos (hpos t ht) (S.r_pos _)).le
        (mul_pos (hpos s hs) (S.r_pos _)).le hprod)
  kappa_antitone := fun _ _ _ _ hst =>
    S.kappa_antitone (M51Numerical.epochIndex_monotone hst)
  r_le_epsilon := fun t _ => S.r_le_epsilon _
  h_le := by
    intro t ht
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
      S.setup.selector.h_le (delta t * S.r (M51Numerical.epochIndex t)) (delta t)
        (mul_pos (hpos t ht) (S.r_pos _)) (hpos t ht)

variable (delta : ℝ → ℝ) (hmono : AntitoneOn delta (Set.Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < delta t)

@[simp] theorem parameters_epsilon :
    (S.parameters delta hmono hpos).epsilon = S.setup.epsilon := rfl

@[simp] theorem parameters_C : (S.parameters delta hmono hpos).C = S.setup.C := rfl

@[simp] theorem parameters_delta : (S.parameters delta hmono hpos).delta = delta := rfl

theorem parameters_height (t : ℝ) :
    (S.parameters delta hmono hpos).h t = S.setup.selector.h
      (delta t * (S.parameters delta hmono hpos).r t) (delta t) := rfl

theorem parameters_r {t : ℝ} {j : ℕ} (ht : t ∈ surgeryEpochEntry j) :
    (S.parameters delta hmono hpos).r t = S.r j := by
  change S.r (M51Numerical.epochIndex t) = S.r j
  rw [M51Numerical.epochIndex_of_mem ht]

theorem parameters_kappa {t : ℝ} {j : ℕ} (ht : t ∈ surgeryEpochEntry j) :
    (S.parameters delta hmono hpos).kappa t = S.kappa j := by
  change S.kappa (M51Numerical.epochIndex t) = S.kappa j
  rw [M51Numerical.epochIndex_of_mem ht]

@[simp] theorem parameters_r_zero :
    (S.parameters delta hmono hpos).r 0 = S.setup.epsilon := by
  change S.r (M51Numerical.epochIndex 0) = S.setup.epsilon
  rw [M51Numerical.epochIndex_zero, S.r_zero]

theorem parameters_agreement
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t → delta t ≤ S.Delta j)
    {t : ℝ} {j : ℕ} (ht : t ∈ surgeryEpochEntry j) (ht0 : 0 ≤ t) :
    let P := S.parameters delta hmono hpos
    P.r t = S.r j ∧ P.kappa t = S.kappa j ∧ P.delta t ≤ S.Delta j ∧
      P.h t = S.setup.selector.h (P.delta t * P.r t) (P.delta t) :=
  ⟨S.parameters_r delta hmono hpos ht, S.parameters_kappa delta hmono hpos ht,
    hcut j t ht ht0, S.parameters_height delta hmono hpos t⟩

end GlobalSurgerySchedule

namespace M51Numerical

theorem parameters_initial_height (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S) (C : RepairedCanonicalInductionData S N)
    (control : ℝ → ℝ) (hmono : AntitoneOn control (Set.Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < control t) (hcut : control 0 ≤ S.Delta0) :
    ((schedule S N C).parameters control hmono hpos).h 0 ≤
      S.constants.R₀ ^ (-1 / 2 : ℝ) := by
  have heps := S.setup.epsilon_pos
  have hdelta : 0 < S.Delta0 := by
    simpa only [delta_zero] using delta_pos S N C 0
  have hp := hpos 0 le_rfl
  change S.setup.selector.h (control 0 * r S N C (epochIndex 0)) (control 0) ≤ _
  rw [epochIndex_zero, r_zero]
  apply le_trans ?_ S.calibration.selector_initial_bound
  exact (S.setup.selector.h_mono_delta _ (mul_pos hp heps).le
    hp.le hdelta.le hcut).trans
    (S.setup.selector.h_mono_rho _ hdelta.le (mul_pos hp heps).le
      (mul_pos hdelta heps).le (mul_le_mul_of_nonneg_right hcut heps.le))

end M51Numerical
end PoincareConjecture
