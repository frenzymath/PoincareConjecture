import PoincareConjecture.Proofs.M03.Existence.SpectralModeNative

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology BigOperators

noncomputable section

namespace PoincareConjecture

variable {iota : Type*}

def spectralGeneratorEnergy (lambda : ℝ) (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, (lambda * spectralMode lambda 0 f t) ^ 2

def spectralForcingEnergy (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, (f t) ^ 2

def spectralDefectGeneratorEnergy (lambda : ℝ) (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T,
      (f t - lambda * spectralMode lambda 0 f t) ^ 2) +
    spectralGeneratorEnergy lambda f T

theorem finite_spectralMode_generator_energy_le
    (s : Finset iota) (lambda : iota → ℝ) (f : iota → ℝ → ℝ)
    {T : ℝ} (hT : 0 ≤ T)
    (hlambda : ∀ i, 0 ≤ lambda i)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) T)) :
    (∑ i ∈ s, spectralGeneratorEnergy (lambda i) (f i) T) ≤
      ∑ i ∈ s, spectralForcingEnergy (f i) T := by
  apply Finset.sum_le_sum
  intro i hi
  dsimp [spectralGeneratorEnergy, spectralForcingEnergy]
  exact spectralMode_zero_initial_generator_energy_le
    (lambda := lambda i) (T := T) (f := f i) (hlambda i) hT (hf i)

theorem finite_spectralMode_defect_generator_energy_le
    (s : Finset iota) (lambda : iota → ℝ) (f : iota → ℝ → ℝ)
    {T : ℝ} (hT : 0 ≤ T)
    (hlambda : ∀ i, 0 ≤ lambda i)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) T)) :
    (∑ i ∈ s, spectralDefectGeneratorEnergy (lambda i) (f i) T) ≤
      ∑ i ∈ s, spectralForcingEnergy (f i) T := by
  apply Finset.sum_le_sum
  intro i hi
  dsimp [spectralDefectGeneratorEnergy, spectralGeneratorEnergy,
    spectralForcingEnergy]
  simpa using (spectralMode_energy_le
    (lambda := lambda i) (c := 0) (T := T) (f := f i)
    (hlambda i) hT (hf i))

theorem finite_spectralMode_generator_energy_mono
    {s r : Finset iota} (hsr : s ⊆ r)
    (lambda : iota → ℝ) (f : iota → ℝ → ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hlambda : ∀ i, 0 ≤ lambda i)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) T)) :
    (∑ i ∈ s, spectralGeneratorEnergy (lambda i) (f i) T) ≤
      ∑ i ∈ r, spectralGeneratorEnergy (lambda i) (f i) T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hsr (fun i hi hnot => by
    dsimp [spectralGeneratorEnergy]
    exact intervalIntegral.integral_nonneg_of_forall hT
      (fun _ => sq_nonneg _))

end PoincareConjecture

end
