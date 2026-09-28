import PoincareConjecture.Definitions.Ch16.ControlledSurgery
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareConjecture.M44

theorem height_le_delta_sq_epsilon (P : SurgeryParameters) {t : ℝ} (ht : 0 ≤ t) :
    P.h t ≤ P.delta t ^ 2 * P.epsilon :=
  (P.h_le t ht).trans (mul_le_mul_of_nonneg_left (P.r_le_epsilon t ht) (sq_nonneg _))

theorem exists_surgery_height_cutoff {epsilon R : ℝ} (hepsilon : 0 < epsilon) (hR : 0 < R) :
    ∃ deltaBar : ℝ, 0 < deltaBar ∧ ∀ (P : SurgeryParameters),
      P.epsilon = epsilon → ∀ t : ℝ, 0 ≤ t → P.delta t ≤ deltaBar → P.h t ≤ R := by
  refine ⟨min 1 (R / (epsilon + 1)),
    lt_min zero_lt_one (div_pos hR (by linarith)), ?_⟩
  intro P heq t ht hdelta
  have hdpos := P.delta_pos t ht
  have hd1 := hdelta.trans (min_le_left _ _)
  have hdR : P.delta t * (epsilon + 1) ≤ R :=
    (le_div_iff₀ (by linarith : 0 < epsilon + 1)).mp
      (hdelta.trans (min_le_right _ _))
  have hsq : P.delta t ^ 2 ≤ P.delta t := by nlinarith
  have hh := height_le_delta_sq_epsilon P ht
  rw [heq] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right hsq hepsilon.le).trans (by linarith))

theorem exists_surgery_normalization_cutoff {epsilon r : ℝ}
    (hepsilon : 0 < epsilon) (hr : 0 < r) :
    ∃ deltaBar : ℝ, 0 < deltaBar ∧ ∀ (P : SurgeryParameters),
      P.epsilon = epsilon → ∀ t : ℝ, 0 ≤ t → P.delta t ≤ deltaBar →
        P.h t ^ 2 ≤ 1 ∧ (P.h t / r) ^ 2 ≤ 1 := by
  obtain ⟨deltaBar, hd, hbound⟩ := exists_surgery_height_cutoff hepsilon (lt_min zero_lt_one hr)
  refine ⟨deltaBar, hd, ?_⟩
  intro P heq t ht hdelta
  have hh := hbound P heq t ht hdelta
  have hh0 := P.h_pos t ht
  have hh1 := hh.trans (min_le_left _ _)
  have hhr := hh.trans (min_le_right _ _)
  have hratio : P.h t / r ≤ 1 := (div_le_one hr).mpr hhr
  have hratio0 : 0 ≤ P.h t / r := (div_pos hh0 hr).le
  constructor <;> nlinarith

theorem surgery_height_tendsto_zero {ι : Type*} {l : Filter ι}
    (P : ι → SurgeryParameters) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    {epsilon : ℝ} (hepsilon : ∀ i, (P i).epsilon ≤ epsilon)
    (hdelta : Tendsto (fun i => (P i).delta (t i)) l (𝓝 0)) :
    Tendsto (fun i => (P i).h (t i)) l (𝓝 0) := by
  apply squeeze_zero (fun i => ((P i).h_pos (t i) (ht i)).le)
    (fun i => (height_le_delta_sq_epsilon (P i) (ht i)).trans
      (mul_le_mul_of_nonneg_left (hepsilon i) (sq_nonneg _)))
  simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0), zero_mul] using
    (hdelta.pow 2).mul_const epsilon

end PoincareConjecture.M44
