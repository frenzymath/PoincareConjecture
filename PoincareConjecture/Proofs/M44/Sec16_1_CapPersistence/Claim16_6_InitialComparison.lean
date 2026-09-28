import PoincareConjecture.Definitions.Ch16.CapPersistence
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Filter
open scoped Topology

universe u

namespace PoincareConjecture

theorem exists_initial_cap_comparison_cutoff (K : MetricSurgeryConstants)
    {A tolerance : ℝ} (hA : 0 < A) (htolerance : 0 < tolerance) (k : ℕ) :
    ∃ eta : ℝ, 0 < eta ∧ eta < tolerance ∧ A < eta⁻¹ ∧ k ≤ ⌊eta⁻¹⌋₊ ∧
      ∃ deltaBar : ℝ, 0 < deltaBar ∧
        ∀ (F : SurgeryFlowData.{u}), F.local_constants = K →
          ∀ (t : ℝ) (hT : t ∈ F.surgery_times)
            [Nonempty (F.slice t).carrier],
            F.parameters.delta t ≤ deltaBar →
            ∀ i : Fin (F.event t hT).cap_count,
              Nonempty (SurgeryCapClose F.standard_initial
                ((F.event t hT).local_result i).output
                ((F.event t hT).local_result i).metric
                ((F.event t hT).local_result i).tip
                (((F.event t hT).necks i).neck.scale) eta) := by
  let eta := min (tolerance / 2) (A + (k : ℝ) + 1)⁻¹
  have hden : 0 < A + (k : ℝ) + 1 := by positivity
  have heta : 0 < eta := lt_min (by positivity) (inv_pos.mpr hden)
  have hetol : eta < tolerance :=
    (min_le_left _ _).trans_lt (by linarith)
  have hinv : A + (k : ℝ) + 1 ≤ eta⁻¹ := by
    have h := one_div_le_one_div_of_le heta (min_le_right _ _)
    simpa only [one_div, inv_inv] using h
  refine ⟨eta, heta, hetol, ?_, ?_, K.comparison_delta eta,
    K.comparison_delta_pos eta heta, ?_⟩
  · linarith [Nat.cast_nonneg (α := ℝ) k]
  · exact (Nat.le_floor_iff (inv_pos.mpr heta).le).mpr (by linarith)
  · intro F hK t hT _ hdelta i
    apply ((F.event t hT).local_result i).standard_close eta heta
    rw [(F.event t hT).neck_delta i, hK]
    exact hdelta

theorem SurgeryParameters.height_le_delta_sq_mul_epsilon (P : SurgeryParameters)
    {t : ℝ} (ht : 0 ≤ t) : P.h t ≤ P.delta t ^ 2 * P.epsilon :=
  (P.h_le t ht).trans
    (mul_le_mul_of_nonneg_left (P.r_le_epsilon t ht) (sq_nonneg _))

theorem surgery_delta_tendsto_zero
    (F : ℕ → SurgeryFlowData.{u}) (t : ℕ → ℝ)
    (ht : ∀ n, 0 ≤ t n)
    (hdelta : ∀ n, (F n).parameters.delta (t n) ≤ 1 / ((n : ℝ) + 1)) :
    Tendsto (fun n => (F n).parameters.delta (t n)) atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n => ((F n).parameters.delta_pos (t n) (ht n)).le) hdelta

theorem surgery_height_tendsto_zero
    (F : ℕ → SurgeryFlowData.{u}) (t : ℕ → ℝ) {epsilon : ℝ}
    (ht : ∀ n, 0 ≤ t n)
    (hepsilon : ∀ n, (F n).parameters.epsilon = epsilon)
    (hdelta : Tendsto (fun n => (F n).parameters.delta (t n)) atTop (𝓝 0)) :
    Tendsto (fun n => (F n).parameters.h (t n)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n => (F n).parameters.delta (t n) ^ 2 * epsilon)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul] using
      (hdelta.pow 2).mul_const epsilon
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => ((F n).parameters.h_pos (t n) (ht n)).le)
  intro n
  simpa only [hepsilon n] using
    (F n).parameters.height_le_delta_sq_mul_epsilon (ht n)

end PoincareConjecture
