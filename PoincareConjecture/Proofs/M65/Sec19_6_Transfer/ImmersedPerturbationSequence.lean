import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace PoincareConjecture.M65Perturbation

theorem exists_small_generic_parameter {N : ℕ} (Bad : Set (Fin N → ℝ))
    (hBad : volume Bad = 0) (r : ℝ) (hr : 0 < r) :
    ∃ p : Fin N → ℝ, ‖p‖ < r ∧ p ∉ Bad := by
  by_contra h
  push Not at h
  have hsub : ball (0 : Fin N → ℝ) r ⊆ Bad := by
    intro p hp
    exact h p (by simpa only [mem_ball, dist_zero_right] using hp)
  have hpos := Metric.measure_ball_pos volume (0 : Fin N → ℝ) hr
  exact (not_le_of_gt hpos) (hBad ▸ measure_mono hsub)

theorem exists_generic_parameter_sequence {N : ℕ} (Bad : Set (Fin N → ℝ))
    (hBad : volume Bad = 0) (delta : ℝ) (hdelta : 0 < delta)
    (eta : ℕ → ℝ) (heta : ∀ n, 0 < eta n) :
    ∃ p : ℕ → (Fin N → ℝ),
      (∀ n, ‖p n‖ < min delta (min (eta n) (1 / ((n : ℝ) + 1))) ∧ p n ∉ Bad) ∧
      Tendsto p atTop (𝓝 0) := by
  have hex (n : ℕ) := exists_small_generic_parameter Bad hBad
    (min delta (min (eta n) (1 / ((n : ℝ) + 1))))
    (lt_min hdelta (lt_min (heta n) (by positivity)))
  choose p hp using hex
  refine ⟨p, hp, tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  exact squeeze_zero (fun n => norm_nonneg (p n))
    (fun n => ((hp n).1.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end PoincareConjecture.M65Perturbation
