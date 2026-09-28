import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open Filter Topology

namespace Poincare.CurvatureIntegral

theorem exists_positive_slab_parameters {r : ℝ} (hr : 0 < r) (K : ℝ) :
    ∃ T ε : ℝ, 0 < T ∧ T < r / 4 ∧ 0 < ε ∧ ε < r / 8 ∧
      2 * ε / T + (4 / (3 * (r / 2 - T)) + K * (3 * r + T) / 4 + 1) * T / 2 <
        1 / 4 := by
  let E : ℝ → ℝ := fun t =>
    (4 / (3 * (r / 2 - t)) + K * (3 * r + t) / 4 + 1) * t / 2
  have hden : 3 * (r / 2 - 0) ≠ 0 := by
    apply ne_of_gt
    linarith
  have hE : ContinuousAt E 0 := by
    dsimp only [E]
    fun_prop (disch := first | exact hden | positivity)
  have hE0 : E 0 = 0 := by simp [E]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), E t < 1 / 8 :=
    hE.eventually_lt continuousAt_const (by rw [hE0]; norm_num)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let T := min (δ / 2) (r / 8)
  have hT : 0 < T := lt_min (half_pos hδ) (by positivity)
  have hTδ : T < δ := (min_le_left _ _).trans_lt (by linarith)
  have hTr : T < r / 4 := (min_le_right _ _).trans_lt (by linarith)
  have hET : E T < 1 / 8 := by
    apply hball
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hT] using hTδ
  let ε := min (r / 16) (T / 32)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεr : ε < r / 8 := (min_le_left _ _).trans_lt (by linarith)
  have herr : 2 * ε / T ≤ 1 / 16 := by
    apply (div_le_iff₀ hT).mpr
    have hle : ε ≤ T / 32 := min_le_right _ _
    linarith
  refine ⟨T, ε, hT, hTr, hε, hεr, ?_⟩
  change 2 * ε / T + E T < 1 / 4
  linarith only [herr, hET]

end Poincare.CurvatureIntegral
