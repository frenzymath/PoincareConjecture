import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false

open Filter Topology

namespace Poincare.Alexandrov

theorem exists_distance_increment_witness_of_local_ascent
    {X : Type*} [MetricSpace X] {p y : X} (hpy : p ≠ y) (K : ℝ)
    {c c' : ℝ} (hcc' : c < c')
    (hascent : ∀ s : ℝ, 0 < s → ∃ q : X, dist y q < s ∧
      c' * dist y q < dist p q - dist p y) :
    ∃ q : X, 0 < dist y q ∧ dist y q < dist p y ∧
      c < (dist p q - dist p y) / dist y q -
        (4 / (3 * (dist p y - dist y q)) + K * (dist p y + dist y q) / 4) *
          dist y q / 2 := by
  let a := dist p y
  have ha : 0 < a := dist_pos.mpr hpy
  let E : ℝ → ℝ := fun t => (4 / (3 * (a - t)) + K * (a + t) / 4) * t / 2
  have hE : ContinuousAt E 0 := by
    dsimp only [E]
    fun_prop (disch := positivity)
  have hE0 : E 0 = 0 := by simp [E]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), E t < c' - c :=
    hE.eventually_lt continuousAt_const (by rw [hE0]; linarith)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨q, hqsmall, hqgain⟩ := hascent (min r a) (lt_min hr ha)
  have hqpos : 0 < dist y q := by
    apply dist_pos.mpr
    intro hq
    subst q
    simp only [dist_self, mul_zero, sub_self, lt_self_iff_false] at hqgain
  have hqr : dist y q < r := hqsmall.trans_le (min_le_left _ _)
  have hqa : dist y q < a := hqsmall.trans_le (min_le_right _ _)
  have herror : E (dist y q) < c' - c := by
    apply hball
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hqpos] using hqr
  have hratio : c' < (dist p q - dist p y) / dist y q :=
    (lt_div_iff₀ hqpos).mpr hqgain
  refine ⟨q, hqpos, hqa, ?_⟩
  change c < (dist p q - dist p y) / dist y q - E (dist y q)
  linarith only [hratio, herror]

end Poincare.Alexandrov
