import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecificLimits.Basic












noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture





theorem m64CompactUniform_integral_pairing_tendsto
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {mu : Measure X}
    {K : Set Y} (hK : IsCompact K) {q : X → Y} (hq : Measurable q)
    (hqK : ∀ᵐ x ∂mu, q x ∈ K) {w : X → ℝ} (hw : Integrable w mu)
    {g : ℕ → Y → ℝ} {f : Y → ℝ}
    (hg : ∀ j, Continuous (g j)) (hf : Continuous f)
    (hclose : ∀ j, ∀ y ∈ K, dist (g j y) (f y) ≤ (1 / 2 : ℝ) ^ j) :
    Tendsto (fun j => ∫ x, g j (q x) * w x ∂mu) atTop
      (𝓝 (∫ x, f (q x) * w x ∂mu)) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hpow : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply tendsto_integral_of_dominated_convergence (fun x => (1 + B) * ‖w x‖)
  · intro j
    exact ((hg j).measurable.comp hq).aestronglyMeasurable.mul hw.aestronglyMeasurable
  · exact hw.norm.const_mul (1 + B)
  · intro j
    filter_upwards [hqK] with x hx
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖g j (q x)‖ ≤ ‖g j (q x) - f (q x)‖ + ‖f (q x)‖ := norm_le_norm_sub_add _ _
      _ ≤ (1 / 2 : ℝ) ^ j + B := add_le_add (by
        simpa only [dist_eq_norm] using hclose j (q x) hx) (hB _ hx)
      _ ≤ 1 + B := add_le_add
        (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (n := j)) le_rfl
  · filter_upwards [hqK] with x hx
    have hdist : Tendsto (fun j => dist (g j (q x)) (f (q x))) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun j => hclose j (q x) hx) hpow
    exact (tendsto_iff_dist_tendsto_zero.mpr hdist).mul_const (w x)

end PoincareConjecture
