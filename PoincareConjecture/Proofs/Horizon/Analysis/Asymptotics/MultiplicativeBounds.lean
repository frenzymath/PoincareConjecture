import Mathlib.Topology.Instances.ENNReal.Lemmas



set_option autoImplicit false

open Set Filter
open scoped ENNReal Topology

namespace Poincare.Analysis

theorem ennreal_le_of_forall_one_lt_pow_mul_add (n : ℕ) {x y z : ℝ≥0∞}
    (h : ∀ C : ℝ, 1 < C → x ≤ ENNReal.ofReal C ^ n * y + z) : x ≤ y + z := by
  have hp : Tendsto (fun C : ℝ => ENNReal.ofReal C ^ n) (𝓝 1) (𝓝 1) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one, one_pow] using
      ((ENNReal.continuous_pow n).comp ENNReal.continuous_ofReal).tendsto 1
  have hm : Tendsto (fun C : ℝ => ENNReal.ofReal C ^ n * y + z)
      (𝓝 1) (𝓝 (y + z)) := by
    simpa only [one_mul] using
      (ENNReal.Tendsto.mul hp (Or.inl one_ne_zero) tendsto_const_nhds
        (Or.inr ENNReal.one_ne_top)).add tendsto_const_nhds
  apply ge_of_tendsto (hm.mono_left (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds))
  exact (show ∀ᶠ C : ℝ in 𝓝[>] 1, 1 < C from self_mem_nhdsWithin).mono fun C hC => h C hC

theorem ennreal_le_of_forall_one_lt_pow_mul (n : ℕ) {x y : ℝ≥0∞}
    (h : ∀ C : ℝ, 1 < C → x ≤ ENNReal.ofReal C ^ n * y) : x ≤ y := by
  simpa only [add_zero] using ennreal_le_of_forall_one_lt_pow_mul_add n
    (z := 0) (fun C hC => by simpa only [add_zero] using h C hC)

end Poincare.Analysis
