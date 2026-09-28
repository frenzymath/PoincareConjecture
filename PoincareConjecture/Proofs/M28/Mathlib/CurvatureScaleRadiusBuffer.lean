import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M28

theorem eventually_curvatureScale_radius_mem_Icc
    {S X : Type*} [MetricSpace X]
    (E : UniformSpace.Completion X) (x : ℕ → S → X) (q : ℕ → X) (R : ℕ → ℝ)
    (hRpos : ∀ i, 0 < R i) {a m : ℝ} (hm : 0 < m) (ham : a ≤ m)
    (hcenter : Tendsto
      (fun i => Real.sqrt (R i) * dist (q i : UniformSpace.Completion X) E)
      atTop (𝓝 m))
    (hshort : ∀ᶠ i in atTop, ∀ u : S,
      Real.sqrt (R i) * dist (x i u) (q i) ≤ 3 * a / 64) :
    ∀ᶠ i in atTop, ∀ u : S,
      dist (x i u : UniformSpace.Completion X) E / (Real.sqrt (R i))⁻¹ ∈
        Icc (3 * m / 4) (5 * m / 4) := by
  have hcenterLower : ∀ᶠ i in atTop,
      7 * m / 8 < Real.sqrt (R i) * dist (q i : UniformSpace.Completion X) E :=
    (tendsto_order.mp hcenter).1 (7 * m / 8) (by linarith only [hm])
  have hcenterUpper : ∀ᶠ i in atTop,
      Real.sqrt (R i) * dist (q i : UniformSpace.Completion X) E < 9 * m / 8 :=
    (tendsto_order.mp hcenter).2 (9 * m / 8) (by linarith only [hm])
  filter_upwards [hcenterLower, hcenterUpper, hshort] with i hlow hhigh hshort
  intro u
  have hradius :
      |dist (x i u : UniformSpace.Completion X) E -
        dist (q i : UniformSpace.Completion X) E| ≤ dist (x i u) (q i) := by
    simpa only [UniformSpace.Completion.dist_eq] using
      abs_dist_sub_le (x i u : UniformSpace.Completion X)
        (q i : UniformSpace.Completion X) E
  have hsqrt : 0 ≤ Real.sqrt (R i) := (Real.sqrt_pos.mpr (hRpos i)).le
  have hlowRadius := mul_le_mul_of_nonneg_left (abs_le.mp hradius).1 hsqrt
  have hhighRadius := mul_le_mul_of_nonneg_left (abs_le.mp hradius).2 hsqrt
  have hcost : Real.sqrt (R i) * dist (x i u) (q i) ≤ m / 8 :=
    (hshort u).trans (by linarith only [ham, hm])
  rw [div_inv_eq_mul]
  constructor <;> nlinarith only [hlow, hhigh, hlowRadius, hhighRadius, hcost]

end PoincareConjecture.M28
