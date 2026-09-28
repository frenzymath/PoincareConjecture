import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.CompleteGeometry

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Riemannian.Soul

variable {M : Type*} [MetricSpace M]

theorem IsRay.eventually_rescaled_window_distance
    {ray : ℝ → M} (hray : IsRay ray)
    {scale : ℕ → ℝ} (hscale : ∀ k, 0 < scale k)
    (hescape : Tendsto (fun k => scale k * (k : ℝ)) atTop atTop)
    (s t : ℝ) :
    ∀ᶠ k in atTop,
      scale k * dist (ray ((k : ℝ) + s / scale k))
        (ray ((k : ℝ) + t / scale k)) = |s - t| := by
  have hparam (k : ℕ) (a : ℝ) (ha : |a| ≤ scale k * (k : ℝ)) :
      0 ≤ (k : ℝ) + a / scale k := by
    have hdiv : -(k : ℝ) ≤ a / scale k := (le_div_iff₀ (hscale k)).mpr (by
      nlinarith [neg_abs_le a])
    linarith
  filter_upwards [(tendsto_atTop.mp hescape) (max |s| |t|)] with k hk
  rw [hray (hparam k s ((le_max_left _ _).trans hk))
    (hparam k t ((le_max_right _ _).trans hk))]
  rw [show (k : ℝ) + s / scale k - ((k : ℝ) + t / scale k) =
      (s - t) / scale k by ring, abs_div, abs_of_pos (hscale k)]
  field_simp [(hscale k).ne']

end Poincare.Riemannian.Soul
