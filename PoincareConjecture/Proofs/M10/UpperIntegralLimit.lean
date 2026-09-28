import Mathlib.MeasureTheory.Integral.DominatedConvergence










set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M10


theorem integral_limit_le_of_ae_upper_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a : ℕ → X → ℝ} {b c : X → ℝ} {I : ℝ}
    (ha : ∀ k, Integrable (a k) μ) (hb : Integrable b μ) (hc : Integrable c μ)
    (hupper : ∀ k, a k ≤ᵐ[μ] c)
    (hlim : ∀ᵐ x ∂μ, ∃ r : ℝ, Tendsto (fun k ↦ a k x) atTop (𝓝 r) ∧ r ≤ b x)
    (hint : Tendsto (fun k ↦ ∫ x, a k x ∂μ) atTop (𝓝 I)) :
    I ≤ ∫ x, b x ∂μ := by
  let G := fun k x ↦ max (b x) (a k x)
  have hGi (k : ℕ) : Integrable (G k) μ := hb.sup (ha k)
  have hbound (k : ℕ) : ∀ᵐ x ∂μ, ‖G k x‖ ≤ |b x| + |c x| := by
    filter_upwards [hupper k] with x hx
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · calc
        -(|b x| + |c x|) ≤ -|b x| := by linarith [abs_nonneg (c x)]
        _ ≤ b x := neg_abs_le _
        _ ≤ G k x := le_max_left _ _
    · apply max_le
      · linarith [le_abs_self (b x), abs_nonneg (c x)]
      · linarith [hx, le_abs_self (c x), abs_nonneg (b x)]
  have hGl : ∀ᵐ x ∂μ, Tendsto (fun k ↦ G k x) atTop (𝓝 (b x)) := by
    filter_upwards [hlim] with x hx
    obtain ⟨r, hr, hrb⟩ := hx
    have h := (tendsto_const_nhds (x := b x)).max hr
    simpa only [G, max_eq_left hrb] using h
  have hGint := tendsto_integral_of_dominated_convergence
    (fun x ↦ |b x| + |c x|) (fun k ↦ (hGi k).aestronglyMeasurable)
    (hb.abs.add hc.abs) hbound hGl
  apply le_of_tendsto_of_tendsto hint hGint
  exact Eventually.of_forall (fun k ↦ integral_mono_ae (ha k) (hGi k)
    (Eventually.of_forall (fun x ↦ le_max_right (b x) (a k x))))

end PoincareConjecture.M10
