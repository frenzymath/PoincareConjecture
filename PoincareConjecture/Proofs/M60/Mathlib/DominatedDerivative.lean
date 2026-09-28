import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence











set_option autoImplicit false

open MeasureTheory Filter Set
open scoped Topology

namespace PoincareConjecture.M60



theorem hasDerivWithinAt_integral_of_dominated_lipschitz
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {F : ℝ → X → ℝ} {F' bound : X → ℝ} {J : Set ℝ} {t : ℝ}
    [NeBot (𝓝[J \ {t}] t)]
    (hF : ∀ s : ℝ, Integrable (F s) mu) (hbound : Integrable bound mu)
    (hlip : ∀ᵐ x ∂mu, ∀ s ∈ J, ‖F s x - F t x‖ ≤ bound x * ‖s - t‖)
    (hdiff : ∀ᵐ x ∂mu, HasDerivWithinAt (fun s => F s x) (F' x) J t) :
    Integrable F' mu ∧
      HasDerivWithinAt (fun s => ∫ x, F s x ∂mu) (∫ x, F' x ∂mu) J t := by
  let Q := fun s x => slope (fun r => F r x) t s
  have hmeas (s : ℝ) : AEStronglyMeasurable (Q s) mu := by
    exact ((hF s).aestronglyMeasurable.sub (hF t).aestronglyMeasurable).const_smul (s - t)⁻¹
  have hlim : ∀ᵐ x ∂mu, Tendsto (fun s => Q s x) (𝓝[J \ {t}] t) (𝓝 (F' x)) :=
    hdiff.mono fun _ hx => hasDerivWithinAt_iff_tendsto_slope.mp hx
  have hquot (x : X) (hx : ∀ s ∈ J, ‖F s x - F t x‖ ≤ bound x * ‖s - t‖)
      {s : ℝ} (hs : s ∈ J \ {t}) : ‖Q s x‖ ≤ bound x := by
    have hst : s - t ≠ 0 := sub_ne_zero.mpr hs.2
    simp only [Q, slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv,
      ← div_eq_inv_mul]
    exact (div_le_iff₀ (abs_pos.mpr hst)).mpr (hx s hs.1)
  have hderiv_meas : AEStronglyMeasurable F' mu :=
    aestronglyMeasurable_of_tendsto_ae (𝓝[J \ {t}] t) hmeas hlim
  have hderiv_bound : ∀ᵐ x ∂mu, ‖F' x‖ ≤ bound x := by
    filter_upwards [hlip, hlim] with x hx hlimit
    apply le_of_tendsto hlimit.norm
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hquot x hx hs
  refine ⟨hbound.mono' hderiv_meas hderiv_bound, ?_⟩
  have hlimit := tendsto_integral_filter_of_dominated_convergence bound
    (Filter.Eventually.of_forall hmeas)
    (show ∀ᶠ s in 𝓝[J \ {t}] t, ∀ᵐ x ∂mu, ‖Q s x‖ ≤ bound x from by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hlip.mono fun x hx => hquot x hx hs)
    hbound hlim
  have hswap (s : ℝ) : (∫ x, Q s x ∂mu) = slope (fun r => ∫ x, F r x ∂mu) t s := by
    simp only [Q, slope_def_module, integral_smul, integral_sub (hF s) (hF t)]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  simpa only [hswap] using hlimit

end PoincareConjecture.M60
