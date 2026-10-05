import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.Algebra.Order.Field

/-!
# Liouville vanishing for a stereographic decay bound

The Hopf coefficient of a C1 sphere has fourth-order decay in the
standard plane coordinate. Liouville's theorem then makes an entire
coefficient vanish, as required by SU Lemma 1.5 and MT Lemma 18.10.
-/

set_option autoImplicit false

open Set Filter Bornology
open scoped Topology

namespace PoincareMT.M60

/-- An entire complex function with the stereographic quartic decay
bound is zero. Source: SU Lemma 1.5, p. 5; MT Lemma 18.10, pp. 424-426. -/
theorem complex_eq_zero_of_quartic_decay {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, ‖f z‖ ≤ C / (‖z‖ ^ 2 + 4) ^ 2) (z : ℂ) : f z = 0 := by
  have hb : IsBounded (range f) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨C, ?_⟩
    rintro _ ⟨w, rfl⟩
    refine (hbound w).trans (div_le_self hC ?_)
    nlinarith [sq_nonneg ‖w‖]
  have hden : Tendsto (fun r : ℝ => (r ^ 2 + 4) ^ 2) atTop atTop := by
    apply tendsto_atTop_mono (f := fun r : ℝ => r) _ tendsto_id
    intro r
    nlinarith [sq_nonneg (r - 1), sq_nonneg r, sq_nonneg (r ^ 2 + 3)]
  have hlim : Tendsto (fun r : ℝ => C / (r ^ 2 + 4) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  apply norm_le_zero_iff.mp
  apply le_of_tendsto_of_tendsto (b := atTop) tendsto_const_nhds hlim
  exact Eventually.of_forall fun r : ℝ => by
    rw [hf.apply_eq_apply_of_bounded hb z (r : ℂ)]
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hbound (r : ℂ)

end PoincareMT.M60
