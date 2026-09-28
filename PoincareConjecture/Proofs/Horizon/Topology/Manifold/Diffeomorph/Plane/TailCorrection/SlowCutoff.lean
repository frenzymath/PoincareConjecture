import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.MetricSpace.ProperSpace

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Manifold.PlaneDiffeomorph

theorem exists_slow_cutoff (a M : ℝ) (hM : 0 ≤ M) :
    ∃ (η : ℝ → ℝ) (b : ℝ), a < b ∧ ContDiff ℝ ∞ η ∧
      (∀ x, η x ∈ Icc 0 1) ∧
      (∀ x, x ≤ a → η x = 0) ∧ (∀ x, b ≤ x → η x = 1) ∧
      ∀ x, |deriv η x| * M < 1 / 2 := by
  have hθ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hθd : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp hθ).2
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hθd.continuous.continuousOn (s := Icc (0 : ℝ) 1))
  let N : ℝ := max C 0
  have hN : 0 ≤ N := le_max_right _ _
  have hbound (x : ℝ) : |deriv Real.smoothTransition x| ≤ N := by
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · have hcx : |deriv Real.smoothTransition x| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC x hx
      exact hcx.trans (le_max_left _ _)
    · have hzero : deriv Real.smoothTransition x = 0 := by
        simp only [mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
            filter_upwards [eventually_lt_nhds hx] with y hy
            exact Real.smoothTransition.zero_of_nonpos hy.le
          exact heq.deriv_eq.trans (deriv_const x 0)
        · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
            filter_upwards [eventually_gt_nhds hx] with y hy
            exact Real.smoothTransition.one_of_one_le hy.le
          exact heq.deriv_eq.trans (deriv_const x 1)
      simpa only [hzero, abs_zero] using hN
  let w : ℝ := 2 * (M + 1) * (N + 1)
  have hw : 0 < w := by dsimp only [w]; positivity
  let η : ℝ → ℝ := fun x => Real.smoothTransition ((x - a) / w)
  have hη : ContDiff ℝ ∞ η := hθ.comp ((contDiff_id.sub contDiff_const).div_const w)
  have hηderiv (x : ℝ) :
      deriv η x = deriv Real.smoothTransition ((x - a) / w) / w := by
    have hd := ((hθ.differentiable (by simp)) ((x - a) / w)).hasDerivAt.comp x
      (((hasDerivAt_id x).sub_const a).div_const w)
    simpa only [η, Function.comp_def, id_eq, one_div, div_eq_mul_inv, one_mul] using hd.deriv
  refine ⟨η, a + w, by linarith, hη,
    fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, ?_, ?_, ?_⟩
  · intro x hx
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hx) hw.le)
  · intro x hx
    apply Real.smoothTransition.one_of_one_le
    exact (le_div_iff₀ hw).mpr (by linarith)
  · intro x
    rw [hηderiv, abs_div, abs_of_pos hw]
    calc
      |deriv Real.smoothTransition ((x - a) / w)| / w * M ≤ N / w * M :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hbound _) hw.le) hM
      _ < 1 / 2 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hw]
        dsimp only [w]
        nlinarith

end Poincare.Manifold.PlaneDiffeomorph
