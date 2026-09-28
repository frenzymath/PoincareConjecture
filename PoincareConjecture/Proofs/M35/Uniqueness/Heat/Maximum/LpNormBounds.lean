import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic









set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

def lpPointNorm (f : Lp E 2 μ) : Lp ℝ 2 μ :=
  lipschitzWith_one_norm.compLp (norm_zero : ‖(0 : E)‖ = 0) f

theorem lpPointNorm_coe (f : Lp E 2 μ) : lpPointNorm f =ᵐ[μ] fun x => ‖f x‖ :=
  lipschitzWith_one_norm.coeFn_compLp (norm_zero : ‖(0 : E)‖ = 0) f

theorem norm_lpPointNorm (f : Lp E 2 μ) : ‖lpPointNorm f‖ = ‖f‖ := by
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [lpPointNorm_coe f] with x hx
    simp [hx]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [lpPointNorm_coe f] with x hx
    simp [hx]

theorem lp_norm_le_sum {ι : Type*} [Fintype ι]
    (f : Lp F 2 μ) (g : ι → Lp E 2 μ) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ ∑ i, a i * ‖g i x‖) :
    ‖f‖ ≤ ∑ i, a i * ‖g i‖ := by
  classical
  let h : Lp ℝ 2 μ := ∑ i, a i • lpPointNorm (g i)
  have he : h =ᵐ[μ] fun x => ∑ i, a i * ‖g i x‖ := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • lpPointNorm (g i)),
      ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (lpPointNorm (g i))),
      ae_all_iff.mpr (fun i => lpPointNorm_coe (g i))] with x hs hm hn
    change (∑ i, a i • lpPointNorm (g i)) x = _
    rw [hs]
    apply Finset.sum_congr rfl
    intro i _
    rw [hm i]
    change a i * lpPointNorm (g i) x = _
    rw [hn i]
  have hfh : ‖f‖ ≤ ‖h‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [he, hb] with x hx hb
    rw [hx, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ =>
      mul_nonneg (ha i) (norm_nonneg _))]
    exact hb
  apply hfh.trans
  calc
    ‖h‖ ≤ ∑ i, ‖a i • lpPointNorm (g i)‖ := norm_sum_le _ _
    _ = ∑ i, a i * ‖g i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha i), norm_lpPointNorm]

end PoincareConjecture.M35.Uniqueness.Heat
