import PoincareConjecture.Proofs.M47.TerminalGermsExtraction










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M47



theorem terminalGerms_limit_at_terminal
    {E : Type*} [NormedAddCommGroup E]
    {tau C : ℝ} (htau : 0 < tau)
    (f : ℕ → ℝ → E) (B : ℝ → E) (B0 : E)
    (hzero : Tendsto (fun k => f k 0) atTop (𝓝 B0))
    (hminus : ∀ t ∈ Ioo (-tau) 0, Tendsto (fun k => f k t) atTop (𝓝 (B t)))
    (hbound : ∀ t ∈ Ioo (-tau) 0, ∀ᶠ k in atTop,
      ‖f k t - f k 0‖ ≤ C * |t|) :
    (∀ t ∈ Ioo (-tau) 0, ‖B t - B0‖ ≤ C * |t|) ∧
      Tendsto B (𝓝[<] 0) (𝓝 B0) := by
  have hlimit (t : ℝ) (ht : t ∈ Ioo (-tau) 0) : ‖B t - B0‖ ≤ C * |t| :=
    le_of_tendsto ((hminus t ht).sub hzero).norm (hbound t ht)
  refine ⟨hlimit, ?_⟩
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hden : 0 < |C| + 1 := by positivity
  have hnear : ∀ᶠ t in 𝓝[<] (0 : ℝ), |t| < epsilon / (|C| + 1) := by
    have hcont : Tendsto (fun t : ℝ => |t|) (𝓝[<] 0) (𝓝 |(0 : ℝ)|) :=
      (continuous_abs.tendsto 0).mono_left nhdsWithin_le_nhds
    exact hcont.eventually (gt_mem_nhds (by simpa only [abs_zero] using div_pos hepsilon hden))
  filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr htau), hnear] with t ht hsmall
  rw [dist_eq_norm]
  have hstep : C * |t| ≤ (|C| + 1) * |t| :=
    mul_le_mul_of_nonneg_right ((le_abs_self C).trans (le_add_of_nonneg_right zero_le_one))
      (abs_nonneg t)
  exact ((hlimit t ht).trans hstep).trans_lt (by
    simpa only [mul_comm] using (lt_div_iff₀ hden).mp hsmall)

end PoincareConjecture.M47
