import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt











set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace PoincareConjecture.M63





theorem continuous_compLpL_of_strong
    {P E X : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace X]
    (A : P → E →L[ℝ] E) (μ : Measure X) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ p, ‖A p‖ ≤ K)
    (hstrong : Continuous (fun z : P × E => A z.1 z.2)) :
    Continuous (fun z : P × Lp E 2 μ => (A z.1).compLpL 2 μ z.2) := by
  have hnorm (G : Lp E 2 μ) : ‖G‖ ^ 2 = ∫ x, ‖G x‖ ^ 2 ∂μ := by
    calc
      _ = inner ℝ G G := (real_inner_self_eq_norm_sq G).symm
      _ = ∫ x, inner ℝ (G x) (G x) ∂μ := L2.inner_def G G
      _ = _ := by simp only [real_inner_self_eq_norm_sq]
  apply continuous_prod_of_continuous_lipschitzWith' _ (⟨K, hK⟩ : NNReal)
  · intro p
    exact ContinuousLinearMap.lipschitzWith_of_opNorm_le (K := (⟨K, hK⟩ : NNReal))
      ((ContinuousLinearMap.norm_compLpL_le (A p)).trans (hbound p))
  · intro F
    apply continuous_iff_continuousAt.mpr
    intro p0
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    let f (p : P) (x : X) : ℝ := ‖A p (F x) - A p0 (F x)‖ ^ 2
    let b (x : X) : ℝ := (K + K) ^ 2 * ‖F x‖ ^ 2
    have hmeas (p : P) : AEStronglyMeasurable (f p) μ :=
      (((A p).continuous.comp_aestronglyMeasurable (Lp.memLp F).aestronglyMeasurable).sub
        ((A p0).continuous.comp_aestronglyMeasurable (Lp.memLp F).aestronglyMeasurable)).norm.pow 2
    have hb : Integrable b μ :=
      ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
    have hdom (p : P) (x : X) : ‖f p x‖ ≤ b x := by
      have hn : ‖A p (F x) - A p0 (F x)‖ ≤ (K + K) * ‖F x‖ := by
        calc
          _ ≤ ‖A p (F x)‖ + ‖A p0 (F x)‖ := norm_sub_le _ _
          _ ≤ K * ‖F x‖ + K * ‖F x‖ := add_le_add
            (((A p).le_opNorm (F x)).trans
              (mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg _)))
            (((A p0).le_opNorm (F x)).trans
              (mul_le_mul_of_nonneg_right (hbound p0) (norm_nonneg _)))
          _ = _ := (add_mul _ _ _).symm
      change ‖‖A p (F x) - A p0 (F x)‖ ^ 2‖ ≤ _
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [b, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hlim (x : X) : Tendsto (fun p => f p x) (𝓝 p0) (𝓝 (0 : ℝ)) := by
      have hc := hstrong.comp (continuous_id.prodMk (continuous_const (y := F x)))
      simpa only [Function.comp_def, id_eq, f, sub_self, norm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        ((hc.tendsto p0).sub_const (A p0 (F x))).norm.pow 2
    have hint : Tendsto (fun p => ∫ x, f p x ∂μ) (𝓝 p0) (𝓝 (0 : ℝ)) := by
      simpa only [integral_zero] using
        tendsto_integral_filter_of_dominated_convergence (μ := μ) b
          (Eventually.of_forall hmeas)
          (Eventually.of_forall (fun p => Eventually.of_forall (hdom p))) hb
          (Eventually.of_forall hlim)
    have hid (p : P) : ‖(A p).compLpL 2 μ F - (A p0).compLpL 2 μ F‖ ^ 2 =
        ∫ x, f p x ∂μ := by
      rw [hnorm]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub ((A p).compLpL 2 μ F) ((A p0).compLpL 2 μ F),
        (A p).coeFn_compLpL F, (A p0).coeFn_compLpL F] with x hx hp hp0
      simp only [hx, Pi.sub_apply, hp, hp0, f]
    have hsq : Tendsto (fun p => ‖(A p).compLpL 2 μ F - (A p0).compLpL 2 μ F‖ ^ 2)
        (𝓝 p0) (𝓝 (0 : ℝ)) := by simpa only [hid] using hint
    have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

end PoincareConjecture.M63
