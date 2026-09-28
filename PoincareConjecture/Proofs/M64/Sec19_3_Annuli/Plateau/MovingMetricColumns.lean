import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

variable {X E : Type*} [MeasurableSpace X] {mu : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem norm_toLp_sq_integral {f : X → E} (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq]



theorem m64Metric_test_columns_strong
    (B : ℕ → X → E →L[ℝ] E →L[ℝ] ℝ) (B0 : X → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ j, AEStronglyMeasurable (B j) mu) (hB0 : AEStronglyMeasurable B0 mu)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ j, ∀ᵐ x ∂mu, ‖B j x‖ ≤ K)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun j => B j x) atTop (𝓝 (B0 x)))
    (v : Lp E 2 mu) :
    let w := fun j x => (InnerProductSpace.toDual ℝ E).symm (B j x (v x))
    let w0 := fun x => (InnerProductSpace.toDual ℝ E).symm (B0 x (v x))
    ∃ (hw : ∀ j, MemLp (w j) 2 mu) (hw0 : MemLp w0 2 mu),
      Tendsto (fun j => (hw j).toLp (w j)) atTop (𝓝 (hw0.toLp w0)) := by
  let R := (InnerProductSpace.toDual ℝ E).symm
  let w := fun j x => R (B j x (v x))
  let w0 := fun x => R (B0 x (v x))
  have hbound0 : ∀ᵐ x ∂mu, ‖B0 x‖ ≤ K := by
    filter_upwards [hlim, ae_all_iff.mpr hbound] with x hx hb
    have hn : Tendsto (fun j => ‖B j x‖) atTop (𝓝 ‖B0 x‖) := by
      simpa only [Function.comp_def] using (continuous_norm.tendsto (B0 x)).comp hx
    exact le_of_tendsto hn (Eventually.of_forall hb)
  have happly : Continuous (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × E => q.1 q.2) :=
    continuous_fst.clm_apply continuous_snd
  have hwm (j : ℕ) : AEStronglyMeasurable (w j) mu :=
    R.continuous.comp_aestronglyMeasurable
      (happly.comp_aestronglyMeasurable ((hB j).prodMk (Lp.aestronglyMeasurable v)))
  have hw0m : AEStronglyMeasurable w0 mu :=
    R.continuous.comp_aestronglyMeasurable
      (happly.comp_aestronglyMeasurable (hB0.prodMk (Lp.aestronglyMeasurable v)))
  have hwb (j : ℕ) : ∀ᵐ x ∂mu, ‖w j x‖ ≤ K * ‖v x‖ := by
    filter_upwards [hbound j] with x hx
    exact (R.norm_map _).le.trans ((B j x).le_opNorm (v x) |>.trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))
  have hw0b : ∀ᵐ x ∂mu, ‖w0 x‖ ≤ K * ‖v x‖ := by
    filter_upwards [hbound0] with x hx
    exact (R.norm_map _).le.trans ((B0 x).le_opNorm (v x) |>.trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))
  have hw (j : ℕ) : MemLp (w j) 2 mu := (Lp.memLp v).of_le_mul (hwm j) (hwb j)
  have hw0 : MemLp w0 2 mu := (Lp.memLp v).of_le_mul hw0m hw0b
  have hint : Integrable (fun x => 4 * K ^ 2 * ‖v x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
      |>.const_mul _
  have hdom (j : ℕ) : ∀ᵐ x ∂mu,
      ‖‖w j x - w0 x‖ ^ 2‖ ≤ 4 * K ^ 2 * ‖v x‖ ^ 2 := by
    filter_upwards [hwb j, hw0b] with x hx hx0
    have hn : ‖w j x - w0 x‖ ≤ 2 * K * ‖v x‖ :=
      (norm_sub_le _ _).trans (by linarith)
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * K * ‖v x‖)).mpr hn
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hpoint : ∀ᵐ x ∂mu, Tendsto (fun j => ‖w j x - w0 x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    have hh : Tendsto (fun j => w j x) atTop (𝓝 (w0 x)) :=
      R.continuous.tendsto _ |>.comp
        ((happly.tendsto (B0 x, v x)).comp (hx.prodMk_nhds tendsto_const_nhds))
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((hh.sub_const (w0 x)).norm.pow 2)
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun x => 4 * K ^ 2 * ‖v x‖ ^ 2)
    (fun j => ((hwm j).sub hw0m).norm.pow 2) hint hdom hpoint
  simp only [integral_zero] at hDCT
  have heq (j : ℕ) : ‖(hw j).toLp (w j) - hw0.toLp w0‖ ^ 2 =
      ∫ x, ‖w j x - w0 x‖ ^ 2 ∂mu := by
    rw [← MemLp.toLp_sub, norm_toLp_sq_integral]
    rfl
  have hsq : Tendsto (fun j => ‖(hw j).toLp (w j) - hw0.toLp w0‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := hDCT.congr' (Eventually.of_forall fun j => (heq j).symm)
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hn
  exact ⟨hw, hw0, tendsto_iff_norm_sub_tendsto_zero.mpr hn⟩

end PoincareConjecture
