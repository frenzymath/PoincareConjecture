import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPeriodPositive
import Mathlib.MeasureTheory.Integral.DominatedConvergence












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M64Uniformization

local notation "Cover" => ℝ × ℝ







theorem scalar_integral_band_tendsto {F : Cover → ℝ}
    (hF : IntegrableOn F (Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1))
    {a b : ℕ → ℝ} (ha : ∀ n, 1 < a n) (hb : ∀ n, b n < 2)
    (halim : Tendsto a atTop (𝓝 1)) (hblim : Tendsto b atTop (𝓝 2)) :
    Tendsto (fun n => ∫ z in Icc (a n) (b n) ×ˢ Ioo (0 : ℝ) 1, F z) atTop
      (𝓝 (∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1, F z)) := by
  let B := Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1
  let K : ℕ → Set Cover := fun n => Icc (a n) (b n) ×ˢ Ioo (0 : ℝ) 1
  have hBm : MeasurableSet B := measurableSet_Ioo.prod measurableSet_Ioo
  have hKm (n : ℕ) : MeasurableSet (K n) := measurableSet_Icc.prod measurableSet_Ioo
  have hsub (n : ℕ) : K n ⊆ B :=
    fun z hz => ⟨⟨(ha n).trans_le hz.1.1, hz.1.2.trans_lt (hb n)⟩, hz.2⟩
  have hFi (n : ℕ) : Integrable ((K n).indicator F) :=
    (hF.mono_set (hsub n)).integrable_indicator (hKm n)
  have hFnorm : IntegrableOn (fun z => ‖F z‖) B := hF.norm
  have hbound : Integrable (B.indicator (fun z => ‖F z‖)) := hFnorm.integrable_indicator hBm
  have hlim (z : Cover) : Tendsto (fun n => (K n).indicator F z) atTop
      (𝓝 (B.indicator F z)) := by
    by_cases hz : z ∈ B
    · have har : ∀ᶠ n in atTop, a n < z.1 := (tendsto_order.mp halim).2 _ hz.1.1
      have hbr : ∀ᶠ n in atTop, z.1 < b n := (tendsto_order.mp hblim).1 _ hz.1.2
      apply tendsto_const_nhds.congr'
      filter_upwards [har, hbr] with n han hbn
      simp only [indicator_of_mem hz F,
        indicator_of_mem (show z ∈ K n from ⟨⟨han.le, hbn.le⟩, hz.2⟩) F]
    · have hzK (n : ℕ) : z ∉ K n := fun h => hz (hsub n h)
      simpa only [indicator_of_notMem hz F, indicator_of_notMem (hzK _) F]
        using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hdom (n : ℕ) (z : Cover) : ‖(K n).indicator F z‖ ≤ B.indicator (fun y => ‖F y‖) z := by
    by_cases hz : z ∈ K n
    · simp only [indicator_of_mem hz F, indicator_of_mem (hsub n hz), le_refl]
    · rw [indicator_of_notMem hz F, norm_zero]
      by_cases hzB : z ∈ B
      · simpa only [indicator_of_mem hzB] using norm_nonneg (F z)
      · simp only [indicator_of_notMem hzB, le_refl]
  have ht := tendsto_integral_filter_of_dominated_convergence
    (B.indicator (fun z => ‖F z‖)) (Eventually.of_forall fun n => (hFi n).aestronglyMeasurable)
    (Eventually.of_forall fun n => ae_of_all _ (hdom n)) hbound (ae_of_all _ hlim)
  simpa only [integral_indicator (hKm _), integral_indicator hBm] using ht

end PoincareConjecture.M64Uniformization
