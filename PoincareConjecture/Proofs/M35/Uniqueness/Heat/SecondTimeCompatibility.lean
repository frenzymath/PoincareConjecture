import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeCompatibility










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem moving_operator_second_compatibility {T : ℝ} (hT : 0 ≤ T)
    (K K₁ K₂ : ℝ → V →L[ℝ] V)
    (hK : ContDiffOn ℝ 1 K (Icc 0 T)) (hK₁ : ContDiffOn ℝ 1 K₁ (Icc 0 T))
    (hKd : ∀ t ∈ Ioo 0 T, HasDerivAt K (K₁ t) t)
    (hK₁d : ∀ t ∈ Ioo 0 T, HasDerivAt K₁ (K₂ t) t)
    (u w z q : ℝ → V) (u₀ w₀ y₀ : V)
    (hz : IntervalIntegrable z volume 0 T) (hw : IntervalIntegrable w volume 0 T)
    (hq : IntervalIntegrable q volume 0 T)
    (hwi : ∀ t, w t = w₀ + ∫ s in (0 : ℝ)..t, z s)
    (hui : ∀ t, u t = u₀ + ∫ s in (0 : ℝ)..t, w s)
    (hzero : y₀ + K 0 w₀ + K₁ 0 u₀ = 0)
    (heq : ∀ᵐ t ∂timeMeasure T,
      q t + K t (z t) + K₁ t (w t) + K₁ t (w t) + K₂ t (u t) = 0) :
    ∀ t ∈ Icc 0 T,
      y₀ + (∫ s in (0 : ℝ)..t, q s) + K t (w t) + K₁ t (u t) = 0 := by
  have huc : ContDiffOn ℝ 1 (fun _ : ℝ => u₀) (uIcc 0 T) := contDiffOn_const
  have hwc : ContDiffOn ℝ 1 (fun _ : ℝ => w₀) (uIcc 0 T) := contDiffOn_const
  have hyc : ContDiffOn ℝ 1 (fun _ : ℝ => y₀) (uIcc 0 T) := contDiffOn_const
  have hua : AbsolutelyContinuousOnInterval u 0 T := by
    have he : u = fun t => u₀ + ∫ s in (0 : ℝ)..t, w s := funext hui
    rw [he]
    exact huc.absolutelyContinuousOnInterval.fun_add
      (absoluteContinuous_bochner_primitive hw left_mem_uIcc)
  have hwa : AbsolutelyContinuousOnInterval w 0 T := by
    have he : w = fun t => w₀ + ∫ s in (0 : ℝ)..t, z s := funext hwi
    rw [he]
    exact hwc.absolutelyContinuousOnInterval.fun_add
      (absoluteContinuous_bochner_primitive hz left_mem_uIcc)
  let y : ℝ → V := fun t => y₀ + ∫ s in (0 : ℝ)..t, q s
  have hya : AbsolutelyContinuousOnInterval y 0 T :=
    hyc.absolutelyContinuousOnInterval.fun_add
      (absoluteContinuous_bochner_primitive hq left_mem_uIcc)
  have hKa : AbsolutelyContinuousOnInterval K 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hT] using hK
  have hK₁a : AbsolutelyContinuousOnInterval K₁ 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hT] using hK₁
  have hres : AbsolutelyContinuousOnInterval
      (fun t => y t + K t (w t) + K₁ t (u t)) 0 T :=
    (hya.fun_add (absoluteContinuous_clm_apply hKa hwa)).fun_add
      (absoluteContinuous_clm_apply hK₁a hua)
  have heq' : ∀ᵐ t ∂volume, t ∈ Ioc 0 T →
      q t + K t (z t) + K₁ t (w t) + K₁ t (w t) + K₂ t (u t) = 0 :=
    (ae_restrict_iff' measurableSet_Ioc).mp heq
  have hd : ∀ᵐ t ∂volume, t ∈ uIcc 0 T →
      HasDerivAt (fun t => y t + K t (w t) + K₁ t (u t)) 0 t := by
    filter_upwards [hz.ae_hasDerivAt_integral, hw.ae_hasDerivAt_integral,
      hq.ae_hasDerivAt_integral, heq', volume.ae_ne (0 : ℝ), volume.ae_ne T]
      with t hzt hwt hqt het ht0 htT ht
    have htcc : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
    have htoo : t ∈ Ioo 0 T := ⟨lt_of_le_of_ne htcc.1 ht0.symm,
      lt_of_le_of_ne htcc.2 htT⟩
    have hdu : HasDerivAt u (w t) t := by
      simpa only [← hui] using (hwt ht 0 left_mem_uIcc).const_add u₀
    have hdw : HasDerivAt w (z t) t := by
      simpa only [← hwi] using (hzt ht 0 left_mem_uIcc).const_add w₀
    have hdy : HasDerivAt y (q t) t := (hqt ht 0 left_mem_uIcc).const_add y₀
    apply ((hdy.add ((hKd t htoo).clm_apply hdw)).add
      ((hK₁d t htoo).clm_apply hdu)).congr_deriv
    calc
      q t + (K₁ t (w t) + K t (z t)) + (K₂ t (u t) + K₁ t (w t)) =
          q t + K t (z t) + K₁ t (w t) + K₁ t (w t) + K₂ t (u t) := by abel
      _ = 0 := het ⟨htoo.1, htcc.2⟩
  obtain ⟨c, hc⟩ := hres.const_of_ae_hasDerivAt_zero hd
  have hc0 : c = 0 := by
    have h := hc 0 left_mem_uIcc
    simp only [y, hwi 0, hui 0, intervalIntegral.integral_same, add_zero] at h
    exact h.symm.trans hzero
  intro t ht
  exact (hc t (by simpa only [uIcc_of_le hT] using ht)).trans hc0

end PoincareConjecture.M35.Uniqueness.Heat
