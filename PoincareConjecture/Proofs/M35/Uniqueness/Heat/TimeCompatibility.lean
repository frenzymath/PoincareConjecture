import PoincareConjecture.Proofs.M35.Uniqueness.Heat.BochnerAbsolute

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem moving_operator_compatibility {T : ℝ} (hT : 0 ≤ T)
    (K K' : ℝ → V →L[ℝ] V) (hK : ContDiffOn ℝ 1 K (Icc 0 T))
    (hKd : ∀ t ∈ Ioo 0 T, HasDerivAt K (K' t) t)
    (w q : ℝ → V) (hw : IntervalIntegrable w volume 0 T)
    (hq : IntervalIntegrable q volume 0 T) (u₀ z₀ : V)
    (hzero : z₀ + K 0 u₀ = 0)
    (heq : ∀ᵐ t ∂timeMeasure T,
      q t + K' t (u₀ + ∫ s in (0 : ℝ)..t, w s) + K t (w t) = 0) :
    ∀ t ∈ Icc 0 T,
      z₀ + (∫ s in (0 : ℝ)..t, q s) + K t (u₀ + ∫ s in (0 : ℝ)..t, w s) = 0 := by
  let u : ℝ → V := fun t => u₀ + ∫ s in (0 : ℝ)..t, w s
  let z : ℝ → V := fun t => z₀ + ∫ s in (0 : ℝ)..t, q s
  have hu : AbsolutelyContinuousOnInterval u 0 T := by
    have huc : ContDiffOn ℝ 1 (fun _ : ℝ => u₀) (uIcc 0 T) := contDiffOn_const
    exact huc.absolutelyContinuousOnInterval.fun_add
      (absoluteContinuous_bochner_primitive hw left_mem_uIcc)
  have hz : AbsolutelyContinuousOnInterval z 0 T := by
    have hzc : ContDiffOn ℝ 1 (fun _ : ℝ => z₀) (uIcc 0 T) := contDiffOn_const
    exact hzc.absolutelyContinuousOnInterval.fun_add
      (absoluteContinuous_bochner_primitive hq left_mem_uIcc)
  have hKa : AbsolutelyContinuousOnInterval K 0 T := by
    have hK' : ContDiffOn ℝ 1 K (uIcc 0 T) := by simpa only [uIcc_of_le hT] using hK
    exact hK'.absolutelyContinuousOnInterval
  have hres : AbsolutelyContinuousOnInterval (fun t => z t + K t (u t)) 0 T :=
    hz.fun_add (absoluteContinuous_clm_apply hKa hu)
  have heq' : ∀ᵐ t ∂volume, t ∈ Ioc 0 T →
      q t + K' t (u t) + K t (w t) = 0 :=
    (ae_restrict_iff' measurableSet_Ioc).mp heq
  have hd : ∀ᵐ t ∂volume, t ∈ uIcc 0 T →
      HasDerivAt (fun t => z t + K t (u t)) 0 t := by
    filter_upwards [hw.ae_hasDerivAt_integral, hq.ae_hasDerivAt_integral,
      heq', volume.ae_ne (0 : ℝ), volume.ae_ne T] with t hwt hqt het ht0 htT ht
    have htcc : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
    have htoo : t ∈ Ioo 0 T := ⟨lt_of_le_of_ne htcc.1 ht0.symm,
      lt_of_le_of_ne htcc.2 htT⟩
    have hdu : HasDerivAt u (w t) t :=
      (hwt ht 0 left_mem_uIcc).const_add u₀
    have hdz : HasDerivAt z (q t) t :=
      (hqt ht 0 left_mem_uIcc).const_add z₀
    have h := hdz.add ((hKd t htoo).clm_apply hdu)
    apply h.congr_deriv
    have he := het ⟨htoo.1, htcc.2⟩
    simpa only [add_assoc] using he
  obtain ⟨c, hc⟩ := hres.const_of_ae_hasDerivAt_zero hd
  have hc0 : c = 0 := by
    have h := hc 0 left_mem_uIcc
    simp only [u, z, intervalIntegral.integral_same, add_zero] at h
    exact h.symm.trans hzero
  intro t ht
  exact (hc t (by simpa only [uIcc_of_le hT] using ht)).trans hc0

end PoincareConjecture.M35.Uniqueness.Heat
