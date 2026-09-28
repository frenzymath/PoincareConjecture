import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerACL












set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff intervalIntegral

namespace PoincareConjecture

private theorem m65Endpoint_integral_tendsto
    {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {d : ℕ → Lp ℝ 2 (volume.restrict (Icc a b))}
    {d0 : Lp ℝ 2 (volume.restrict (Icc a b))}
    (hd : Tendsto d atTop (𝓝 d0)) :
    Tendsto (fun n => ∫ x in s..t, d n x) atTop (𝓝 (∫ x in s..t, d0 x)) := by
  have hordered {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      Tendsto (fun n => ∫ x in s..t, d n x) atTop
        (𝓝 (∫ x in s..t, d0 x)) := by
    let mu := volume.restrict (Icc a b)
    have hfin : mu (Ioc s t) ≠ ⊤ := measure_ne_top _ _
    have hpair (v : Lp ℝ 2 mu) :
        ⟪indicatorConstLp 2 measurableSet_Ioc hfin (1 : ℝ), v⟫_ℝ =
          ∫ x in s..t, v x := by
      rw [L2.inner_indicatorConstLp_one, intervalIntegral.integral_of_le hst,
        Measure.restrict_restrict_of_subset (show Ioc s t ⊆ Icc a b from
          fun x hx => ⟨hs.1.trans hx.1.le, hx.2.trans ht.2⟩)]
    have hh : Tendsto (fun n =>
        ⟪indicatorConstLp 2 measurableSet_Ioc hfin (1 : ℝ), d n⟫_ℝ) atTop
      (𝓝 ⟪indicatorConstLp 2 measurableSet_Ioc hfin (1 : ℝ), d0⟫_ℝ) :=
      tendsto_const_nhds.inner hd
    simpa only [hpair] using hh
  rcases le_total s t with hst | hts
  · exact hordered hs ht hst
  · simpa only [← intervalIntegral.integral_symm] using (hordered ht hs hts).neg






theorem m65Interval_AC_graph_endpoint_limit
    {a b : ℝ} (hab : a < b) (f : ℕ → ℝ → ℝ)
    (hf : ∀ n, ContDiff ℝ 1 (f n))
    (u d : ℕ → Lp ℝ 2 (volume.restrict (Icc a b)))
    (u0 d0 : Lp ℝ 2 (volume.restrict (Icc a b)))
    (hu : ∀ n, u n =ᵐ[volume.restrict (Icc a b)] f n)
    (hd : ∀ n, d n =ᵐ[volume.restrict (Icc a b)] deriv (f n))
    (hu0 : Tendsto u atTop (𝓝 u0)) (hd0 : Tendsto d atTop (𝓝 d0)) :
    ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧
      (v =ᵐ[volume.restrict (Icc a b)] u0) ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        v t - v s = ∫ x in s..t, d0 x) ∧
      ∀ t ∈ Icc a b, Tendsto (fun n => f n t) atTop (𝓝 (v t)) := by
  obtain ⟨v, hv, hvu, hvd⟩ :=
    m65Interval_AC_of_smooth_L2_graph hab f hf u d u0 d0 hu hd hu0 hd0
  refine ⟨v, hv, hvu, hvd, ?_⟩
  intro t ht
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨σ, hσ, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hu0.comp hns)).exists_seq_tendsto_ae
  have hactual : ∀ᵐ x ∂volume.restrict (Icc a b),
      Tendsto (fun n => f (ns (σ n)) x) atTop (𝓝 (v x)) := by
    filter_upwards [hpoint, ae_all_iff.mpr hu, hvu] with x hx hux hvx
    rw [hvx]
    exact hx.congr (fun n => hux (ns (σ n)))
  have hvol : volume (Icc a b) ≠ 0 := by
    simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero]
    linarith
  obtain ⟨c, hc, hfc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol hactual
  have htail := hns.comp hσ.tendsto_atTop
  have hdconv := (m65Endpoint_integral_tendsto hc ht hd0).comp htail
  have hFTC (n : ℕ) :
      f (ns (σ n)) c + (∫ x in c..t, d (ns (σ n)) x) = f (ns (σ n)) t := by
    have heq : (∫ x in c..t, d (ns (σ n)) x) =
        ∫ x in c..t, deriv (f (ns (σ n))) x := by
      apply intervalIntegral.integral_congr_ae_restrict
      exact ae_restrict_of_ae_restrict_of_subset
        ((uIoc_subset_uIcc).trans (uIcc_subset_Icc hc ht)) (hd (ns (σ n)))
    rw [heq, intervalIntegral.integral_eq_sub_of_hasDerivAt]
    · ring
    · intro x _
      exact ((hf (ns (σ n))).differentiable one_ne_zero x).hasDerivAt
    · exact ((hf (ns (σ n))).continuous_deriv (by norm_num)).intervalIntegrable c t
  have hsum : v c + (∫ x in c..t, d0 x) = v t := by
    linarith [hvd c hc t ht]
  have hlim := hfc.add hdconv
  rw [hsum] at hlim
  exact ⟨σ, hlim.congr hFTC⟩

end PoincareConjecture
