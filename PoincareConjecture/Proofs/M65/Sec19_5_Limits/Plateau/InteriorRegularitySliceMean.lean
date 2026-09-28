import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerSlicing











set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace PoincareConjecture.M65Interior

private theorem intervalMean_tendsto {a b : ℝ} (hab : a ≤ b)
    {u : ℕ → Lp ℝ 2 (volume.restrict (Icc a b))}
    {u0 : Lp ℝ 2 (volume.restrict (Icc a b))}
    (hu : Tendsto u atTop (𝓝 u0)) :
    Tendsto (fun n => ∫ t in a..b, u n t) atTop (𝓝 (∫ t in a..b, u0 t)) := by
  let mu := volume.restrict (Icc a b)
  have hfin : mu (Ioc a b) ≠ ⊤ := measure_ne_top _ _
  have hpair (v : Lp ℝ 2 mu) :
      ⟪indicatorConstLp 2 measurableSet_Ioc hfin (1 : ℝ), v⟫_ℝ =
        ∫ t in a..b, v t := by
    rw [L2.inner_indicatorConstLp_one, intervalIntegral.integral_of_le hab,
      Measure.restrict_restrict_of_subset Ioc_subset_Icc_self]
  have hconv : Tendsto (fun n =>
      ⟪indicatorConstLp 2 measurableSet_Ioc hfin (1 : ℝ), u n⟫_ℝ) atTop
        (𝓝 ⟪indicatorConstLp 2 measurableSet_Ioc hfin (1 : ℝ), u0⟫_ℝ) :=
    tendsto_const_nhds.inner hu
  simpa only [hpair] using hconv




theorem sliceMean_zero_of_tendsto
    {X : Type*} [MeasurableSpace X] {mu : Measure X} [SFinite mu]
    {a b : ℝ} (hab : a ≤ b)
    {u : ℕ → Lp ℝ 2 (mu.prod (volume.restrict (Icc a b)))}
    {u0 : Lp ℝ 2 (mu.prod (volume.restrict (Icc a b)))}
    (hu : Tendsto u atTop (𝓝 u0))
    (hzero : ∀ n, ∀ᵐ x ∂mu, (∫ t in a..b, u n (x, t)) = 0) :
    ∀ᵐ x ∂mu, (∫ t in a..b, u0 (x, t)) = 0 := by
  obtain ⟨σ, _, hslice⟩ := m65L2_exists_slice_subsequence hu
  filter_upwards [hslice, ae_all_iff.mpr hzero] with x hx hz
  obtain ⟨hUn, hU0, hconv⟩ := hx
  have heq (v : Lp ℝ 2 (volume.restrict (Icc a b)))
      (f : ℝ → ℝ) (hv : v =ᵐ[volume.restrict (Icc a b)] f) :
      (∫ t in a..b, v t) = ∫ t in a..b, f t := by
    apply intervalIntegral.integral_congr_ae_restrict
    exact ae_restrict_of_ae_restrict_of_subset
      (by simpa only [uIoc_of_le hab] using Ioc_subset_Icc_self) hv
  have hn (n : ℕ) :
      (∫ t in a..b, (hUn n).toLp (fun t => u (σ n) (x, t)) t) = 0 := by
    rw [heq _ _ (hUn n).coeFn_toLp]
    exact hz (σ n)
  have hmean := (intervalMean_tendsto hab hconv).congr hn
  have hlim : (∫ t in a..b, hU0.toLp (fun t => u0 (x, t)) t) = 0 :=
    tendsto_nhds_unique hmean tendsto_const_nhds
  rwa [heq _ _ hU0.coeFn_toLp] at hlim

end PoincareConjecture.M65Interior
