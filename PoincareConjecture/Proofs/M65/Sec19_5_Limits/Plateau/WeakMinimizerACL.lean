import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerTrace
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure











set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff intervalIntegral

namespace PoincareConjecture

private theorem m65IntervalL2_integral_tendsto
    {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {u : ℕ → Lp ℝ 2 (volume.restrict (Icc a b))}
    {u0 : Lp ℝ 2 (volume.restrict (Icc a b))}
    (hu : Tendsto u atTop (𝓝 u0)) :
    Tendsto (fun n => ∫ x in s..t, u n x) atTop (𝓝 (∫ x in s..t, u0 x)) := by
  have hordered {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      Tendsto (fun n => ∫ x in s..t, u n x) atTop
        (𝓝 (∫ x in s..t, u0 x)) := by
    let mu := volume.restrict (Icc a b)
    have hfin : mu (Ioc s t) ≠ ⊤ := measure_ne_top _ _
    have hpair (v : Lp ℝ 2 mu) :
        ⟪indicatorConstLp 2 measurableSet_Ioc hfin (1 : ℝ), v⟫_ℝ =
          ∫ x in s..t, v x := by
      rw [L2.inner_indicatorConstLp_one, intervalIntegral.integral_of_le hst]
      rw [Measure.restrict_restrict_of_subset (show Ioc s t ⊆ Icc a b from
        fun x hx => ⟨hs.1.trans hx.1.le, hx.2.trans ht.2⟩)]
    have hconv : Tendsto (fun n =>
        ⟪indicatorConstLp 2 measurableSet_Ioc hfin (1 : ℝ), u n⟫_ℝ) atTop
        (𝓝 ⟪indicatorConstLp 2 measurableSet_Ioc hfin (1 : ℝ), u0⟫_ℝ) :=
      tendsto_const_nhds.inner hu
    simpa only [hpair] using hconv
  rcases le_total s t with hst | hts
  · exact hordered hs ht hst
  · simpa only [← intervalIntegral.integral_symm] using (hordered ht hs hts).neg






theorem m65Interval_AC_of_smooth_L2_graph
    {a b : ℝ} (hab : a < b) (f : ℕ → ℝ → ℝ)
    (hf : ∀ n, ContDiff ℝ 1 (f n))
    (u d : ℕ → Lp ℝ 2 (volume.restrict (Icc a b)))
    (u0 d0 : Lp ℝ 2 (volume.restrict (Icc a b)))
    (hu : ∀ n, u n =ᵐ[volume.restrict (Icc a b)] f n)
    (hd : ∀ n, d n =ᵐ[volume.restrict (Icc a b)] deriv (f n))
    (hu0 : Tendsto u atTop (𝓝 u0)) (hd0 : Tendsto d atTop (𝓝 d0)) :
    ∃ v : ℝ → ℝ, AbsolutelyContinuousOnInterval v a b ∧
      v =ᵐ[volume.restrict (Icc a b)] u0 ∧
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        v t - v s = ∫ x in s..t, d0 x := by
  obtain ⟨σ, hσ, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hu0).exists_seq_tendsto_ae
  have hactual : ∀ᵐ x ∂volume.restrict (Icc a b),
      Tendsto (fun n => f (σ n) x) atTop (𝓝 (u0 x)) := by
    filter_upwards [hpoint, ae_all_iff.mpr hu] with x hx hux
    exact hx.congr (fun n => hux (σ n))
  have hvol : volume (Icc a b) ≠ 0 := by
    simp only [Real.volume_Icc, ne_eq, ENNReal.ofReal_eq_zero]
    linarith
  obtain ⟨c, hc, hfc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol hactual
  have hdint : IntegrableOn d0 (Icc a b) volume :=
    MemLp.integrable (by norm_num) (Lp.memLp d0)
  have hdint' {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
      IntervalIntegrable d0 volume s t :=
    (hdint.mono_set (uIcc_subset_Icc hs ht)).intervalIntegrable
  let v : ℝ → ℝ := fun t => u0 c + ∫ x in c..t, d0 x
  have hvconv (t : ℝ) (ht : t ∈ Icc a b) :
      Tendsto (fun n => f (σ n) t) atTop (𝓝 (v t)) := by
    have hdconv := (m65IntervalL2_integral_tendsto hc ht hd0).comp hσ.tendsto_atTop
    have hFTC (n : ℕ) : f (σ n) c + (∫ x in c..t, d (σ n) x) = f (σ n) t := by
      have heq : (∫ x in c..t, d (σ n) x) = ∫ x in c..t, deriv (f (σ n)) x := by
        apply intervalIntegral.integral_congr_ae_restrict
        exact ae_restrict_of_ae_restrict_of_subset
          ((uIoc_subset_uIcc).trans (uIcc_subset_Icc hc ht)) (hd (σ n))
      rw [heq, intervalIntegral.integral_eq_sub_of_hasDerivAt]
      · ring
      · intro x _
        exact ((hf (σ n)).differentiable one_ne_zero x).hasDerivAt
      · exact ((hf (σ n)).continuous_deriv (by norm_num)).intervalIntegrable c t
    exact (hfc.add hdconv).congr hFTC
  refine ⟨v, ?_, ?_, ?_⟩
  · have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => u0 c) a b :=
      contDiffOn_const.absolutelyContinuousOnInterval
    exact hconst.add
      ((hdint' ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩).absolutelyContinuousOnInterval_intervalIntegral
        (by simpa only [uIcc_of_le hab.le] using hc))
  · filter_upwards [hactual, ae_restrict_mem measurableSet_Icc] with t hft ht
    exact tendsto_nhds_unique (hvconv t ht) hft
  · intro s hs t ht
    dsimp only [v]
    rw [add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hdint' hc ht) (hdint' hc hs)]

end PoincareConjecture
