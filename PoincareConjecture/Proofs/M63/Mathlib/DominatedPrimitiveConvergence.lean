import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

universe u

namespace intervalIntegral

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure ℝ} [NullSingletonClass μ]
  {a b : ℝ} {fn : ℕ → ℝ → E} {f : ℝ → E} {bound : ℝ → ℝ}

theorem tendstoUniformlyOn_primitive_of_dominated
    [CompleteSpace E]
    (hab : a ≤ b)
    (hmeas : ∀ j, AEStronglyMeasurable (fn j) (μ.restrict (Icc a b)))
    (hint : IntegrableOn bound (Icc a b) μ)
    (hbound : ∀ j, ∀ᵐ t ∂μ.restrict (Icc a b), ‖fn j t‖ ≤ bound t)
    (hlim : ∀ᵐ t ∂μ.restrict (Icc a b),
      Tendsto (fun j => fn j t) atTop (𝓝 (f t))) :
    (∀ j, IntervalIntegrable (fn j) μ a b) ∧
      IntervalIntegrable f μ a b ∧
      ContinuousOn (fun t => ∫ s in a..t, f s ∂μ) (Icc a b) ∧
      TendstoUniformlyOn (fun j t => ∫ s in a..t, fn j s ∂μ)
        (fun t => ∫ s in a..t, f s ∂μ) atTop (Icc a b) := by
  have hfm : AEStronglyMeasurable f (μ.restrict (Icc a b)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim
  have hfb : ∀ᵐ t ∂μ.restrict (Icc a b), ‖f t‖ ≤ bound t := by
    filter_upwards [hlim, ae_all_iff.mpr hbound] with t ht hb
    exact le_of_tendsto ht.norm (Eventually.of_forall hb)
  have hfi : IntegrableOn f (Icc a b) μ := hint.mono' hfm hfb
  have hfni (j : ℕ) : IntegrableOn (fn j) (Icc a b) μ :=
    hint.mono' (hmeas j) (hbound j)
  have hfint : IntervalIntegrable f μ a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hfi
  have hfnint (j : ℕ) : IntervalIntegrable (fn j) μ a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hfni j)
  have herr : Tendsto
      (fun j => ∫ t in Icc a b, ‖fn j t - f t‖ ∂μ) atTop (𝓝 0) := by
    have hdom := tendsto_integral_of_dominated_convergence
      (μ := μ.restrict (Icc a b))
      (F := fun j t => ‖fn j t - f t‖) (f := (0 : ℝ → ℝ))
      (fun t => 2 * bound t)
      (fun j => ((hmeas j).sub hfm).norm) (hint.const_mul 2) ?_ ?_
    · simpa only [Pi.zero_apply, MeasureTheory.integral_zero] using hdom
    · intro j
      filter_upwards [hbound j, hfb] with t hj ht
      rw [norm_norm]
      calc
        ‖fn j t - f t‖ ≤ ‖fn j t‖ + ‖f t‖ := norm_sub_le _ _
        _ ≤ bound t + bound t := add_le_add hj ht
        _ = 2 * bound t := (two_mul _).symm
    · filter_upwards [hlim] with t ht
      change Tendsto (fun j => ‖fn j t - f t‖) atTop (𝓝 (0 : ℝ))
      simpa only [sub_self, norm_zero] using
        (ht.sub (tendsto_const_nhds (x := f t))).norm
  have herr' : Tendsto
      (fun j => ∫ t in a..b, ‖fn j t - f t‖ ∂μ) atTop (𝓝 0) := by
    simpa only [integral_of_le hab, integral_Icc_eq_integral_Ioc] using herr
  refine ⟨hfnint, hfint, ?_, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  · simpa only [uIcc_of_le hab] using
      continuousOn_primitive_interval (a := a) (b := b) (μ := μ) (f := f)
        (by simpa only [uIcc_of_le hab] using hfi)
  · intro ε hε
    filter_upwards [herr'.eventually (gt_mem_nhds hε)] with j hj
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    calc
      dist (∫ s in a..t, f s ∂μ) (∫ s in a..t, fn j s ∂μ) =
          ‖∫ s in a..t, fn j s - f s ∂μ‖ := by
        rw [dist_comm, dist_eq_norm,
          integral_sub ((hfnint j).mono_set hsub) (hfint.mono_set hsub)]
      _ ≤ ∫ s in a..t, ‖fn j s - f s‖ ∂μ :=
        norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in a..b, ‖fn j s - f s‖ ∂μ :=
        integral_mono_interval le_rfl ht.1 ht.2
          (Eventually.of_forall fun s => norm_nonneg (fn j s - f s))
          ((hfnint j).sub hfint).norm
      _ < ε := hj

end intervalIntegral
