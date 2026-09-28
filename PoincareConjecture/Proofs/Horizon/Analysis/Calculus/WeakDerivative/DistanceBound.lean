import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic










open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Poincare.Analysis.WeakDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem segment_bound {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (z v : E) {C : ℝ}
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      DifferentiableAt ℝ f (z + t • v) ∧ ‖fderiv ℝ f (z + t • v)‖ ≤ C) :
    |f (z + v) - f z| ≤ C * ‖v‖ := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  let F : ℝ → ℝ := fun t => f (z + t • v)
  have hF : LipschitzWith (K * (0 + ‖L‖₊)) F :=
    hf.comp ((LipschitzWith.const z).add L.lipschitz)
  have hAC := hF.lipschitzOnWith.absolutelyContinuousOnInterval (a := 0) (b := 1)
  have hbound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      |deriv F t| ≤ C * ‖v‖ := by
    filter_upwards [hderiv] with t ht
    have hpath : HasDerivAt (fun t : ℝ => z + t • v) v t := by
      simpa [L] using L.hasDerivAt.const_add z
    have hd := ht.1.hasFDerivAt.comp_hasDerivAt t hpath
    rw [show deriv F t = fderiv ℝ f (z + t • v) v from hd.deriv]
    exact (fderiv ℝ f (z + t • v)).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v))
  calc
    |f (z + v) - f z| = |∫ t in (0 : ℝ)..1, deriv F t| := by
      rw [hAC.integral_deriv_eq_sub]
      simp [F]
    _ ≤ ∫ t in (0 : ℝ)..1, |deriv F t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ _t in (0 : ℝ)..1, C * ‖v‖ :=
      intervalIntegral.integral_mono_ae_restrict (by norm_num)
        hAC.intervalIntegrable_deriv.abs intervalIntegrable_const hbound
    _ = C * ‖v‖ := by simp




theorem lipschitzOnWith_of_ae_fderiv_bound
    (μ : Measure E) [μ.IsAddHaarMeasure] {U G : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hG : MeasurableSet G)
    (hfull : ∀ᵐ x ∂μ, x ∈ U → x ∈ G)
    {f : E → ℝ} {K C : ℝ≥0} (hf : LipschitzWith K f)
    (hderiv : ∀ x ∈ U ∩ G, DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x‖ ≤ C) :
    LipschitzOnWith C f U := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let v := y - x
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have hfull' : ∀ᵐ z ∂μ, z ∈ Uᶜ ∪ G := by
    filter_upwards [hfull] with z hz
    by_cases hzU : z ∈ U
    · exact Or.inr (hz hzU)
    · exact Or.inl hzU
  have hline : ∀ᵐ z ∂μ, ∀ᵐ t ∂volume, z + t • v ∈ Uᶜ ∪ G :=
    (ae_ae_add_linearMap_mem_iff L.toLinearMap volume μ
      (hU.measurableSet.compl.union hG)).mpr hfull'
  have hseg : (fun t : ℝ => x + t • v) '' Icc 0 1 ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hconv.add_smul_sub_mem hx hy ht
  obtain ⟨δ, hδ, hδU⟩ :=
    (isCompact_Icc.image (by fun_prop : Continuous (fun t : ℝ => x + t • v))).exists_thickening_subset_open hU hseg
  have hnear : ∀ z, dist z x < δ → (∀ᵐ (t : ℝ) ∂volume, z + t • v ∈ Uᶜ ∪ G) →
      |f (z + v) - f z| ≤ (C : ℝ) * ‖v‖ := by
    intro z hz hgood
    apply segment_bound hf z v
    filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem measurableSet_Icc] with t ht htI
    have htU : z + t • v ∈ U := by
      apply hδU
      apply Metric.mem_thickening_iff.mpr
      refine ⟨x + t • v, ⟨t, htI, rfl⟩, ?_⟩
      simpa only [dist_add_right] using hz
    exact hderiv _ ⟨htU, ht.resolve_left (not_not.mpr htU)⟩
  have hclosed : IsClosed {z : E | |f (z + v) - f z| ≤ (C : ℝ) * ‖v‖} :=
    isClosed_le ((hf.continuous.comp (continuous_id.add continuous_const)).sub
      hf.continuous).abs continuous_const
  have hxclosed : x ∈ {z : E | |f (z + v) - f z| ≤ (C : ℝ) * ‖v‖} := by
    apply hclosed.closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨z, hz, hzx⟩ := (μ.dense_of_ae hline).exists_dist_lt x (lt_min hδ hε)
    refine ⟨z, hnear z ?_ hz, hzx.trans_le (min_le_right _ _)⟩
    exact (dist_comm z x).trans_lt (hzx.trans_le (min_le_left _ _))
  simpa [v, Real.dist_eq, dist_eq_norm, abs_sub_comm, norm_sub_rev] using hxclosed



theorem lipschitzOnWith_of_ae_fderiv_bound_on
    (μ : Measure E) [μ.IsAddHaarMeasure] {U G : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hG : MeasurableSet G)
    (hfull : ∀ᵐ x ∂μ, x ∈ U → x ∈ G)
    {f : E → ℝ} {K C : ℝ≥0} (hf : LipschitzOnWith K f U)
    (hderiv : ∀ x ∈ U ∩ G, DifferentiableAt ℝ f x ∧ ‖fderiv ℝ f x‖ ≤ C) :
    LipschitzOnWith C f U := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  have hbound : LipschitzOnWith C F U :=
    lipschitzOnWith_of_ae_fderiv_bound μ hU hconv hG hfull hF (by
      intro x hx
      have hlocal : f =ᶠ[𝓝 x] F :=
        heq.eventuallyEq_of_mem (hU.mem_nhds hx.1)
      obtain ⟨hd, hb⟩ := hderiv x hx
      exact ⟨hd.congr_of_eventuallyEq hlocal.symm, hlocal.fderiv_eq (𝕜 := ℝ) ▸ hb⟩)
  intro x hx y hy
  rw [heq hx, heq hy]
  exact hbound hx hy

end Poincare.Analysis.WeakDerivative
