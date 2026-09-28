import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzDistance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

private theorem auxiliary_edist_le_energy_closed
    (F : GeneralizedFlowSpacetime n X time I) {gamma : ℝ → F.Point}
    {sigma : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hC : 0 < C)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel n) 1 gamma (Icc a b))
    (hsigma : IntervalIntegrable sigma volume a b) (hnonneg : ∀ s, 0 ≤ sigma s)
    (hvelocity : ∀ s ∈ Ioo a b, M14.auxiliarySpacetimeForm F (gamma s)
      (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) gamma s 1)
      (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) gamma s 1) ≤ sigma s) :
    M14.auxiliarySpacetimeEDist F (gamma a) (gamma b) ≤ ENNReal.ofReal
      (((∫ s in a..b, sigma s) + (b - a) * C ^ 2) / (2 * C)) := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel n) : F.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric F).toRiemannianMetric⟩
  have hint : IntervalIntegrable (fun s => (sigma s + C ^ 2) / (2 * C)) volume a b :=
    (hsigma.add intervalIntegrable_const).div_const _
  apply (riemannianEDist_le_pathELength hgamma rfl rfl hab).trans
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  calc
    _ ≤ ∫⁻ s in Ioo a b, ENNReal.ofReal ((sigma s + C ^ 2) / (2 * C)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      have hnorm : M14.auxiliarySpacetimeForm F (gamma s)
          (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) gamma s 1)
          (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) gamma s 1) =
            ‖mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) gamma s 1‖ ^ 2 :=
        real_inner_self_eq_norm_sq (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) gamma s 1)
      have hv := hvelocity s hs
      rw [hnorm] at hv
      apply (le_div_iff₀ (by positivity : 0 < 2 * C)).mpr
      nlinarith [sq_nonneg (‖mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) gamma s 1‖ - C)]
    _ = ENNReal.ofReal (∫ s in a..b, (sigma s + C ^ 2) / (2 * C)) := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
      symm
      apply ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hint)
      exact ae_of_all _ (fun s => div_nonneg (add_nonneg (hnonneg s) (sq_nonneg C))
        (by positivity))
    _ = _ := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_add hsigma intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]



theorem auxiliary_edist_le_energy_of_interior_regular
    (F : GeneralizedFlowSpacetime n X time I) {gamma : ℝ → F.Point}
    {sigma : ℝ → ℝ} {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (hgamma : ContinuousOn gamma (Icc a b))
    (hregular : ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel n) 1 gamma (Ioo a b))
    (hsigma : IntervalIntegrable sigma volume a b) (hnonneg : ∀ s, 0 ≤ sigma s)
    (hvelocity : ∀ s ∈ Ioo a b, M14.auxiliarySpacetimeForm F (gamma s)
      (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) gamma s 1)
      (mfderiv 𝓘(ℝ, ℝ) (spacetimeModel n) gamma s 1) ≤ sigma s) :
    M14.auxiliarySpacetimeEDist F (gamma a) (gamma b) ≤ ENNReal.ofReal
      (((∫ s in a..b, sigma s) + (b - a) * C ^ 2) / (2 * C)) := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel n) : F.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric F).toRiemannianMetric⟩
  let : EMetricSpace F.Point := .ofRiemannianMetric (spacetimeModel n) F.Point
  let bound := ((∫ s in a..b, sigma s) + (b - a) * C ^ 2) / (2 * C)
  have hordered (s t : ℝ) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (hst : s ≤ t) :
      M14.auxiliarySpacetimeEDist F (gamma s) (gamma t) ≤ ENNReal.ofReal bound := by
    have hsub : Icc s t ⊆ Ioo a b := Icc_subset_Ioo hs.1 ht.2
    have hint := hsigma.mono_set (by
      rw [uIcc_of_le hst, uIcc_of_le hab.le]
      exact Icc_subset_Icc hs.1.le ht.2.le)
    have hlength := auxiliary_edist_le_energy_closed F hst hC (hregular.mono hsub)
      hint hnonneg (fun r hr => hvelocity r (hsub ⟨hr.1.le, hr.2.le⟩))
    apply hlength.trans (ENNReal.ofReal_le_ofReal ?_)
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply add_le_add
    · exact intervalIntegral.integral_mono_interval hs.1.le hst ht.2.le
        (ae_of_all _ hnonneg) hsigma
    · exact mul_le_mul_of_nonneg_right (by linarith [hs.1, ht.2]) (sq_nonneg C)
  have hopen (s : ℝ) (hs : s ∈ Ioo a b) (t : ℝ) (ht : t ∈ Ioo a b) :
      edist (gamma s) (gamma t) ≤ ENNReal.ofReal bound := by
    rcases le_total s t with hst | hts
    · exact hordered s t hs ht hst
    · rw [edist_comm]
      exact hordered t s ht hs hts
  have hleft (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Ioo a b) :
      edist (gamma s) (gamma t) ≤ ENNReal.ofReal bound := by
    apply le_on_closure (fun r hr => hopen r hr t ht)
    · simpa only [closure_Ioo hab.ne, Function.comp_def] using
        continuous_edist.comp_continuousOn (hgamma.prodMk continuousOn_const)
    · exact continuousOn_const
    · simpa only [closure_Ioo hab.ne] using hs
  change edist (gamma a) (gamma b) ≤ ENNReal.ofReal bound
  apply le_on_closure (fun r hr => hleft a ⟨le_rfl, hab.le⟩ r hr)
  · simpa only [closure_Ioo hab.ne, Function.comp_def] using
      continuous_edist.comp_continuousOn (continuousOn_const.prodMk hgamma)
  · exact continuousOn_const
  · simp only [closure_Ioo hab.ne, mem_Icc, le_refl, and_true]
    exact hab.le

end PoincareConjecture.Proofs.M46
