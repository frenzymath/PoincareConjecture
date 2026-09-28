import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Mollification
import Mathlib.Topology.MetricSpace.Thickening

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ} {U V K : Set (Spacetime n)}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

private theorem convolution_indicator_eq {η u : Spacetime n → ℝ}
    {z : Spacetime n} (hs : tsupport (translatedKernel η z) ⊆ K) :
    lebesgueConvolution η (K.indicator u) z = lebesgueConvolution η u z := by
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y ∈ K
  · rw [indicator_of_mem hy]
  · have he : η (z - y) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := translatedKernel η z) (fun h => hy (hs h))
    simp [he]

private theorem translated_support_mono {η κ : Spacetime n → ℝ}
    (hs : tsupport κ ⊆ tsupport η) (z : Spacetime n) :
    tsupport (translatedKernel κ z) ⊆ tsupport (translatedKernel η z) := by
  change tsupport (κ ∘ Homeomorph.subLeft z) ⊆ tsupport (η ∘ Homeomorph.subLeft z)
  rw [tsupport_comp_eq_preimage, tsupport_comp_eq_preimage]
  exact preimage_mono hs

private theorem exists_translated_compact_buffer {η : Spacetime n → ℝ}
    {z : Spacetime n} (hU : IsOpen U) (hηc : HasCompactSupport η)
    (hs : tsupport (translatedKernel η z) ⊆ U) :
    ∃ (V K : Set (Spacetime n)), IsOpen V ∧ z ∈ V ∧ IsCompact K ∧ K ⊆ U ∧
      ∀ w ∈ V, tsupport (translatedKernel η w) ⊆ K := by
  have hc : IsCompact (tsupport (translatedKernel η z)) :=
    hηc.comp_homeomorph (Homeomorph.subLeft z)
  obtain ⟨δ, hδ, hδU⟩ := hc.exists_cthickening_subset_open hU hs
  refine ⟨ball z δ, cthickening δ (tsupport (translatedKernel η z)),
    isOpen_ball, mem_ball_self hδ, hc.cthickening, hδU, ?_⟩
  intro w hw y hy
  have hymem : z - w + y ∈ tsupport (translatedKernel η z) := by
    change z - w + y ∈ tsupport (η ∘ Homeomorph.subLeft z)
    change y ∈ tsupport (η ∘ Homeomorph.subLeft w) at hy
    rw [tsupport_comp_eq_preimage] at hy ⊢
    simpa only [mem_preimage, Homeomorph.subLeft_apply,
      show z - (z - w + y) = w - y by abel] using hy
  apply mem_cthickening_of_dist_le y (z - w + y) δ _ hymem
  have he : y - (z - w + y) = w - z := by abel
  simpa only [dist_eq_norm, he] using (mem_ball.mp hw).le

theorem contDiffAt_lebesgueConvolution_locallyIntegrableOn
    {n : ℕ} {U : Set (Spacetime n)} {η u : Spacetime n → ℝ}
    {z : Spacetime n} (hU : IsOpen U)
    (hu : LocallyIntegrableOn u U volume)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : tsupport (translatedKernel η z) ⊆ U) :
    ContDiffAt ℝ ∞ (lebesgueConvolution η u) z := by
  obtain ⟨V, K, hV, hzV, hK, hKU, hsupport⟩ :=
    exists_translated_compact_buffer hU hηc hs
  have hi : Integrable (K.indicator u) :=
    (hu.integrableOn_compact_subset hKU hK).integrable_indicator hK.measurableSet
  apply (contDiff_lebesgueConvolution hi.locallyIntegrable hη hηc).contDiffAt.congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hzV] with w hw
  exact (convolution_indicator_eq (hsupport w hw)).symm

theorem fderiv_lebesgueConvolution_locallyIntegrableOn
    {n : ℕ} {U : Set (Spacetime n)} {η u : Spacetime n → ℝ}
    {z v : Spacetime n} (hU : IsOpen U)
    (hu : LocallyIntegrableOn u U volume)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : tsupport (translatedKernel η z) ⊆ U) :
    fderiv ℝ (lebesgueConvolution η u) z v =
      lebesgueConvolution (fun y => fderiv ℝ η y v) u z := by
  obtain ⟨V, K, hV, hzV, hK, hKU, hsupport⟩ :=
    exists_translated_compact_buffer hU hηc hs
  have hi : Integrable (K.indicator u) :=
    (hu.integrableOn_compact_subset hKU hK).integrable_indicator hK.measurableSet
  have he : lebesgueConvolution η u =ᶠ[𝓝 z] lebesgueConvolution η (K.indicator u) := by
    filter_upwards [hV.mem_nhds hzV] with w hw
    exact (convolution_indicator_eq (hsupport w hw)).symm
  rw [he.fderiv_eq, fderiv_lebesgueConvolution hi.locallyIntegrable hη hηc]
  exact convolution_indicator_eq
    ((translated_support_mono (tsupport_fderiv_apply_subset ℝ v) z).trans (hsupport z hzV))

theorem fderiv_lebesgueConvolution_eq_weakDerivative
    {n : ℕ} {U : Set (Spacetime n)} {u g η : Spacetime n → ℝ}
    {z v : Spacetime n} (hU : IsOpen U)
    (hu : LocallyIntegrableOn u U volume)
    (hg : LocallyIntegrableOn g U volume)
    (hw : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ y in U, φ y * g y) = -(∫ y in U, fderiv ℝ φ y v * u y))
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : tsupport (translatedKernel η z) ⊆ U) :
    fderiv ℝ (lebesgueConvolution η u) z v = lebesgueConvolution η g z := by
  have ht : ContDiff ℝ ∞ (translatedKernel η z) :=
    hη.comp (contDiff_const.sub contDiff_id)
  have htc : HasCompactSupport (translatedKernel η z) :=
    hηc.comp_homeomorph (Homeomorph.subLeft z)
  have htest := hw (translatedKernel η z) ht htc hs
  have htderiv (y : Spacetime n) :
      fderiv ℝ (translatedKernel η z) y v = -fderiv ℝ η (z - y) v := by
    have hd := (hη.differentiable (by simp) (z - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const z y).sub (hasFDerivAt_id y))
    change HasFDerivAt (translatedKernel η z) _ y at hd
    rw [hd.fderiv]
    simp
  have hleft : (∫ y in U, translatedKernel η z y * g y) =
      lebesgueConvolution η g z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hz : translatedKernel η z y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
    simp only [hz, zero_mul]
  have hright : (∫ y in U, fderiv ℝ η (z - y) v * u y) =
      lebesgueConvolution (fun y => fderiv ℝ η y v) u z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hds := (translated_support_mono (tsupport_fderiv_apply_subset ℝ v) z).trans hs
    have hz : translatedKernel (fun y => fderiv ℝ η y v) z y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (hds h))
    exact mul_eq_zero_of_left hz _
  simp only [htderiv, neg_mul, integral_neg, neg_neg] at htest
  rw [hleft, hright] at htest
  rw [fderiv_lebesgueConvolution_locallyIntegrableOn hU hu hη hηc hs]
  exact htest.symm

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
