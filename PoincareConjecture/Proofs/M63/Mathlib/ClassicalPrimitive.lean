import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

theorem hasDerivAt_of_ae_continuous_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b) {f R Q : ℝ → E}
    (hf : IntervalIntegrable f volume a b) (hR : ContinuousOn R (Icc a b))
    (heq : f =ᵐ[volume.restrict (Ioc a b)] R)
    (hprimitive : ∀ s ∈ Icc a b, Q s = Q a + ∫ r in a..s, f r)
    {t : ℝ} (ht : t ∈ Ioo a b) : HasDerivAt Q (R t) t := by
  have heq' (s : ℝ) (hs : s ∈ Icc a b) : f =ᵐ[volume.restrict (uIoc a s)] R := by
    rw [uIoc_of_le hs.1]
    exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl hs.2) heq
  have hft : IntervalIntegrable f volume a t := hf.mono_set (by
    simpa only [uIcc_of_le ht.1.le, uIcc_of_le hab] using
      (Icc_subset_Icc le_rfl ht.2.le))
  have hRt : IntervalIntegrable R volume a t := hft.congr_ae (heq' t (Ioo_subset_Icc_self ht))
  have hRopen : ContinuousOn R (Ioo a b) := hR.mono Ioo_subset_Icc_self
  have hFTC := intervalIntegral.integral_hasDerivAt_right hRt
    (hRopen.stronglyMeasurableAtFilter isOpen_Ioo t ht)
    (hRopen.continuousAt (isOpen_Ioo.mem_nhds ht))
  have hderiv : HasDerivAt (fun s => Q a + ∫ r in a..s, R r) (R t) t := by
    exact hFTC.const_add (Q a)
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  rw [hprimitive s (Ioo_subset_Icc_self hs),
    intervalIntegral.integral_congr_ae_restrict (heq' s (Ioo_subset_Icc_self hs))]
