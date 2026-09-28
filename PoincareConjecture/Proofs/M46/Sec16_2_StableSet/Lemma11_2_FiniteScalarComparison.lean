import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.FiniteEventInduction
import Mathlib.Analysis.Calculus.Deriv.MeanValue










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.Proofs.M46



theorem image_sub_le_mul_sub_of_finite_deriv_exceptions
    {f f' : ℝ → ℝ} {a b C : ℝ} {events : Set ℝ}
    (hab : a ≤ b) (hfinite : (events ∩ Ioc a b).Finite)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, t ∉ events → HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, t ∉ events → f' t ≤ C) :
    f b - f a ≤ C * (b - a) := by
  let Q (t : ℝ) : Prop := f t - f a ≤ C * (t - a)
  apply finite_event_forward_induction hab hfinite Q
    (by simp only [Q, sub_self, mul_zero, le_refl])
  · intro s hs t ht hst hfree hQs
    have hinternal (z : ℝ) (hz : z ∈ Ioo s t) : z ∈ Ioo a b :=
      ⟨hs.1.trans_lt hz.1, hz.2.trans_le ht.2⟩
    have hnot (z : ℝ) (hz : z ∈ Ioo s t) : z ∉ events :=
      fun he => Set.disjoint_left.mp hfree he ⟨hz.1, hz.2.le⟩
    have hdiff : DifferentiableOn ℝ f (interior (Icc s t)) := by
      rw [interior_Icc]
      intro z hz
      exact (hderiv z (hinternal z hz) (hnot z hz)).differentiableAt.differentiableWithinAt
    have hrate : ∀ z ∈ interior (Icc s t), deriv f z ≤ C := by
      rw [interior_Icc]
      intro z hz
      rw [(hderiv z (hinternal z hz) (hnot z hz)).deriv]
      exact hbound z (hinternal z hz) (hnot z hz)
    have hinc := (convex_Icc s t).image_sub_le_mul_sub_of_deriv_le
      (hcont.mono (Icc_subset_Icc hs.1 ht.2)) hdiff hrate
      s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
    dsimp only [Q] at hQs ⊢
    nlinarith
  · intro t ht hbefore
    have hleft : ContinuousWithinAt f (Iio t) t := by
      apply (hcont t ⟨ht.2.1.le, ht.2.2⟩).mono_of_mem_nhdsWithin
      exact Filter.mem_of_superset (Ico_mem_nhdsLT ht.2.1)
        (fun s hs => ⟨hs.1, hs.2.le.trans ht.2.2⟩)
    have hclock : Tendsto (fun s : ℝ => C * (s - a)) (𝓝[<] t) (𝓝 (C * (t - a))) := by
      have hc : Continuous (fun s : ℝ => C * (s - a)) := by fun_prop
      exact hc.continuousAt.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto (hleft.sub_const (f a)) hclock
    filter_upwards [Ico_mem_nhdsLT ht.2.1] with s hs
    exact hbefore s hs




theorem scalar_le_four_inv_sq_of_finite_events
    {f f' : ℝ → ℝ} {duration B r : ℝ} {events : Set ℝ}
    (hB : 0 < B) (hr : 0 < r)
    (hfinite : (events ∩ Ioc 0 duration).Finite)
    (hcont : ContinuousOn f (Icc 0 duration))
    (hderiv : ∀ t ∈ Ioo 0 duration, t ∉ events → HasDerivAt f (f' t) t)
    (hinitial : f 0 ≤ 2 * r⁻¹ ^ 2)
    (hrate : ∀ t ∈ Ioo 0 duration, t ∉ events →
      r⁻¹ ^ 2 ≤ f t → f' t ≤ B * f t ^ 2)
    (hshort : 64 * B * r⁻¹ ^ 2 * duration ≤ 1) :
    ∀ t ∈ Icc 0 duration, f t ≤ 4 * r⁻¹ ^ 2 := by
  intro t ht
  by_contra hbad
  have hhigh : 4 * r⁻¹ ^ 2 < f t := lt_of_not_ge hbad
  have hq : 0 < r⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hr)
  have hct : ContinuousOn f (Icc 0 t) := hcont.mono (Icc_subset_Icc_right ht.2)
  have hupperClosed : IsClosed (Icc (0 : ℝ) t ∩ f ⁻¹' Ici (4 * r⁻¹ ^ 2)) :=
    hct.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  obtain ⟨b, hb, hfirst⟩ :=
    (isCompact_Icc.of_isClosed_subset hupperClosed inter_subset_left).exists_isLeast
      ⟨t, ⟨⟨ht.1, le_rfl⟩, hhigh.le⟩⟩
  have hbpos : 0 < b := by
    apply lt_of_le_of_ne hb.1.1
    intro heq
    have h : 4 * r⁻¹ ^ 2 ≤ f b := hb.2
    rw [← heq] at h
    linarith
  have hbvalue : f b = 4 * r⁻¹ ^ 2 := by
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hbpos.le
      (hct.mono (Icc_subset_Icc_right hb.1.2))
      ⟨hinitial.trans (by linarith), hb.2⟩
    have hbs : b ≤ s := hfirst ⟨⟨hs.1, hs.2.trans hb.1.2⟩, hfs.ge⟩
    simpa only [le_antisymm hbs hs.2] using hfs
  have hlowerClosed : IsClosed (Icc (0 : ℝ) b ∩ f ⁻¹' Iic (2 * r⁻¹ ^ 2)) :=
    (hct.mono (Icc_subset_Icc_right hb.1.2)).preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Iic
  obtain ⟨a, ha, hlast⟩ :=
    (isCompact_Icc.of_isClosed_subset hlowerClosed inter_subset_left).exists_isGreatest
      ⟨0, ⟨⟨le_rfl, hbpos.le⟩, hinitial⟩⟩
  have hab : a < b := by
    apply lt_of_le_of_ne ha.1.2
    intro heq
    have h : f a ≤ 2 * r⁻¹ ^ 2 := ha.2
    rw [heq, hbvalue] at h
    linarith
  have havalue : f a = 2 * r⁻¹ ^ 2 := by
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hab.le
      (hct.mono (Icc_subset_Icc ha.1.1 hb.1.2))
      ⟨ha.2, by rw [hbvalue]; linarith⟩
    have hsa : s ≤ a := hlast ⟨⟨ha.1.1.trans hs.1, hs.2⟩, hfs.le⟩
    simpa only [le_antisymm hsa hs.1] using hfs
  have hband (s : ℝ) (hs : s ∈ Ioo a b) :
      2 * r⁻¹ ^ 2 ≤ f s ∧ f s ≤ 4 * r⁻¹ ^ 2 := by
    constructor
    · by_contra hlo
      exact not_le_of_gt hs.1
        (hlast ⟨⟨ha.1.1.trans hs.1.le, hs.2.le⟩, (lt_of_not_ge hlo).le⟩)
    · by_contra hhi
      exact not_le_of_gt hs.2
        (hfirst ⟨⟨ha.1.1.trans hs.1.le, hs.2.le.trans hb.1.2⟩,
          (lt_of_not_ge hhi).le⟩)
  have hwindow (s : ℝ) (hs : s ∈ Ioo a b) : s ∈ Ioo 0 duration :=
    ⟨ha.1.1.trans_lt hs.1, hs.2.trans_le (hb.1.2.trans ht.2)⟩
  have hrateBand (s : ℝ) (hs : s ∈ Ioo a b) (hne : s ∉ events) :
      f' s ≤ 16 * B * r⁻¹ ^ 4 := by
    obtain ⟨hlo, hhi⟩ := hband s hs
    have hsquare : f s ^ 2 ≤ 16 * r⁻¹ ^ 4 := by nlinarith
    have h := (hrate s (hwindow s hs) hne (by linarith)).trans
      (mul_le_mul_of_nonneg_left hsquare hB.le)
    nlinarith
  have hinc := image_sub_le_mul_sub_of_finite_deriv_exceptions hab.le
    (hfinite.subset (fun s hs =>
      ⟨hs.1, ha.1.1.trans_lt hs.2.1, hs.2.2.trans (hb.1.2.trans ht.2)⟩))
    (hcont.mono (Icc_subset_Icc ha.1.1 (hb.1.2.trans ht.2)))
    (fun s hs hne => hderiv s (hwindow s hs) hne) hrateBand
  rw [havalue, hbvalue] at hinc
  have hlength : b - a ≤ duration := by linarith [ha.1.1, hb.1.2, ht.2]
  have hlong := mul_le_mul_of_nonneg_left hlength
    (by positivity : 0 ≤ 16 * B * r⁻¹ ^ 4)
  have hscaled := mul_le_mul_of_nonneg_right hshort (by positivity : 0 ≤ r⁻¹ ^ 2)
  nlinarith

end PoincareConjecture.Proofs.M46
