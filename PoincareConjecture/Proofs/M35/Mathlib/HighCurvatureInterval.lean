import PoincareConjecture.Proofs.M35.Mathlib.ReciprocalBlowup
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false

open Filter Set
open scoped Topology



theorem exists_last_threshold_crossing
    {f : ℝ → ℝ} {a b H s : ℝ} (hcont : ContinuousOn f (Ico a b))
    (hblow : Tendsto f (𝓝[<] b) atTop) (hs : s ∈ Ico a b) (hfs : f s ≤ H) :
    ∃ c ∈ Ico s b, f c = H ∧ ∀ u ∈ Ioo c b, H < f u := by
  obtain ⟨r₀, hr₀, htail⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    (hblow.eventually_gt_atTop H)
  obtain ⟨r, hr, hrb⟩ := exists_between (max_lt hs.2 hr₀)
  have hsr : s ≤ r := (lt_of_le_of_lt (le_max_left s r₀) hr).le
  have hr₀r : r₀ < r := lt_of_le_of_lt (le_max_right s r₀) hr
  have hfr : H < f r := htail ⟨hr₀r, hrb⟩
  have hsub : Icc s r ⊆ Ico a b := fun u hu =>
    ⟨hs.1.trans hu.1, hu.2.trans_lt hrb⟩
  have hclosed : IsClosed (Icc s r ∩ f ⁻¹' Iic H) :=
    (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  obtain ⟨c, hc, hlast⟩ :=
    (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).exists_isGreatest
      ⟨s, ⟨⟨le_rfl, hsr⟩, hfs⟩⟩
  have hcdom : c ∈ Ico s b := ⟨hc.1.1, hc.1.2.trans_lt hrb⟩
  have hfc : f c = H := by
    obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc hc.1.2
      (hcont.mono (fun u hu => hsub ⟨hc.1.1.trans hu.1, hu.2⟩)) ⟨hc.2, hfr.le⟩
    have hzc : z ≤ c := hlast ⟨⟨hc.1.1.trans hz.1, hz.2⟩, hfz.le⟩
    simpa only [le_antisymm hzc hz.1] using hfz
  refine ⟨c, hcdom, hfc, ?_⟩
  intro u hu
  by_cases hur : u ≤ r
  · by_contra hfu
    exact (not_le_of_gt hu.1) (hlast ⟨⟨hc.1.1.trans hu.1.le, hur⟩, not_lt.mp hfu⟩)
  · exact htail ⟨hr₀r.trans (lt_of_not_ge hur), hu.2⟩



theorem inv_mul_time_sub_le_of_eventual_quadratic_bound
    {f f' : ℝ → ℝ} {a b A H t : ℝ} (hA : 0 < A) (hH : 0 < H)
    (hpos : ∀ u ∈ Ico a b, 0 < f u)
    (hderiv : ∀ u ∈ Ico a b, HasDerivWithinAt f (f' u) (Ico a b) u)
    (hbound : ∀ u ∈ Ico a b, H ≤ f u → f' u ≤ A * (f u) ^ 2)
    (hblow : Tendsto f (𝓝[<] b) atTop) (ht : t ∈ Ico a b)
    (hnear : A * H * (b - t) < 1) : (A * (b - t))⁻¹ ≤ f t := by
  have hcont : ContinuousOn f (Ico a b) := fun u hu => (hderiv u hu).continuousWithinAt
  have hhigh : ∀ s ∈ Ico t b, H < f s := by
    intro s hs
    by_contra hfs
    obtain ⟨c, hc, hfc, htail⟩ := exists_last_threshold_crossing hcont hblow
      ⟨ht.1.trans hs.1, hs.2⟩ (not_lt.mp hfs)
    have hsub : Ico c b ⊆ Ico a b := fun u hu =>
      ⟨ht.1.trans (hs.1.trans (hc.1.trans hu.1)), hu.2⟩
    have hge : ∀ u ∈ Ico c b, H ≤ f u := by
      intro u hu
      rcases hu.1.eq_or_lt with hcu | hcu
      · simpa only [← hcu, hfc] using (le_refl H)
      · exact (htail u ⟨hcu, hu.2⟩).le
    have hrate := inv_mul_time_sub_le_of_tendsto_atTop hA
      (fun u hu => hpos u (hsub hu))
      (fun u hu => (hderiv u (hsub hu)).mono hsub)
      (fun u hu => hbound u (hsub hu) (hge u hu)) hblow c ⟨le_rfl, hc.2⟩
    rw [hfc] at hrate
    have hone : 1 ≤ A * H * (b - c) := by
      have := mul_le_mul_of_nonneg_left hrate (mul_pos hA (sub_pos.mpr hc.2)).le
      rw [mul_inv_cancel₀ (mul_pos hA (sub_pos.mpr hc.2)).ne'] at this
      nlinarith
    have htime : A * H * (b - c) ≤ A * H * (b - t) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left (hs.1.trans hc.1) b) (mul_pos hA hH).le
    exact (not_lt_of_ge (hone.trans htime)) hnear
  have hsub : Ico t b ⊆ Ico a b := fun u hu => ⟨ht.1.trans hu.1, hu.2⟩
  exact inv_mul_time_sub_le_of_tendsto_atTop hA
    (fun u hu => hpos u (hsub hu))
    (fun u hu => (hderiv u (hsub hu)).mono hsub)
    (fun u hu => hbound u (hsub hu) (hhigh u hu).le) hblow t ⟨le_rfl, ht.2⟩
