import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open Set




theorem Real.abs_sub_le_mul_abs_sub_of_deriv_le_below
    {f : ℝ → ℝ} {a b c k : ℝ}
    (hcont : ContinuousOn f (Set.uIcc a b))
    (hk : 0 ≤ k)
    (hcap : ∀ t ∈ Set.uIcc a b, f t ≤ c)
    (hderiv : ∀ t ∈ Set.uIoo a b, f t < c →
      DifferentiableAt ℝ f t ∧ |deriv f t| ≤ k) :
    |f b - f a| ≤ k * |b - a| := by
  classical
  have hordered (x y : ℝ) (hxy : x ≤ y)
      (hc : ContinuousOn f (Icc x y))
      (hbound : ∀ t ∈ Icc x y, f t ≤ c)
      (hd : ∀ t ∈ Ioo x y, f t < c →
        DifferentiableAt ℝ f t ∧ |deriv f t| ≤ k) :
      |f y - f x| ≤ k * (y - x) := by
    by_cases heq : x = y
    · subst y
      simp only [sub_self, abs_zero, mul_zero, le_refl]
    have hxylt : x < y := lt_of_le_of_ne hxy heq
    have hsegment (u v : ℝ) (hu : x ≤ u) (hv : v ≤ y) (huv : u < v)
        (hbelow : ∀ t ∈ Ioo u v, f t < c) :
        |f v - f u| ≤ k * (v - u) := by
      have hsub : Icc u v ⊆ Icc x y :=
        fun _ ht => ⟨hu.trans ht.1, ht.2.trans hv⟩
      have hdiff : DifferentiableOn ℝ f (Ioo u v) := by
        intro t ht
        exact (hd t ⟨hu.trans_lt ht.1, ht.2.trans_le hv⟩
          (hbelow t ht)).1.differentiableWithinAt
      obtain ⟨t, ht, hdt⟩ := exists_deriv_eq_slope f huv (hc.mono hsub) hdiff
      have hdtbound := (hd t ⟨hu.trans_lt ht.1, ht.2.trans_le hv⟩ (hbelow t ht)).2
      have hmul : f v - f u = deriv f t * (v - u) := by
        rw [hdt, div_mul_cancel₀ _ (sub_pos.mpr huv).ne']
      calc
        |f v - f u| = |deriv f t * (v - u)| := congrArg abs hmul
        _ = |deriv f t| * (v - u) := by
          rw [abs_mul, abs_of_pos (sub_pos.mpr huv)]
        _ ≤ k * (v - u) :=
          mul_le_mul_of_nonneg_right hdtbound (sub_nonneg.mpr huv.le)
    let S : Set ℝ := Icc x y ∩ f ⁻¹' {c}
    have hSclosed : IsClosed S :=
      hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hScompact : IsCompact S :=
      isCompact_Icc.of_isClosed_subset hSclosed inter_subset_left
    by_cases hS : S.Nonempty
    · rcases lt_trichotomy (f x) (f y) with hinc | hequal | hdec
      · have hfx : f x < c := hinc.trans_le (hbound y ⟨hxy, le_rfl⟩)
        obtain ⟨t, ht⟩ := hScompact.exists_isLeast hS
        have hft : f t = c := mem_singleton_iff.mp ht.1.2
        have hxt : x < t := by
          apply lt_of_le_of_ne ht.1.1.1
          intro h
          subst t
          exact hfx.ne hft
        have hbelow (r : ℝ) (hr : r ∈ Ioo x t) : f r < c := by
          have hrxy : r ∈ Icc x y := ⟨hr.1.le, hr.2.le.trans ht.1.1.2⟩
          apply lt_of_le_of_ne (hbound r hrxy)
          intro hrc
          have hrS : r ∈ S := ⟨hrxy, hrc⟩
          exact (not_le_of_gt hr.2) (ht.2 hrS)
        have hfirst := hsegment x t le_rfl ht.1.1.2 hxt hbelow
        rw [hft, abs_of_pos (sub_pos.mpr hfx)] at hfirst
        rw [abs_of_pos (sub_pos.mpr hinc)]
        calc
          f y - f x ≤ c - f x := sub_le_sub_right (hbound y ⟨hxy, le_rfl⟩) _
          _ ≤ k * (t - x) := hfirst
          _ ≤ k * (y - x) :=
            mul_le_mul_of_nonneg_left (sub_le_sub_right ht.1.1.2 x) hk
      · rw [hequal, sub_self, abs_zero]
        exact mul_nonneg hk (sub_nonneg.mpr hxy)
      · have hfy : f y < c := hdec.trans_le (hbound x ⟨le_rfl, hxy⟩)
        obtain ⟨t, ht⟩ := hScompact.exists_isGreatest hS
        have hft : f t = c := mem_singleton_iff.mp ht.1.2
        have hty : t < y := by
          apply lt_of_le_of_ne ht.1.1.2
          intro h
          subst t
          exact hfy.ne hft
        have hbelow (r : ℝ) (hr : r ∈ Ioo t y) : f r < c := by
          have hrxy : r ∈ Icc x y := ⟨ht.1.1.1.trans hr.1.le, hr.2.le⟩
          apply lt_of_le_of_ne (hbound r hrxy)
          intro hrc
          have hrS : r ∈ S := ⟨hrxy, hrc⟩
          exact (not_le_of_gt hr.1) (ht.2 hrS)
        have hlast := hsegment t y ht.1.1.1 le_rfl hty hbelow
        rw [hft, abs_sub_comm, abs_of_pos (sub_pos.mpr hfy)] at hlast
        rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hdec)]
        calc
          f x - f y ≤ c - f y := sub_le_sub_right (hbound x ⟨le_rfl, hxy⟩) _
          _ ≤ k * (y - t) := hlast
          _ ≤ k * (y - x) :=
            mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1.1.1 y) hk
    · apply hsegment x y le_rfl le_rfl hxylt
      intro t ht
      apply lt_of_le_of_ne (hbound t ⟨ht.1.le, ht.2.le⟩)
      intro htc
      exact hS ⟨t, ⟨ht.1.le, ht.2.le⟩, htc⟩
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact hordered a b hab
      (by simpa only [uIcc_of_le hab] using hcont)
      (by simpa only [uIcc_of_le hab] using hcap)
      (by simpa only [uIoo_of_le hab] using hderiv)
  · rw [abs_sub_comm (f b) (f a), abs_sub_comm b a,
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hordered b a hba
      (by simpa only [uIcc_of_ge hba] using hcont)
      (by simpa only [uIcc_of_ge hba] using hcap)
      (by simpa only [uIoo_of_ge hba] using hderiv)
