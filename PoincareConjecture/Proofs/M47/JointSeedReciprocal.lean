import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture.M47



theorem jointSeed_first_future_level {u : ℝ → ℝ} {s t L : ℝ}
    (hst : s ≤ t) (hu : ContinuousOn u (Icc s t))
    (hs : L < u s) (ht : u t ≤ L) :
    ∃ r ∈ Ioc s t, u r = L ∧ ∀ w ∈ Ico s r, L < u w := by
  have hclosed : IsClosed (Icc s t ∩ u ⁻¹' Iic L) :=
    hu.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  obtain ⟨r, hr, hmin⟩ :=
    (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).exists_isLeast
      ⟨t, ⟨⟨hst, le_rfl⟩, ht⟩⟩
  have hsr : s < r := by
    apply lt_of_le_of_ne hr.1.1
    intro heq
    have h := hr.2
    rw [← heq] at h
    exact not_le_of_gt hs h
  have hvalue : u r = L := by
    obtain ⟨w, hw, huw⟩ := intermediate_value_Icc' hsr.le
      (hu.mono (Icc_subset_Icc le_rfl hr.1.2)) ⟨hr.2, hs.le⟩
    have hrw : r ≤ w := hmin ⟨⟨hw.1, hw.2.trans hr.1.2⟩, huw.le⟩
    simpa only [le_antisymm hw.2 hrw] using huw
  refine ⟨r, ⟨hsr, hr.1.2⟩, hvalue, ?_⟩
  intro w hw
  apply lt_of_not_ge
  intro hwL
  exact not_le_of_gt hw.2 (hmin ⟨⟨hw.1, hw.2.le.trans hr.1.2⟩, hwL⟩)



theorem jointSeed_backward_scalar_comparison
    {u : ℝ → ℝ} {a b A L : ℝ} (_hab : a ≤ b) (hA : 0 ≤ A) (hL : 0 < L)
    (hu : ContinuousOn u (Icc a b)) (hterminal : u b ≤ L)
    (hderiv : ∀ w ∈ Ioo a b, L < u w →
      ∃ z : ℝ, HasDerivAt u z w ∧ |z| ≤ A * u w ^ 2)
    (hshort : A * L * (b - a) ≤ 1 / 4) :
    ∀ s ∈ Icc a b, u s ≤ 4 * L / 3 := by
  intro s hs
  by_cases hhigh : L < u s
  · obtain ⟨r, hr, hvalue, hlevel⟩ := jointSeed_first_future_level hs.2
      (hu.mono (Icc_subset_Icc hs.1 le_rfl)) hhigh hterminal
    have hpositive : ∀ w ∈ Icc s r, 0 < u w := by
      intro w hw
      rcases lt_or_eq_of_le hw.2 with hwr | rfl
      · exact hL.trans (hlevel w ⟨hw.1, hwr⟩)
      · rwa [hvalue]
    have hsub : Icc s r ⊆ Icc a b := Icc_subset_Icc hs.1 hr.2
    have hcont : ContinuousOn (fun w => (u w)⁻¹) (Icc s r) :=
      (hu.mono hsub).inv₀ (fun w hw => (hpositive w hw).ne')
    have hinverse (w : ℝ) (hw : w ∈ interior (Icc s r)) :
        ∃ z : ℝ, HasDerivAt (fun v => (u v)⁻¹) z w ∧ z ≤ A := by
      rw [interior_Icc] at hw
      obtain ⟨z, hz, hbound⟩ := hderiv w
        ⟨hs.1.trans_lt hw.1, hw.2.trans_le hr.2⟩
        (hlevel w ⟨hw.1.le, hw.2⟩)
      refine ⟨-z / u w ^ 2, hz.inv (hpositive w ⟨hw.1.le, hw.2.le⟩).ne', ?_⟩
      apply (div_le_iff₀ (sq_pos_of_pos (hpositive w ⟨hw.1.le, hw.2.le⟩))).2
      exact (neg_le_abs z).trans hbound
    have hcomparison := (convex_Icc s r).image_sub_le_mul_sub_of_deriv_le hcont
      (fun w hw => (hinverse w hw).choose_spec.1.differentiableAt.differentiableWithinAt)
      (fun w hw => by
        obtain ⟨z, hz, hzA⟩ := hinverse w hw
        simpa only [hz.deriv] using hzA)
      s ⟨le_rfl, hr.1.le⟩ r ⟨hr.1.le, le_rfl⟩ hr.1.le
    rw [hvalue] at hcomparison
    have htime : A * (r - s) ≤ A * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith [hs.1, hr.2]) hA
    have hreciprocal : L⁻¹ - (u s)⁻¹ ≤ A * (b - a) := hcomparison.trans htime
    have hmul := mul_le_mul_of_nonneg_left hreciprocal hL.le
    have hLinverse : L * L⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
    have hbudget : 1 - L * (u s)⁻¹ ≤ 1 / 4 := by
      calc
        _ = L * (L⁻¹ - (u s)⁻¹) := by rw [mul_sub, hLinverse]
        _ ≤ L * (A * (b - a)) := hmul
        _ ≤ 1 / 4 := by nlinarith [hshort]
    have hus : 0 < u s := hL.trans hhigh
    have hfinal := mul_le_mul_of_nonneg_right
      (show (3 / 4 : ℝ) ≤ L * (u s)⁻¹ by linarith) hus.le
    have hinv : (L * (u s)⁻¹) * u s = L := by
      rw [mul_assoc, inv_mul_cancel₀ hus.ne', mul_one]
    rw [hinv] at hfinal
    linarith
  · have hlow := le_of_not_gt hhigh
    linarith

end PoincareConjecture.M47
