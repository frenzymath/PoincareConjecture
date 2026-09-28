import PoincareConjecture.Proofs.M63.Mathlib.PeriodicMaximumPrinciple

set_option autoImplicit false

open Set Filter

namespace Poincare.Parabolic

theorem periodic_le_quadratic_barrier
    {U V : ℝ → ℝ → ℝ} {p a b D R : ℝ} (hp : 0 < p) (hab : a < b)
    (hD : 0 ≤ D) (hR : 0 < R) (hshort : D * R * (b - a) ≤ 1 / 2)
    (hU : ContinuousOn (Function.uncurry U) (univ ×ˢ Icc a b))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => U x t) p)
    (hderiv : ∀ x t, t ∈ Ioo a b → HasDerivAt (U x) (V x t) t)
    (hmax : ∀ x t, t ∈ Ioo a b → IsLocalMax (fun y => U y t) x →
      V x t ≤ D * U x t ^ 2)
    (hinit : ∀ x, U x a ≤ R) :
    ∀ x t, t ∈ Icc a b →
      U x t ≤ R / (1 - D * R * (t - a)) ∧ R / (1 - D * R * (t - a)) ≤ 2 * R := by
  let H := fun t => R / (1 - D * R * (t - a))
  have hden {t : ℝ} (ht : t ∈ Icc a b) : (1 / 2 : ℝ) ≤ 1 - D * R * (t - a) := by
    have h := (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a)
      (mul_nonneg hD hR.le)).trans hshort
    linarith
  have hdenpos {t : ℝ} (ht : t ∈ Icc a b) : 0 < 1 - D * R * (t - a) := by
    linarith [hden ht]
  have hHbound {t : ℝ} (ht : t ∈ Icc a b) : H t ≤ 2 * R := by
    apply (div_le_iff₀ (hdenpos ht)).mpr
    nlinarith [mul_le_mul_of_nonneg_left (hden ht) hR.le]
  have hH : ContinuousOn H (Icc a b) :=
    continuousOn_const.div (by fun_prop) (fun _ ht => (hdenpos ht).ne')
  have hHd {t : ℝ} (ht : t ∈ Ioo a b) : HasDerivAt H (D * H t ^ 2) t := by
    have hd : HasDerivAt (fun s => 1 - D * R * (s - a)) (-(D * R)) t := by
      simpa only [id_eq, mul_one] using
        ((((hasDerivAt_id t).sub_const a).const_mul (D * R)).const_sub 1)
    convert! (hasDerivAt_const t R).div hd (hdenpos (Ioo_subset_Icc_self ht)).ne' using 1
    dsimp only [H]
    field_simp [(hdenpos (Ioo_subset_Icc_self ht)).ne']
    ring
  obtain ⟨Q, hQ⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (hU.mono (Set.prod_mono (show Icc (0 : ℝ) p ⊆ univ from subset_univ _) Subset.rfl))
  have hUbound (x t : ℝ) (ht : t ∈ Icc a b) : U x t ≤ Q := by
    obtain ⟨y, hy, hxy⟩ := (hper t ht).exists_mem_Ico₀ hp x
    rw [hxy]
    exact hQ ⟨(y, t), ⟨Ico_subset_Icc_self hy, ht⟩, rfl⟩
  have hW := periodic_nonpos_of_deriv_le_mul_at_localMax
    (F := fun x t => U x t - H t) (V := fun x t => V x t - D * H t ^ 2)
    (K := D * (max Q 0 + 2 * R)) hp hab
    (hU.sub (hH.comp continuous_snd.continuousOn (fun _ hz => hz.2)))
    (fun t ht x => by simp only [(hper t ht) x])
    (fun x t ht => (hderiv x t ht).sub (hHd ht))
    (fun x t ht hpos hlocal => by
      have hlocalU : IsLocalMax (fun y => U y t) x := by
        filter_upwards [hlocal] with y hy
        change U y t - H t ≤ U x t - H t at hy
        change U y t ≤ U x t
        linarith
      have hsum : U x t + H t ≤ max Q 0 + 2 * R :=
        add_le_add ((hUbound x t (Ioo_subset_Icc_self ht)).trans (le_max_left _ _))
          (hHbound (Ioo_subset_Icc_self ht))
      have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hD) hpos.le
      nlinarith only [hmax x t ht hlocalU, hmul])
    (fun x => by simpa only [H, sub_self, mul_zero, sub_zero, div_one, sub_nonpos] using hinit x)
  intro x t ht
  exact ⟨sub_nonpos.mp (hW x t ht), hHbound ht⟩

end Poincare.Parabolic
