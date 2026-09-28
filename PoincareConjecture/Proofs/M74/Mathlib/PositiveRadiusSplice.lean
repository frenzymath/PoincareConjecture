import PoincareConjecture.Proofs.M74.Cor15_4.CollarAbsorption
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M74

noncomputable def positiveRadiusSplice (g : ℝ → ℝ) (a0 a b k r : ℝ) : ℝ :=
  if r ≤ a0 then k * r else k * r + collarCutoff a b r * (g r - k * r)

theorem positiveRadiusSplice_linear (g : ℝ → ℝ) {a0 a b k r : ℝ}
    (hab : a < b) (hr : r ≤ a) : positiveRadiusSplice g a0 a b k r = k * r := by
  unfold positiveRadiusSplice
  split_ifs
  · rfl
  · rw [collarCutoff_eq_zero hab hr]
    ring

theorem positiveRadiusSplice_outer (g : ℝ → ℝ) {a0 a b k r : ℝ}
    (ha : a0 < a) (hab : a < b) (hr : b ≤ r) :
    positiveRadiusSplice g a0 a b k r = g r := by
  rw [positiveRadiusSplice, if_neg (by linarith), collarCutoff_eq_one hab hr]
  ring

theorem collarCutoff_deriv_nonneg {a b : ℝ} (hab : a < b) (r : ℝ) :
    0 ≤ deriv (collarCutoff a b) r := by
  have hm : Monotone (collarCutoff a b) := by
    intro x y hxy
    apply Real.smoothTransition.monotone
    exact div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le
  exact hm.deriv_nonneg

theorem positiveRadiusSplice_contDiffAt {g : ℝ → ℝ} {a0 a b k R r : ℝ}
    (ha : a0 < a) (hab : a < b) (hg : ContDiffOn ℝ ∞ g (Ioo a0 R)) (hr : r < R) :
    ContDiffAt ℝ ∞ (positiveRadiusSplice g a0 a b k) r := by
  by_cases hra : r < a
  · have hlin : ContDiffAt ℝ ∞ (fun t : ℝ => k * t) r :=
      contDiffAt_const.mul contDiffAt_id
    apply hlin.congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hra] with t ht
    exact positiveRadiusSplice_linear g hab (le_of_lt ht)
  · have hrg : r ∈ Ioo a0 R := ⟨ha.trans_le (le_of_not_gt hra), hr⟩
    have hsmooth : ContDiffAt ℝ ∞
        (fun t => k * t + collarCutoff a b t * (g t - k * t)) r :=
      (contDiffAt_const.mul contDiffAt_id).add
        ((contDiff_collarCutoff a b).contDiffAt.mul
          ((hg.contDiffAt (isOpen_Ioo.mem_nhds hrg)).sub
            (contDiffAt_const.mul contDiffAt_id)))
    apply hsmooth.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hrg.1] with t ht
    exact if_neg (not_le_of_gt ht)

theorem positiveRadiusSplice_deriv_pos {g : ℝ → ℝ} {a0 a b k R r : ℝ}
    (ha : a0 < a) (hab : a < b) (hk : 0 < k)
    (hg : ContDiffOn ℝ ∞ g (Ioo a0 R))
    (hgd : ∀ x ∈ Ico a R, 0 < deriv g x)
    (hbound : ∀ x ∈ Ico a R, k * x ≤ g x) (hr : r < R) :
    0 < deriv (positiveRadiusSplice g a0 a b k) r := by
  have hlin : HasDerivAt (fun t : ℝ => k * t) k r := by
    simpa using (hasDerivAt_id r).const_mul k
  by_cases hra : r < a
  · have hevent : positiveRadiusSplice g a0 a b k =ᶠ[𝓝 r] (fun t => k * t) := by
      filter_upwards [isOpen_Iio.mem_nhds hra] with t ht
      exact positiveRadiusSplice_linear g hab (le_of_lt ht)
    rw [hevent.deriv_eq, hlin.deriv]
    exact hk
  · have hrg : r ∈ Ioo a0 R := ⟨ha.trans_le (le_of_not_gt hra), hr⟩
    have hrI : r ∈ Ico a R := ⟨le_of_not_gt hra, hr⟩
    have hchi : DifferentiableAt ℝ (collarCutoff a b) r :=
      (contDiff_collarCutoff a b).contDiffAt.differentiableAt (by simp)
    have hgdiff := (hg.contDiffAt (isOpen_Ioo.mem_nhds hrg)).differentiableAt (by simp)
    have hfull := hlin.add (hchi.hasDerivAt.mul (hgdiff.hasDerivAt.sub hlin))
    change HasDerivAt (fun t => k * t + collarCutoff a b t * (g t - k * t))
      (k + (deriv (collarCutoff a b) r * (g r - k * r) +
        collarCutoff a b r * (deriv g r - k))) r at hfull
    have hevent : positiveRadiusSplice g a0 a b k =ᶠ[𝓝 r]
        (fun t => k * t + collarCutoff a b t * (g t - k * t)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hrg.1] with t ht
      exact if_neg (not_le_of_gt ht)
    rw [hevent.deriv_eq, hfull.deriv]
    have hchi0 := (collarCutoff_mem_Icc a b r).1
    have hchi1 := (collarCutoff_mem_Icc a b r).2
    have hmix : 0 < (1 - collarCutoff a b r) * k + collarCutoff a b r * deriv g r := by
      by_cases h1 : collarCutoff a b r = 1
      · simpa only [h1, sub_self, zero_mul, one_mul, zero_add] using hgd r hrI
      · have hlt : collarCutoff a b r < 1 := lt_of_le_of_ne hchi1 h1
        exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hk)
          (mul_nonneg hchi0 (hgd r hrI).le)
    have hcorr := mul_nonneg (collarCutoff_deriv_nonneg hab r) (sub_nonneg.mpr (hbound r hrI))
    nlinarith

theorem positiveRadiusSplice_strictMonoOn {g : ℝ → ℝ} {a0 a b k R : ℝ}
    (ha : a0 < a) (hab : a < b) (hk : 0 < k)
    (hg : ContDiffOn ℝ ∞ g (Ioo a0 R))
    (hgd : ∀ x ∈ Ico a R, 0 < deriv g x)
    (hbound : ∀ x ∈ Ico a R, k * x ≤ g x) :
    StrictMonoOn (positiveRadiusSplice g a0 a b k) (Iio R) := by
  apply strictMonoOn_of_deriv_pos (convex_Iio R)
  · intro r hr
    exact (positiveRadiusSplice_contDiffAt ha hab hg hr).continuousAt.continuousWithinAt
  · intro r hr
    have hrR : r ∈ Iio R := interior_subset hr
    exact positiveRadiusSplice_deriv_pos ha hab hk hg hgd hbound hrR

end PoincareConjecture.M74
