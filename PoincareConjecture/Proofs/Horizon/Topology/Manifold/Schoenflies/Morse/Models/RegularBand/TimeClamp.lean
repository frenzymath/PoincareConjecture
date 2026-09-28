import Mathlib.Analysis.SpecialFunctions.SmoothTransition



noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff

namespace Poincare.Manifold.Schoenflies



theorem exists_smooth_band_endpoint_clamp
    {a b w : Real} (hw : 0 < w) (hsep : a + w < b - w) :
    ∃ θ : Real → Real, ContDiff Real ∞ θ ∧
      (∀ t, θ t ∈ Icc a b) ∧
      (∀ t, t ≤ a + w / 4 → θ t = a) ∧
      (∀ t, b - w / 4 ≤ t → θ t = b) ∧
      ∀ t ∈ Icc a b,
        (t ∈ Icc a (a + w) ∧ θ t ∈ Icc a (a + w)) ∨
        (t ∈ Icc (b - w) b ∧ θ t ∈ Icc (b - w) b) ∨ θ t = t := by
  let L : Real → Real := fun t =>
    Real.smoothTransition ((t - (a + w / 4)) / (w / 4))
  let U : Real → Real := fun t =>
    Real.smoothTransition (((b - w / 4) - t) / (w / 4))
  let θ : Real → Real := fun t => b + U t * (a + L t * (t - a) - b)
  have hw4 : 0 < w / 4 := by positivity
  have hL : ContDiff Real ∞ L := Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _)
  have hU : ContDiff Real ∞ U := Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_id).div_const _)
  have hθ : ContDiff Real ∞ θ := contDiff_const.add
    (hU.mul ((contDiff_const.add (hL.mul (contDiff_id.sub contDiff_const))).sub contDiff_const))
  have hL0 (t : Real) (ht : t ≤ a + w / 4) : L t = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hw4.le)
  have hL1 (t : Real) (ht : a + w / 2 ≤ t) : L t = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hw4).mpr (by linarith))
  have hU0 (t : Real) (ht : b - w / 4 ≤ t) : U t = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hw4.le)
  have hU1 (t : Real) (ht : t ≤ b - w / 2) : U t = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hw4).mpr (by linarith))
  have hleft (t : Real) (ht : t ≤ a + w / 4) : θ t = a := by
    simp only [θ, hL0 t ht, hU1 t (by linarith), zero_mul, add_zero, one_mul]
    ring
  have hright (t : Real) (ht : b - w / 4 ≤ t) : θ t = b := by
    simp only [θ, hU0 t ht, zero_mul, add_zero]
  have hlower (t : Real) (ht0 : a ≤ t) (ht1 : t ≤ a + w / 2) :
      θ t ∈ Icc a (a + w) := by
    have hLnon : 0 ≤ L t := Real.smoothTransition.nonneg _
    have hLle : L t ≤ 1 := Real.smoothTransition.le_one _
    dsimp only [θ]
    rw [hU1 t (by linarith), one_mul]
    constructor <;> nlinarith [mul_nonneg hLnon (sub_nonneg.mpr ht0),
      mul_le_mul_of_nonneg_right hLle (sub_nonneg.mpr ht0)]
  have hupper (t : Real) (ht0 : b - w / 2 ≤ t) (ht1 : t ≤ b) :
      θ t ∈ Icc (b - w) b := by
    have hUnon : 0 ≤ U t := Real.smoothTransition.nonneg _
    have hUle : U t ≤ 1 := Real.smoothTransition.le_one _
    dsimp only [θ]
    rw [hL1 t (by linarith), one_mul]
    constructor <;> nlinarith [mul_nonneg hUnon (sub_nonneg.mpr ht1),
      mul_le_mul_of_nonneg_right hUle (sub_nonneg.mpr ht1)]
  have hmiddle (t : Real) (ht0 : a + w / 2 ≤ t) (ht1 : t ≤ b - w / 2) : θ t = t := by
    simp only [θ, hL1 t ht0, hU1 t ht1, one_mul]
    ring
  have hpieces (t : Real) (ht : t ∈ Icc a b) :
      (t ∈ Icc a (a + w) ∧ θ t ∈ Icc a (a + w)) ∨
      (t ∈ Icc (b - w) b ∧ θ t ∈ Icc (b - w) b) ∨ θ t = t := by
    by_cases hl : t ≤ a + w / 2
    · exact Or.inl ⟨⟨ht.1, by linarith⟩, hlower t ht.1 hl⟩
    by_cases hu : b - w / 2 ≤ t
    · exact Or.inr (Or.inl ⟨⟨by linarith, ht.2⟩, hupper t hu ht.2⟩)
    exact Or.inr (Or.inr (hmiddle t (by linarith) (by linarith)))
  refine ⟨θ, hθ, ?_, hleft, hright, hpieces⟩
  intro t
  by_cases hl : t ≤ a
  · rw [hleft t (by linarith)]
    exact ⟨le_rfl, by linarith⟩
  by_cases hu : b ≤ t
  · rw [hright t (by linarith)]
    exact ⟨by linarith, le_rfl⟩
  have ht : t ∈ Icc a b := ⟨by linarith, by linarith⟩
  rcases hpieces t ht with ⟨_, hθt⟩ | ⟨_, hθt⟩ | hθt
  · exact ⟨hθt.1, by linarith [hθt.2]⟩
  · exact ⟨by linarith [hθt.1], hθt.2⟩
  · rwa [hθt]

end Poincare.Manifold.Schoenflies
