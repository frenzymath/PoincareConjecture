import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_WeightedFocusingCover
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set










noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture





theorem m64_exists_shifted_weighted_focusing_cover
    {f g : ℝ → ℝ} (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hg : Continuous g) (hgnonneg : ∀ x, 0 ≤ g x)
    {l u A τ : ℝ} (hlu : l < u) (hA : 0 ≤ A) (hτ : 3 < τ)
    (T : Set (ℝ × ℝ))
    (hT : ∀ p ∈ T, l ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ u)
    (hfocus : ∀ p ∈ T,
      (∫ x in p.1..p.2, f x) ≤ A * ∫ x in p.1..p.2, g x) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc l u ∧
      (∀ p ∈ T, Icc p.1 p.2 ⊆ E) ∧
      (∫ x in E, f x) ≤ (τ * A) * ∫ x in l..u, g x := by
  let Q := (fun p : ℝ × ℝ => (p.1 - l, p.2 - l)) '' T
  have hQ (q : ℝ × ℝ) (hq : q ∈ Q) :
      0 ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ u - l := by
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨ha, hab, hb⟩ := hT p hp
    exact ⟨sub_nonneg.mpr ha, sub_lt_sub_right hab l, sub_le_sub_right hb l⟩
  have hQfocus (q : ℝ × ℝ) (hq : q ∈ Q) :
      (∫ x in q.1..q.2, f (x + l)) ≤ A * ∫ x in q.1..q.2, g (x + l) := by
    obtain ⟨p, hp, rfl⟩ := hq
    simpa only [intervalIntegral.integral_comp_add_right, sub_add_cancel] using hfocus p hp
  obtain ⟨B, hB, hBsub, hcover, hbound⟩ :=
    m64Intrinsic_exists_weighted_focusing_cover
      (hf.comp (continuous_id.add continuous_const)) (fun x => hfpos (x + l))
      (hg.comp (continuous_id.add continuous_const)) (fun x => hgnonneg (x + l))
      (sub_pos.mpr hlu) hA hτ Q hQ hQfocus
  let E := (fun x : ℝ => x + l) '' B
  have hE : MeasurableSet E :=
    (MeasurableEquiv.addRight l).measurableEmbedding.measurableSet_image' hB
  have hEsub : E ⊆ Icc l u := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hBsub hx
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmass : (∫ x in E, f x) = ∫ x in B, f (x + l) :=
    (measurePreserving_add_right (volume : Measure ℝ) l).setIntegral_image_emb
      (MeasurableEquiv.addRight l).measurableEmbedding f B
  refine ⟨E, hE, hEsub, ?_, ?_⟩
  · intro p hp x hx
    refine ⟨x - l, hcover (p.1 - l, p.2 - l) ⟨p, hp, rfl⟩ ?_, sub_add_cancel x l⟩
    exact ⟨sub_le_sub_right hx.1 l, sub_le_sub_right hx.2 l⟩
  · rw [hmass]
    change (∫ x in B, f (x + l)) ≤ (τ * A) * ∫ x in (0 : ℝ)..u - l, g (x + l) at hbound
    simpa only [intervalIntegral.integral_comp_add_right, zero_add, sub_add_cancel] using hbound

end PoincareConjecture
