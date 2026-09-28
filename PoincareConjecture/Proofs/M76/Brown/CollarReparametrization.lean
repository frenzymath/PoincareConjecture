import PoincareConjecture.Proofs.M76.Brown.SpindleConjugation
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false

open Set

namespace BrownCollar

variable {B : Type*} [MetricSpace B]

noncomputable def positiveSpindleHomeomorph (height : B → ℝ)
    (hc : Continuous height) (hpos : ∀ b, 0 < height b) (hle : ∀ b, height b ≤ 1) :
    (B × Ico (0 : ℝ) 1) ≃ₜ spindle height where
  toFun z := by
    have hlt : height z.1 * (z.2 : ℝ) < height z.1 := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left z.2.property.2 (hpos z.1)
    exact ⟨(z.1, ⟨height z.1 * z.2, mul_nonneg (hpos z.1).le z.2.property.1,
      hlt.trans_le (hle z.1)⟩), hlt⟩
  invFun z := (z.val.1, ⟨(z.val.2 : ℝ) / height z.val.1,
    div_nonneg z.val.2.property.1 (hpos z.val.1).le,
    (div_lt_one (hpos z.val.1)).mpr z.property⟩)
  left_inv z := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact mul_div_cancel_left₀ (z.2 : ℝ) (ne_of_gt (hpos z.1))
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change height z.val.1 * ((z.val.2 : ℝ) / height z.val.1) = (z.val.2 : ℝ)
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt (hpos z.val.1))]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_fst
    apply Continuous.subtype_mk
    exact (hc.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    apply Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val).div
      ((hc.comp continuous_fst).comp continuous_subtype_val)
      (fun z => ne_of_gt (hpos z.val.1))

theorem positiveSpindleHomeomorph_apply_base (height : B → ℝ)
    (hc : Continuous height) (hpos : ∀ b, 0 < height b) (hle : ∀ b, height b ≤ 1)
    (b : B) :
    (positiveSpindleHomeomorph height hc hpos hle (collarBase b) :
      B × Ico (0 : ℝ) 1) = collarBase b := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact mul_zero (height b)

theorem exists_full_collar_of_open_neighborhood {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) X) (i : B → X)
    (hsource : ∀ b, collarBase b ∈ e.source)
    (hfixed : ∀ b, e (collarBase b) = i b) :
    ∃ U : Set X, IsOpen U ∧ range i ⊆ U ∧
      ∃ c : (B × Ico (0 : ℝ) 1) ≃ₜ U, ∀ b, (c (collarBase b) : X) = i b := by
  obtain ⟨height, hbounds, hpos, hS⟩ := exists_spindleHeight isOpen_univ e.open_source
    (fun b _ => hsource b)
  have hp (b : B) : 0 < height b := (hpos b).mpr (mem_univ b)
  have hle (b : B) : height b ≤ 1 := (hbounds b).2
  have hSS : spindle height ⊆ e.source := subset_closure.trans hS
  let U := e '' spindle height
  let R := positiveSpindleHomeomorph height height.continuous hp hle
  let c : (B × Ico (0 : ℝ) 1) ≃ₜ U :=
    R.trans (e.homeomorphOfImageSubsetSource hSS rfl)
  refine ⟨U, e.isOpen_image_of_subset_source
    (isOpen_spindle height height.continuous) hSS, ?_, c, ?_⟩
  · rintro x ⟨b, rfl⟩
    exact ⟨collarBase b, hp b, hfixed b⟩
  · intro b
    change e (R (collarBase b)) = i b
    rw [positiveSpindleHomeomorph_apply_base height height.continuous hp hle]
    exact hfixed b

end BrownCollar
