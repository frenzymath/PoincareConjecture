import PoincareConjecture.Proofs.M76.Brown.SpindleHeight
import Mathlib.Topology.Order.OrderClosed









set_option autoImplicit false

open Set

namespace BrownCollar

variable {B : Type*} [TopologicalSpace B]

def bicollarBase (b : B) : B × Ioo (-1 : ℝ) 1 :=
  (b, ⟨0, by constructor <;> norm_num⟩)

noncomputable def positiveClamp (z : B × Ioo (-1 : ℝ) 1) : B × Ico (0 : ℝ) 1 :=
  (z.1, ⟨max 0 (z.2 : ℝ), le_max_left _ _,
    max_lt (by norm_num) z.2.property.2⟩)

noncomputable def negativeClamp (z : B × Ioo (-1 : ℝ) 1) : B × Ico (0 : ℝ) 1 :=
  (z.1, ⟨max 0 (-(z.2 : ℝ)), le_max_left _ _,
    max_lt (by norm_num) (by linarith [z.2.property.1])⟩)

def positiveHalfInclusion (z : B × Ico (0 : ℝ) 1) : B × Ioo (-1 : ℝ) 1 :=
  (z.1, ⟨(z.2 : ℝ), by linarith [z.2.property.1], z.2.property.2⟩)

noncomputable def negativeHalfInclusion (z : B × Ico (0 : ℝ) 1) : B × Ioo (-1 : ℝ) 1 :=
  (z.1, ⟨-(z.2 : ℝ), by linarith [z.2.property.2], by linarith [z.2.property.1]⟩)

theorem continuous_positiveClamp : Continuous (positiveClamp : B × Ioo (-1 : ℝ) 1 → _) :=
  continuous_fst.prodMk ((continuous_const.max
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _)

theorem continuous_negativeClamp : Continuous (negativeClamp : B × Ioo (-1 : ℝ) 1 → _) :=
  continuous_fst.prodMk ((continuous_const.max
    (continuous_subtype_val.comp continuous_snd).neg).subtype_mk _)

theorem continuous_positiveHalfInclusion :
    Continuous (positiveHalfInclusion : B × Ico (0 : ℝ) 1 → _) :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

theorem continuous_negativeHalfInclusion :
    Continuous (negativeHalfInclusion : B × Ico (0 : ℝ) 1 → _) :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).neg.subtype_mk _)

omit [TopologicalSpace B] in
theorem positiveClamp_positiveHalfInclusion (z : B × Ico (0 : ℝ) 1) :
    positiveClamp (positiveHalfInclusion z) = z := by
  exact Prod.ext rfl (Subtype.ext (max_eq_right z.2.property.1))

omit [TopologicalSpace B] in
theorem negativeClamp_negativeHalfInclusion (z : B × Ico (0 : ℝ) 1) :
    negativeClamp (negativeHalfInclusion z) = z := by
  have hs : (negativeClamp (negativeHalfInclusion z)).2 = z.2 := by
    apply Subtype.ext
    change max 0 (- -(z.2 : ℝ)) = (z.2 : ℝ)
    rw [neg_neg, max_eq_right z.2.property.1]
  exact Prod.ext rfl hs

omit [TopologicalSpace B] in
theorem positiveHalfInclusion_positiveClamp (z : B × Ioo (-1 : ℝ) 1)
    (hz : 0 ≤ (z.2 : ℝ)) : positiveHalfInclusion (positiveClamp z) = z := by
  exact Prod.ext rfl (Subtype.ext (max_eq_right hz))

omit [TopologicalSpace B] in
theorem negativeHalfInclusion_negativeClamp (z : B × Ioo (-1 : ℝ) 1)
    (hz : (z.2 : ℝ) ≤ 0) : negativeHalfInclusion (negativeClamp z) = z := by
  have hs : (negativeHalfInclusion (negativeClamp z)).2 = z.2 := by
    apply Subtype.ext
    change -max 0 (-(z.2 : ℝ)) = (z.2 : ℝ)
    rw [max_eq_right (neg_nonneg.mpr hz), neg_neg]
  exact Prod.ext rfl hs

omit [TopologicalSpace B] in
theorem positiveClamp_of_zero (z : B × Ioo (-1 : ℝ) 1) (hz : (z.2 : ℝ) = 0) :
    positiveClamp z = collarBase z.1 := by
  have hs : (positiveClamp z).2 = (collarBase z.1).2 := by
    apply Subtype.ext
    change max 0 (z.2 : ℝ) = 0
    rw [hz, max_self]
  exact Prod.ext rfl hs

omit [TopologicalSpace B] in
theorem negativeClamp_of_zero (z : B × Ioo (-1 : ℝ) 1) (hz : (z.2 : ℝ) = 0) :
    negativeClamp z = collarBase z.1 := by
  have hs : (negativeClamp z).2 = (collarBase z.1).2 := by
    apply Subtype.ext
    change max 0 (-(z.2 : ℝ)) = 0
    rw [hz, neg_zero, max_self]
  exact Prod.ext rfl hs

omit [TopologicalSpace B] in
theorem positiveHalfInclusion_base (b : B) :
    positiveHalfInclusion (collarBase b) = bicollarBase b := rfl

omit [TopologicalSpace B] in
theorem negativeHalfInclusion_base (b : B) :
    negativeHalfInclusion (collarBase b) = bicollarBase b := by
  exact Prod.ext rfl (Subtype.ext (neg_zero : -(0 : ℝ) = 0))

end BrownCollar
