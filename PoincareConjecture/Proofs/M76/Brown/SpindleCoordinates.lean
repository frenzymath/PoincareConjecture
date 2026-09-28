import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set

namespace BrownCollar

noncomputable def collapseHeight (a t : ℝ) : ℝ := max 0 (min t (2 * t - a))

noncomputable def liftHeight (a t : ℝ) : ℝ := max t ((t + a) / 2)

theorem collapseHeight_nonneg (a t : ℝ) : 0 ≤ collapseHeight a t := le_max_left _ _

theorem collapseHeight_le {a t : ℝ} (ht : 0 ≤ t) : collapseHeight a t ≤ t :=
  max_le ht (min_le_left _ _)

theorem liftHeight_nonneg {a t : ℝ} (ht : 0 ≤ t) : 0 ≤ liftHeight a t :=
  ht.trans (le_max_left _ _)

theorem half_le_liftHeight {a t : ℝ} (ht : 0 ≤ t) : a / 2 ≤ liftHeight a t := by
  exact (by linarith : a / 2 ≤ (t + a) / 2).trans (le_max_right _ _)

theorem liftHeight_lt_one {a t : ℝ} (ha : a ≤ 1) (ht : t < 1) :
    liftHeight a t < 1 := max_lt ht (by linarith)

theorem collapseHeight_of_le {a t : ℝ} (ht : 0 ≤ t) (hat : a ≤ t) :
    collapseHeight a t = t := by
  rw [collapseHeight, min_eq_left (by linarith), max_eq_right ht]

theorem liftHeight_of_le {a t : ℝ} (hat : a ≤ t) : liftHeight a t = t := by
  rw [liftHeight, max_eq_left (by linarith)]

theorem collapseHeight_liftHeight {a t : ℝ} (ht : 0 ≤ t) :
    collapseHeight a (liftHeight a t) = t := by
  by_cases hat : a ≤ t
  · rw [liftHeight_of_le hat, collapseHeight_of_le ht hat]
  · have hta : t ≤ a := le_of_not_ge hat
    rw [liftHeight, max_eq_right (by linarith), collapseHeight,
      min_eq_right (by linarith), max_eq_right (by linarith)]
    ring

theorem liftHeight_collapseHeight {a t : ℝ} (ht : 0 ≤ t) (hat : a / 2 ≤ t) :
    liftHeight a (collapseHeight a t) = t := by
  by_cases hat' : a ≤ t
  · rw [collapseHeight_of_le ht hat', liftHeight_of_le hat']
  · have hta : t ≤ a := le_of_not_ge hat'
    rw [collapseHeight, min_eq_right (by linarith), max_eq_right (by linarith),
      liftHeight, max_eq_right (by linarith)]
    ring

theorem collapseHeight_half {a : ℝ} (ha : 0 ≤ a) : collapseHeight a (a / 2) = 0 := by
  simp only [collapseHeight, show 2 * (a / 2) - a = 0 by ring,
    min_eq_right (by linarith : (0 : ℝ) ≤ a / 2), max_self]

theorem liftHeight_zero {a : ℝ} (ha : 0 ≤ a) : liftHeight a 0 = a / 2 := by
  rw [liftHeight, zero_add, max_eq_right (by linarith)]

variable {B : Type*} [TopologicalSpace B]

def spindleUpper (height : B → ℝ) : Set (B × Ico (0 : ℝ) 1) :=
  {z | height z.1 / 2 ≤ (z.2 : ℝ)}

private theorem continuous_collapseHeight (height : B → ℝ) (hc : Continuous height) :
    Continuous (fun z : B × Ico (0 : ℝ) 1 => collapseHeight (height z.1) z.2) := by
  have ht : Continuous (fun z : B × Ico (0 : ℝ) 1 => (z.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact continuous_const.max (ht.min ((continuous_const.mul ht).sub
    (hc.comp continuous_fst)))

private theorem continuous_liftHeight (height : B → ℝ) (hc : Continuous height) :
    Continuous (fun z : B × Ico (0 : ℝ) 1 => liftHeight (height z.1) z.2) := by
  have ht : Continuous (fun z : B × Ico (0 : ℝ) 1 => (z.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact ht.max ((ht.add (hc.comp continuous_fst)).div_const 2)

noncomputable def spindleUpperHomeomorph (height : B → ℝ) (hc : Continuous height)
    (hbounds : ∀ b, height b ∈ Icc (0 : ℝ) 1) :
    spindleUpper height ≃ₜ B × Ico (0 : ℝ) 1 where
  toFun z := (z.val.1, ⟨collapseHeight (height z.val.1) z.val.2,
    collapseHeight_nonneg _ _, (collapseHeight_le z.val.2.property.1).trans_lt
      z.val.2.property.2⟩)
  invFun z := ⟨(z.1, ⟨liftHeight (height z.1) z.2, liftHeight_nonneg z.2.property.1,
    liftHeight_lt_one (hbounds z.1).2 z.2.property.2⟩),
    half_le_liftHeight z.2.property.1⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Subtype.ext (liftHeight_collapseHeight z.val.2.property.1 z.property)
  right_inv z := by
    apply Prod.ext
    · rfl
    · exact Subtype.ext (collapseHeight_liftHeight z.2.property.1)
  continuous_toFun := by
    apply Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
    apply Continuous.subtype_mk
    exact (continuous_collapseHeight height hc).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_fst
    apply Continuous.subtype_mk
    exact continuous_liftHeight height hc

theorem spindleUpperHomeomorph_apply_above (height : B → ℝ) (hc : Continuous height)
    (hbounds : ∀ b, height b ∈ Icc (0 : ℝ) 1)
    (z : spindleUpper height) (hz : height z.val.1 ≤ (z.val.2 : ℝ)) :
    spindleUpperHomeomorph height hc hbounds z = z.val := by
  apply Prod.ext
  · rfl
  · exact Subtype.ext (collapseHeight_of_le z.val.2.property.1 hz)

theorem spindleUpperHomeomorph_symm_apply_above (height : B → ℝ) (hc : Continuous height)
    (hbounds : ∀ b, height b ∈ Icc (0 : ℝ) 1)
    (z : B × Ico (0 : ℝ) 1) (hz : height z.1 ≤ (z.2 : ℝ)) :
    ((spindleUpperHomeomorph height hc hbounds).symm z).val = z := by
  apply Prod.ext
  · rfl
  · exact Subtype.ext (liftHeight_of_le hz)

end BrownCollar
