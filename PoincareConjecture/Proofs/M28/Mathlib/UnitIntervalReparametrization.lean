import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic









noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff

namespace Poincare



def unitIntervalReparam (a s : ℝ) : ℝ :=
  a * s / ((1 - a) * (1 - s) + a * s)

private theorem denominator_pos {a s : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ Ioo (0 : ℝ) 1) : 0 < (1 - a) * (1 - s) + a * s :=
  add_pos (mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hs.2)) (mul_pos ha.1 hs.1)

private theorem reparam_mem {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    MapsTo (unitIntervalReparam a) (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1) := by
  intro s hs
  refine ⟨div_pos (mul_pos ha.1 hs.1) (denominator_pos ha hs), ?_⟩
  apply (div_lt_one (denominator_pos ha hs)).mpr
  linarith [mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hs.2)]




theorem unitIntervalReparam_properties {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ContDiffOn ℝ ∞ (unitIntervalReparam a) (Ioo (0 : ℝ) 1) ∧
      MapsTo (unitIntervalReparam a) (Ioo (0 : ℝ) 1) (Ioo (0 : ℝ) 1) ∧
      LeftInvOn (unitIntervalReparam (1 - a)) (unitIntervalReparam a)
        (Ioo (0 : ℝ) 1) ∧
      unitIntervalReparam a (1 / 2) = a ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, (1 / 2 : ℝ) < unitIntervalReparam (1 - a) s ↔ a < s := by
  have hb : 1 - a ∈ Ioo (0 : ℝ) 1 := ⟨sub_pos.mpr ha.2, by linarith [ha.1]⟩
  refine ⟨?_, reparam_mem ha, ?_, ?_, ?_⟩
  · exact (contDiffOn_const.mul contDiffOn_id).div
      ((contDiffOn_const.mul (contDiffOn_const.sub contDiffOn_id)).add
        (contDiffOn_const.mul contDiffOn_id)) (fun s hs => (denominator_pos ha hs).ne')
  · intro s hs
    have hd := (denominator_pos ha hs).ne'
    have hd' := (denominator_pos hb (reparam_mem ha hs)).ne'
    dsimp only [unitIntervalReparam] at hd' ⊢
    apply (div_eq_iff hd').mpr
    field_simp [hd]
    ring
  · unfold unitIntervalReparam
    have hd : (1 - a) * (1 - 1 / 2) + a * (1 / 2) = (1 / 2 : ℝ) := by ring
    rw [hd]
    ring
  · intro s hs
    unfold unitIntervalReparam
    rw [lt_div_iff₀ (denominator_pos hb hs)]
    constructor <;> intro h <;> nlinarith



theorem unitIntervalReparam_strictMonoOn {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    StrictMonoOn (unitIntervalReparam a) (Ioo (0 : ℝ) 1) := by
  intro s hs t ht hst
  unfold unitIntervalReparam
  rw [div_lt_div_iff₀ (denominator_pos ha hs) (denominator_pos ha ht)]
  have hp := mul_pos (mul_pos ha.1 (sub_pos.mpr ha.2)) (sub_pos.mpr hst)
  nlinarith

end Poincare
