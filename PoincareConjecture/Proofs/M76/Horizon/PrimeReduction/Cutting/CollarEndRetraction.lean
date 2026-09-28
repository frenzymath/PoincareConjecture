import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedCollarOpenCoordinates
import Mathlib.Topology.Piecewise

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

def CollarEnds := {t : unitInterval | (t : ℝ) < 1 / 4 ∨ (3 / 4 : ℝ) < t}

noncomputable def collarEnd (t : CollarEnds) : unitInterval :=
  if (t.val : ℝ) < 1 / 2 then 0 else 1

theorem continuous_collarEnd : Continuous collarEnd := by
  have hc : Continuous (fun t : CollarEnds => (t.val : ℝ)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hne (t : CollarEnds) : (t.val : ℝ) ≠ 1 / 2 := by
    rcases t.property with h | h <;> linarith
  have he : {t : CollarEnds | (t.val : ℝ) < 1 / 2}ᶜ =
      {t | (1 / 2 : ℝ) < t.val} := by
    ext t
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt]
    exact le_iff_lt_or_eq.trans (or_iff_left (Ne.symm (hne t)))
  have hcl : IsClopen {t : CollarEnds | (t.val : ℝ) < 1 / 2} :=
    ⟨isOpen_compl_iff.mp (he ▸ isOpen_lt continuous_const hc),
      isOpen_lt hc continuous_const⟩
  apply Continuous.if _ continuous_const continuous_const
  intro t ht
  rw [hcl.frontier_eq] at ht
  exact False.elim ht

noncomputable def collarEndSlide (s : unitInterval) (t : CollarEnds) : unitInterval :=
  ⟨(1 - (s : ℝ)) * t.val + (s : ℝ) * collarEnd t, by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) t.val.property.1)
        (mul_nonneg s.property.1 (collarEnd t).property.1)
    · have h0 := t.val.property.2
      have h1 := (collarEnd t).property.2
      nlinarith [s.property.1, s.property.2]⟩

theorem continuous_collarEndSlide :
    Continuous (fun z : unitInterval × CollarEnds => collarEndSlide z.1 z.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_collarEnd.comp continuous_snd)))

theorem collarEndSlide_mem (s : unitInterval) (t : CollarEnds) :
    (collarEndSlide s t : ℝ) < 1 / 4 ∨ (3 / 4 : ℝ) < collarEndSlide s t := by
  rcases t.property with ht | ht
  · left
    have he : collarEnd t = 0 := if_pos (by linarith)
    change (1 - (s : ℝ)) * t.val + (s : ℝ) * collarEnd t < 1 / 4
    rw [he]
    change (1 - (s : ℝ)) * t.val + (s : ℝ) * 0 < 1 / 4
    nlinarith [s.property.1, t.val.property.1]
  · right
    have he : collarEnd t = 1 := if_neg (by linarith)
    change (3 / 4 : ℝ) < (1 - (s : ℝ)) * t.val + (s : ℝ) * collarEnd t
    rw [he]
    change (3 / 4 : ℝ) < (1 - (s : ℝ)) * t.val + (s : ℝ) * 1
    nlinarith [s.property.1, t.val.property.2]

@[simp] theorem collarEndSlide_zero (t : CollarEnds) : collarEndSlide 0 t = t.val := by
  apply Subtype.ext
  simp [collarEndSlide]

@[simp] theorem collarEndSlide_one (t : CollarEnds) : collarEndSlide 1 t = collarEnd t := by
  apply Subtype.ext
  simp [collarEndSlide]

theorem collarEndSlide_fixed (s : unitInterval) (t : CollarEnds)
    (ht : t.val = 0 ∨ t.val = 1) : collarEndSlide s t = t.val := by
  rcases ht with ht | ht
  · have he : collarEnd t = 0 := by simp [collarEnd, ht]
    apply Subtype.ext
    simp [collarEndSlide, ht, he]
  · have he : collarEnd t = 1 := by norm_num [collarEnd, ht]
    apply Subtype.ext
    simp [collarEndSlide, ht, he]

end PoincareConjecture.M76
