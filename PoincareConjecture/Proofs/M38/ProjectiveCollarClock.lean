import PoincareConjecture.Proofs.M38.LowerEndReparametrization
import PoincareConjecture.Proofs.M38.CylinderEndReparametrization

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

theorem exists_projective_collar_clock :
    ∃ f : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      StrictMono f ∧ (∀ t, f (-t) = -f t) ∧ f 1 = 1 ∧
      ∀ s : ℝ, |s| ≤ 1 / 16 → f (1 - s / 2) = (1 + s)⁻¹ := by
  let l := lowerEndOrderIso (1 / 2) (by norm_num) (by norm_num)
  let u : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
    toFun t := 1 - l.symm (1 - t)
    invFun t := 1 - l (1 - t)
    left_inv t := by simp
    right_inv t := by simp
    contMDiff_toFun := (contDiff_const.sub
      ((lowerEndOrderIso_symm_smooth (by norm_num : 0 < (1 : ℝ) / 2)
        (by norm_num)).comp (contDiff_const.sub contDiff_id))).contMDiff
    contMDiff_invFun := (contDiff_const.sub
      ((lowerEndProfile_smooth (1 / 2)).comp (contDiff_const.sub contDiff_id))).contMDiff }
  have hu (t : ℝ) : u t = 1 - l.symm (1 - t) := rfl
  have humono : StrictMono u := by
    intro x y hxy
    exact sub_lt_sub_left (l.symm.strictMono (sub_lt_sub_left hxy 1)) 1
  have hufix (t : ℝ) (ht : t ≤ 3 / 4) : u t = t := by
    have hl : l (1 - t) = 1 - t := lowerEndProfile_outer (1 / 2) (by
      rw [abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
      linarith)
    rw [hu, ← hl, l.symm_apply_apply]
    ring
  have hu0 : u 0 = 0 := hufix 0 (by norm_num)
  have hu1 : u 1 = 1 := by
    rw [hu, sub_self]
    have hl0 : l 0 = 0 := lowerEndOrderIso_zero _ _ _
    rw [← hl0, l.symm_apply_apply]
    ring
  let v : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
    toFun t := -u (-t)
    invFun t := -u.symm (-t)
    left_inv t := by simp
    right_inv t := by simp
    contMDiff_toFun := (u.contMDiff.comp (contMDiff_neg 𝓘(ℝ, ℝ) ∞)).neg
    contMDiff_invFun := (u.symm.contMDiff.comp (contMDiff_neg 𝓘(ℝ, ℝ) ∞)).neg }
  have hvmono : StrictMono v := by
    intro x y hxy
    exact neg_lt_neg (humono (neg_lt_neg hxy))
  let f := v.trans u
  have hfplus (t : ℝ) (ht : 0 ≤ t) : f t = u t := by
    change u (-u (-t)) = u t
    rw [hufix (-t) (by linarith), neg_neg]
  have hfminus (t : ℝ) (ht : t ≤ 0) : f t = -u (-t) := by
    change u (-u (-t)) = -u (-t)
    apply hufix
    have hnonneg : 0 ≤ u (-t) := by
      rw [← hu0]
      exact humono.monotone (by linarith)
    linarith
  refine ⟨f, humono.comp hvmono, ?_, (hfplus 1 (by norm_num)).trans hu1, ?_⟩
  · intro t
    rcases le_total 0 t with ht | ht
    · rw [hfminus (-t) (by linarith), neg_neg, hfplus t ht]
    · rw [hfplus (-t) (by linarith), hfminus t ht, neg_neg]
  · intro s hs
    have hs' := abs_le.mp hs
    have hpos : 0 < 1 + s := by linarith
    have hb : |s / (1 + s)| ≤ 1 / 8 := by
      rw [abs_le]
      constructor
      · apply (le_div_iff₀ hpos).mpr
        linarith
      · apply (div_le_iff₀ hpos).mpr
        linarith
    have he : l (s / (1 + s)) = s / 2 := by
      rw [lowerEndOrderIso_apply, lowerEndProfile_inner (1 / 2) hb]
      field_simp
      ring
    rw [hfplus _ (by linarith), hu]
    have hsub : 1 - (1 - s / 2) = s / 2 := by ring
    rw [hsub, ← he, l.symm_apply_apply]
    field_simp
    ring

end PoincareConjecture.M38
