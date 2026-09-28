import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false

open Set

namespace PoincareConjecture.AncientCylinderPeriod

variable {C M : Type*}

private theorem snd_zpow_of_translation (d : Equiv.Perm (C × ℝ)) (l : ℝ)
    (hd : ∀ z, (d z).2 = z.2 + l) (k : ℤ) (z : C × ℝ) :
    ((d ^ k) z).2 = z.2 + k * l := by
  have hi (z : C × ℝ) : (d⁻¹ z).2 = z.2 - l := by
    have h := hd (d⁻¹ z)
    simpa using (eq_sub_iff_add_eq.mpr h.symm)
  induction k using Int.induction_on generalizing z with
  | zero => simp
  | succ n hn =>
      rw [zpow_add, zpow_one, Equiv.Perm.mul_apply, hn, hd]
      push_cast
      ring
  | pred n hn =>
      rw [zpow_sub, zpow_one, Equiv.Perm.mul_apply, hn, hi]
      push_cast
      ring

private theorem invariant_zpow (d : Equiv.Perm (C × ℝ)) (p : C × ℝ → M)
    (hp : ∀ z, p (d z) = p z) (k : ℤ) (z : C × ℝ) :
    p ((d ^ k) z) = p z := by
  have hi (z : C × ℝ) : p (d⁻¹ z) = p z := by
    simpa using (hp (d⁻¹ z)).symm
  induction k using Int.induction_on generalizing z with
  | zero => simp
  | succ n hn => rw [zpow_add, zpow_one, Equiv.Perm.mul_apply, hn, hp]
  | pred n hn => rw [zpow_sub, zpow_one, Equiv.Perm.mul_apply, hn, hi]

theorem image_slab_eq_univ_of_translation
    (p : C × ℝ → M) (hsurj : Function.Surjective p)
    (d : Equiv.Perm (C × ℝ)) (l : ℝ) (hl : 0 < l)
    (hd : ∀ z, (d z).2 = z.2 + l) (hp : ∀ z, p (d z) = p z) :
    p '' (univ ×ˢ Icc 0 l) = univ := by
  apply eq_univ_of_forall
  intro y
  obtain ⟨z, rfl⟩ := hsurj y
  let k : ℤ := -⌊z.2 / l⌋
  refine ⟨(d ^ k) z, ⟨mem_univ _, ?_⟩, invariant_zpow d p hp k z⟩
  rw [snd_zpow_of_translation d l hd k z]
  have hfloor := Int.floor_le (z.2 / l)
  have hceil := Int.lt_floor_add_one (z.2 / l)
  have h1 := (le_div_iff₀ hl).mp hfloor
  have h2 := (div_lt_iff₀ hl).mp hceil
  dsimp only [k]
  push_cast
  constructor <;> nlinarith

theorem image_slab_eq_univ_of_nonzero_translation
    (p : C × ℝ → M) (hsurj : Function.Surjective p)
    (d : Equiv.Perm (C × ℝ)) (l : ℝ) (hl : l ≠ 0)
    (hd : ∀ z, (d z).2 = z.2 + l) (hp : ∀ z, p (d z) = p z) :
    p '' (univ ×ˢ Icc 0 |l|) = univ := by
  rcases lt_or_gt_of_ne hl with hneg | hpos
  · rw [abs_of_neg hneg]
    apply image_slab_eq_univ_of_translation p hsurj d⁻¹ (-l) (neg_pos.mpr hneg)
    · intro z
      have h := hd (d⁻¹ z)
      simpa using (eq_add_neg_iff_add_eq.mpr h.symm)
    · intro z
      simpa using (hp (d⁻¹ z)).symm
  · rw [abs_of_pos hpos]
    exact image_slab_eq_univ_of_translation p hsurj d l hpos hd hp

theorem compactSpace_of_nonzero_translation
    [TopologicalSpace C] [CompactSpace C] [TopologicalSpace M]
    (p : C × ℝ → M) (hpcont : Continuous p) (hsurj : Function.Surjective p)
    (d : Equiv.Perm (C × ℝ)) (l : ℝ) (hl : l ≠ 0)
    (hd : ∀ z, (d z).2 = z.2 + l) (hp : ∀ z, p (d z) = p z) :
    CompactSpace M := by
  apply isCompact_univ_iff.mp
  rw [← image_slab_eq_univ_of_nonzero_translation p hsurj d l hl hd hp]
  exact (isCompact_univ.prod isCompact_Icc).image hpcont

end PoincareConjecture.AncientCylinderPeriod
