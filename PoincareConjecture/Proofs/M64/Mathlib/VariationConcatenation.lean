import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Piecewise

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal

namespace PoincareConjecture

theorem m64_exists_join_with_variation
    {X : Type*} [PseudoEMetricSpace X] {f g : ℝ → X}
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hjoin : f 1 = g 0) :
    ∃ q : ℝ → X, ContinuousOn q (Icc 0 1) ∧ q 0 = f 0 ∧ q 1 = g 1 ∧
      (∀ t ∈ Icc 0 1, q t ∈ f '' Icc 0 1 ∪ g '' Icc 0 1) ∧
      eVariationOn q (Icc 0 1) = eVariationOn f (Icc 0 1) + eVariationOn g (Icc 0 1) := by
  let q := fun t : ℝ => if t ≤ 1 / 2 then f (2 * t) else g (2 * t - 1)
  have hl (t : ℝ) (ht : t ∈ Icc 0 (1 / 2)) : 2 * t ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hr (t : ℝ) (ht : t ∈ Icc (1 / 2) 1) : 2 * t - 1 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1, ht.2]
  have hleft : EqOn q (fun t => f (2 * t)) (Icc 0 (1 / 2)) := by
    intro t ht
    exact if_pos ht.2
  have hright : EqOn q (fun t => g (2 * t - 1)) (Icc (1 / 2) 1) := by
    intro t ht
    rcases ht.1.eq_or_lt with heq | hlt
    · subst t
      norm_num only [q, le_refl, if_true, mul_div_cancel₀, OfNat.ofNat_ne_zero,
        sub_self]
      exact hjoin
    · exact if_neg (not_le_of_gt hlt)
  have hqc : ContinuousOn q (Icc 0 1) := by
    apply ContinuousOn.if
    · intro t ht
      have heq : t = 1 / 2 := by
        have hh := ht.2
        change t ∈ frontier (Iic (1 / 2 : ℝ)) at hh
        simpa only [frontier_Iic, mem_singleton_iff] using hh
      subst t
      norm_num only [mul_div_cancel₀, OfNat.ofNat_ne_zero, sub_self]
      exact hjoin
    · apply hf.comp (continuous_const.mul continuous_id).continuousOn
      intro t ht
      have ht' : t ≤ 1 / 2 := by
        simpa only [show {t : ℝ | t ≤ 1 / 2} = Iic (1 / 2) from rfl,
          isClosed_Iic.closure_eq, mem_Iic] using ht.2
      exact hl t ⟨ht.1.1, ht'⟩
    · apply hg.comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
      intro t ht
      have ht' : 1 / 2 ≤ t := by
        have hh := ht.2
        simp only [not_le] at hh
        change t ∈ closure (Ioi (1 / 2 : ℝ)) at hh
        simpa only [closure_Ioi, mem_Ici] using hh
      exact hr t ⟨ht', ht.1.2⟩
  refine ⟨q, hqc, by norm_num [q], by norm_num [q], ?_, ?_⟩
  · intro t ht
    by_cases h : t ≤ 1 / 2
    · exact Or.inl ⟨2 * t, hl t ⟨ht.1, h⟩, (if_pos h).symm⟩
    · exact Or.inr ⟨2 * t - 1, hr t ⟨(le_of_not_ge h), ht.2⟩, (if_neg h).symm⟩
  · have hsplit := eVariationOn.Icc_add_Icc q (s := univ)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (mem_univ _)
    simp only [univ_inter] at hsplit
    rw [← hsplit, eVariationOn.eq_of_eqOn hleft, eVariationOn.eq_of_eqOn hright]
    have himl : (fun t : ℝ => 2 * t) '' Icc 0 (1 / 2) = Icc (0 : ℝ) 1 := by
      norm_num [image_mul_left_Icc' (by norm_num : (0 : ℝ) < 2)]
    have himr : (fun t : ℝ => 2 * t - 1) '' Icc (1 / 2) 1 = Icc (0 : ℝ) 1 := by
      have hcont : Continuous (fun t : ℝ => 2 * t - 1) := by fun_prop
      have hmono : MonotoneOn (fun t : ℝ => 2 * t - 1) (Icc (1 / 2) 1) := by
        intro x _ y _ hxy
        linarith
      convert hcont.continuousOn.image_Icc_of_monotoneOn
        (by norm_num : (1 / 2 : ℝ) ≤ 1) hmono using 1
      norm_num
    change eVariationOn (f ∘ fun t => 2 * t) (Icc 0 (1 / 2)) +
      eVariationOn (g ∘ fun t => 2 * t - 1) (Icc (1 / 2) 1) = _
    rw [eVariationOn.comp_eq_of_monotoneOn f _ (by intro x _ y _ hxy; linarith), himl,
      eVariationOn.comp_eq_of_monotoneOn g _ (by intro x _ y _ hxy; linarith), himr]

end PoincareConjecture
