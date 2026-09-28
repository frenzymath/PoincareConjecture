import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith








set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

noncomputable def commonCollarAttachment
    {E X Z : Type*} (c : E × ℝ → X) (rim : Bool → Z → E)
    (G : X → X) (f : ℝ × Z → X) (a : ℝ) (z : ℝ × Z) : X :=
  if z.1 ≤ -1 then c (rim false z.2, a * (z.1 + 2))
  else if 1 ≤ z.1 then c (rim true z.2, a * (2 - z.1))
  else G (f z)

theorem commonCollarAttachment_injOn
    {E X Z : Type*} (c : E × ℝ → X) (rim : Bool → Z → E)
    {K : Set E} {A : Set Z} {a : ℝ} (ha : 0 < a)
    (hc : InjOn c (K ×ˢ Icc (0 : ℝ) a))
    (hrim : ∀ b, MapsTo (rim b) A K)
    (G : X → X) (hG : Function.Injective G)
    (f : ℝ × Z → X) (hf : InjOn f (Icc (-1 : ℝ) 1 ×ˢ A))
    (hbase : ∀ b z, z ∈ A → c (rim b z, 0) = f (if b then 1 else -1, z))
    (hlevel : ∀ b z, z ∈ A → G (c (rim b z, 0)) = c (rim b z, a))
    (hgap : ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ A, G (f z) ∉ c '' (K ×ˢ Ico (0 : ℝ) a)) :
    InjOn (commonCollarAttachment c rim G f a) (Icc (-2 : ℝ) 2 ×ˢ A) := by
  have hzero {b : Bool} {z : Z} (hz : z ∈ A) : (rim b z, (0 : ℝ)) ∈ K ×ˢ Icc (0 : ℝ) a :=
    ⟨hrim b hz, le_rfl, ha.le⟩
  have hrimi {b d : Bool} {z w : Z} (hz : z ∈ A) (hw : w ∈ A)
      (heq : rim b z = rim d w) : (b, z) = (d, w) := by
    have hv : f (if b then 1 else -1, z) = f (if d then 1 else -1, w) := by
      rw [← hbase b z hz, ← hbase d w hw, heq]
    have he := hf (x₁ := (if b then 1 else -1, z)) (x₂ := (if d then 1 else -1, w))
      ⟨by cases b <;> norm_num, hz⟩ ⟨by cases d <;> norm_num, hw⟩ hv
    have hb := congrArg Prod.fst he
    have hz' := congrArg Prod.snd he
    cases b <;> cases d
    · exact Prod.ext rfl hz'
    · norm_num at hb
    · norm_num at hb
    · exact Prod.ext rfl hz'
  have hlow {z : ℝ × Z} (hz : z ∈ Icc (-2 : ℝ) 2 ×ˢ A) (ht : z.1 ≤ -1) :
      (rim false z.2, a * (z.1 + 2)) ∈ K ×ˢ Icc (0 : ℝ) a := by
    refine ⟨hrim false hz.2, mul_nonneg ha.le (by linarith [hz.1.1]), ?_⟩
    nlinarith
  have hhigh {z : ℝ × Z} (hz : z ∈ Icc (-2 : ℝ) 2 ×ˢ A) (ht : 1 ≤ z.1) :
      (rim true z.2, a * (2 - z.1)) ∈ K ×ˢ Icc (0 : ℝ) a := by
    refine ⟨hrim true hz.2, mul_nonneg ha.le (by linarith [hz.1.2]), ?_⟩
    nlinarith
  have hcross {b : Bool} {z w : Z} {s t : ℝ}
      (hz : z ∈ A) (hw : w ∈ A) (hs : s ∈ Icc (0 : ℝ) a)
      (ht : t ∈ Ioo (-1 : ℝ) 1) : c (rim b z, s) ≠ G (f (t, w)) := by
    intro heq
    have hsEq : s = a := by
      apply le_antisymm hs.2
      by_contra hn
      exact hgap (t, w) ⟨⟨ht.1.le, ht.2.le⟩, hw⟩
        ⟨(rim b z, s), ⟨hrim b hz, hs.1, lt_of_not_ge hn⟩, heq⟩
    rw [hsEq, ← hlevel b z hz, hbase b z hz] at heq
    have hv := hf (x₁ := (if b then 1 else -1, z)) (x₂ := (t, w))
      ⟨by cases b <;> norm_num, hz⟩ ⟨⟨ht.1.le, ht.2.le⟩, hw⟩ (hG heq)
    have hh := congrArg Prod.fst hv
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] at hh <;> linarith [ht.1, ht.2]
  intro z hz w hw heq
  unfold commonCollarAttachment at heq
  by_cases hzlow : z.1 ≤ -1 <;> by_cases hzhigh : 1 ≤ z.1 <;>
    by_cases hwlow : w.1 ≤ -1 <;> by_cases hwhigh : 1 ≤ w.1
  all_goals try (exfalso; linarith)
  all_goals simp only [if_pos, hzlow, hzhigh, hwlow, hwhigh] at heq
  · have hsame := hc (hlow hz hzlow) (hlow hw hwlow) heq
    have hh := congrArg Prod.snd hsame
    have hz' := congrArg Prod.snd (hrimi hz.2 hw.2 (congrArg Prod.fst hsame))
    refine Prod.ext ?_ hz'
    change a * (z.1 + 2) = a * (w.1 + 2) at hh
    nlinarith
  · have hsame := hc (hlow hz hzlow) (hhigh hw hwhigh) heq
    have hbad := congrArg Prod.fst (hrimi hz.2 hw.2 (congrArg Prod.fst hsame))
    contradiction
  · exact (hcross hz.2 hw.2 (hlow hz hzlow).2
      ⟨lt_of_not_ge hwlow, lt_of_not_ge hwhigh⟩ heq).elim
  · have hsame := hc (hhigh hz hzhigh) (hlow hw hwlow) heq
    have hbad := congrArg Prod.fst (hrimi hz.2 hw.2 (congrArg Prod.fst hsame))
    contradiction
  · have hsame := hc (hhigh hz hzhigh) (hhigh hw hwhigh) heq
    have hh := congrArg Prod.snd hsame
    have hz' := congrArg Prod.snd (hrimi hz.2 hw.2 (congrArg Prod.fst hsame))
    refine Prod.ext ?_ hz'
    change a * (2 - z.1) = a * (2 - w.1) at hh
    nlinarith
  · exact (hcross hz.2 hw.2 (hhigh hz hzhigh).2
      ⟨lt_of_not_ge hwlow, lt_of_not_ge hwhigh⟩ heq).elim
  · exact (hcross hw.2 hz.2 (hlow hw hwlow).2
      ⟨lt_of_not_ge hzlow, lt_of_not_ge hzhigh⟩ heq.symm).elim
  · exact (hcross hw.2 hz.2 (hhigh hw hwhigh).2
      ⟨lt_of_not_ge hzlow, lt_of_not_ge hzhigh⟩ heq.symm).elim
  · exact hf ⟨⟨(lt_of_not_ge hzlow).le, (lt_of_not_ge hzhigh).le⟩, hz.2⟩
      ⟨⟨(lt_of_not_ge hwlow).le, (lt_of_not_ge hwhigh).le⟩, hw.2⟩ (hG heq)

end PoincareConjecture.M76
