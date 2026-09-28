import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic



set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Reverse



theorem image_cap_eq_translate_union_cylinder
    {E : Type*} [TopologicalSpace E]
    (B : Set (E × Real)) (Q : Set E) {a b d : Real} (hab : a ≤ b) (hd : 0 ≤ d)
    (hbelow : ∀ p ∈ B, a ≤ p.2)
    (hbelt : ∀ x z, z ∈ Icc a b → ((x, z) ∈ B ↔ x ∈ Q))
    (F : E × Real → E × Real) (hF : Continuous F)
    (hfirst : ∀ p, (F p).1 = p.1)
    (hmono : ∀ x, Monotone (fun z : Real => (F (x, z)).2))
    (hbottom : ∀ x ∈ Q, F (x, a) = (x, a))
    (htop : ∀ p ∈ B, b ≤ p.2 → F p = (p.1, p.2 + d)) :
    F '' B = (fun p : E × Real => (p.1, p.2 + d)) '' B ∪ (Q ×ˢ Icc a (a + d)) := by
  have hupper (x : E) (hx : x ∈ Q) : F (x, b) = (x, b + d) :=
    htop (x, b) ((hbelt x b ⟨hab, le_rfl⟩).mpr hx) le_rfl
  have hbetween (x : E) (hx : x ∈ Q) (z : Real) (hz : z ∈ Icc a (b + d)) :
      (x, z) ∈ F '' B := by
    have hc : Continuous (fun t : Real => (F (x, t)).2) := by fun_prop
    have ht : z ∈ Icc (F (x, a)).2 (F (x, b)).2 := by
      simpa only [hbottom x hx, hupper x hx] using hz
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hab hc.continuousOn ht
    exact ⟨(x, t), (hbelt x t ht).mpr hx, Prod.ext (hfirst (x, t)) he⟩
  apply Subset.antisymm
  · rintro _ ⟨⟨x, z⟩, hp, rfl⟩
    by_cases hz : b ≤ z
    · exact Or.inl ⟨(x, z), hp, (htop (x, z) hp hz).symm⟩
    have hza : a ≤ z := hbelow (x, z) hp
    have hzb : z ≤ b := (lt_of_not_ge hz).le
    have hx : x ∈ Q := (hbelt x z ⟨hza, hzb⟩).mp hp
    have hl : a ≤ (F (x, z)).2 := by
      simpa only [hbottom x hx] using hmono x hza
    have hu : (F (x, z)).2 ≤ b + d := by
      simpa only [hupper x hx] using hmono x hzb
    by_cases hy : (F (x, z)).2 ≤ a + d
    · exact Or.inr ⟨(hfirst (x, z)).symm ▸ hx, hl, hy⟩
    · refine Or.inl ⟨(x, (F (x, z)).2 - d), ?_, ?_⟩
      · exact (hbelt x _ ⟨by linarith, by linarith⟩).mpr hx
      · exact Prod.ext (hfirst (x, z)).symm (sub_add_cancel _ _)
  · rintro p (⟨⟨x, z⟩, hp, rfl⟩ | hp)
    · by_cases hz : b ≤ z
      · exact ⟨(x, z), hp, htop (x, z) hp hz⟩
      · have hza : a ≤ z := hbelow (x, z) hp
        have hzb : z ≤ b := (lt_of_not_ge hz).le
        exact hbetween x ((hbelt x z ⟨hza, hzb⟩).mp hp) (z + d)
          ⟨by linarith, by linarith⟩
    · exact hbetween p.1 hp.1 p.2 ⟨hp.2.1, by linarith [hp.2.2]⟩

end Poincare.Manifold.Schoenflies.Reverse
