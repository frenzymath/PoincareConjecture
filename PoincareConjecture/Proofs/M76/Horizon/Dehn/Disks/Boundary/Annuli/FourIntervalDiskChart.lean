import PoincareConjecture.Proofs.M76.Mathlib.FinitePLRectangleBoundary
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "I" => Icc (0 : ℝ) 1
local notation "P2" => (ℝ × ℝ)

theorem square_chart_horizontal_mem_iff {D s : Set P2}
    (H : (I ×ˢ I : Set P2) ≃ₜ D) (p : I ≃ₜ s) {c : ℝ} (hc : c ∈ I)
    (hside : ∀ t : I, (H ⟨(t, c), t.property, hc⟩ : P2) = p t)
    (z : (I ×ˢ I : Set P2)) : (H z : P2) ∈ s ↔ (z : P2).2 = c := by
  constructor
  · intro hz
    let t := p.symm ⟨H z, hz⟩
    have hh : H z = H ⟨(t, c), t.property, hc⟩ := by
      apply Subtype.ext
      rw [hside]
      exact (congrArg Subtype.val (p.apply_symm_apply ⟨H z, hz⟩)).symm
    exact congrArg (fun w : (I ×ˢ I : Set P2) ↦ (w : P2).2) (H.injective hh)
  · intro hz
    have hh : z = ⟨(z.val.1, c), z.property.1, hc⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl hz
    rw [hh, hside ⟨z.val.1, z.property.1⟩]
    exact (p ⟨z.val.1, z.property.1⟩).property

theorem square_chart_vertical_mem_iff {D s : Set P2}
    (H : (I ×ˢ I : Set P2) ≃ₜ D) (p : I ≃ₜ s) {c : ℝ} (hc : c ∈ I)
    (hside : ∀ t : I, (H ⟨(c, t), hc, t.property⟩ : P2) = p t)
    (z : (I ×ˢ I : Set P2)) : (H z : P2) ∈ s ↔ (z : P2).1 = c := by
  constructor
  · intro hz
    let t := p.symm ⟨H z, hz⟩
    have hh : H z = H ⟨(c, t), hc, t.property⟩ := by
      apply Subtype.ext
      rw [hside]
      exact (congrArg Subtype.val (p.apply_symm_apply ⟨H z, hz⟩)).symm
    exact congrArg (fun w : (I ×ˢ I : Set P2) ↦ (w : P2).1) (H.injective hh)
  · intro hz
    have hh : z = ⟨(c, z.val.2), hc, z.property.2⟩ := by
      apply Subtype.ext
      exact Prod.ext hz rfl
    rw [hh, hside ⟨z.val.2, z.property.2⟩]
    exact (p ⟨z.val.2, z.property.2⟩).property



theorem exists_four_interval_disk_chart {D s₀ s₁ l r : Set P2} {a b c d : P2}
    (hD : IsFinitePLBallPair P2 D ((s₀ ∪ s₁) ∪ (l ∪ r)))
    (p₀ : I ≃ₜ s₀) (p₁ : I ≃ₜ s₁) (q₀ : I ≃ₜ l) (q₁ : I ≃ₜ r)
    (hp₀ : p₀.IsFinitePL) (hp₁ : p₁.IsFinitePL)
    (hq₀ : q₀.IsFinitePL) (hq₁ : q₁.IsFinitePL)
    (hp₀a : (p₀ ⟨0, by norm_num⟩ : P2) = a)
    (hp₀b : (p₀ ⟨1, by norm_num⟩ : P2) = b)
    (hp₁c : (p₁ ⟨0, by norm_num⟩ : P2) = c)
    (hp₁d : (p₁ ⟨1, by norm_num⟩ : P2) = d)
    (hq₀a : (q₀ ⟨0, by norm_num⟩ : P2) = a)
    (hq₀c : (q₀ ⟨1, by norm_num⟩ : P2) = c)
    (hq₁b : (q₁ ⟨0, by norm_num⟩ : P2) = b)
    (hq₁d : (q₁ ⟨1, by norm_num⟩ : P2) = d)
    (hs : Disjoint s₀ s₁) (hlr : Disjoint l r)
    (h₀l : s₀ ∩ l = {a}) (h₀r : s₀ ∩ r = {b})
    (h₁l : s₁ ∩ l = {c}) (h₁r : s₁ ∩ r = {d}) :
    ∃ H : (I ×ˢ I : Set P2) ≃ₜ D, H.IsFinitePL ∧
      (∀ t : I, (H ⟨(t, 0), t.property, by norm_num⟩ : P2) = p₀ t) ∧
      (∀ t : I, (H ⟨(t, 1), t.property, by norm_num⟩ : P2) = p₁ t) ∧
      (∀ t : I, (H ⟨(0, t), by norm_num, t.property⟩ : P2) = q₀ t) ∧
      (∀ t : I, (H ⟨(1, t), by norm_num, t.property⟩ : P2) = q₁ t) := by
  classical
  let A : P2 → ℝ := fun z ↦ if hz : z ∈ l then (q₀.symm ⟨z, hz⟩ : ℝ)
    else if hz : z ∈ r then (q₁.symm ⟨z, hz⟩ : ℝ) else if z ∈ s₁ then 1 else 0
  have hleft (t : I) : A (q₀ t) = t := by simp [A, (q₀ t).property]
  have hright (t : I) : A (q₁ t) = t := by
    have hn : (q₁ t : P2) ∉ l := fun h ↦ disjoint_left.mp hlr h (q₁ t).property
    simp [A, hn, (q₁ t).property]
  have hbottom (t : I) : A (p₀ t) = 0 := by
    by_cases hl : (p₀ t : P2) ∈ l
    · have hh : (p₀ t : P2) = a := h₀l.subset ⟨(p₀ t).property, hl⟩
      rw [hh, ← hq₀a, hleft]
    by_cases hr : (p₀ t : P2) ∈ r
    · have hh : (p₀ t : P2) = b := h₀r.subset ⟨(p₀ t).property, hr⟩
      rw [hh, ← hq₁b, hright]
    have hn : (p₀ t : P2) ∉ s₁ := disjoint_left.mp hs (p₀ t).property
    simp [A, hl, hr, hn]
  have htop (t : I) : A (p₁ t) = 1 := by
    by_cases hl : (p₁ t : P2) ∈ l
    · have hh : (p₁ t : P2) = c := h₁l.subset ⟨(p₁ t).property, hl⟩
      rw [hh, ← hq₀c, hleft]
    by_cases hr : (p₁ t : P2) ∈ r
    · have hh : (p₁ t : P2) = d := h₁r.subset ⟨(p₁ t).property, hr⟩
      rw [hh, ← hq₁d, hright]
    simp [A, hl, hr, (p₁ t).property]
  obtain ⟨B, hB, _, hB₀, hB₁, hBl, hBr⟩ :=
    Homeomorph.exists_height_preserving_rectangle_boundary zero_lt_one p₀ p₁ q₀ q₁
      hp₀ hp₁ hq₀ hq₁ A hbottom htop hleft hright hlr
      (hp₀a.trans hq₀a.symm) (hp₀b.trans hq₁b.symm)
      (hp₁c.trans hq₀c.symm) (hp₁d.trans hq₁d.symm)
  have hbox : IsFinitePLBallPair P2 (I ×ˢ I : Set P2)
      (((I ×ˢ {0}) ∪ (I ×ˢ {1})) ∪ (({0} ×ˢ I) ∪ ({1} ×ˢ I))) := by
    have h := (isFinitePLBallPair_Icc zero_lt_one).prod (isFinitePLBallPair_Icc zero_lt_one)
    convert h using 1
    ext z
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  obtain ⟨H, hH, hHB, _⟩ := hbox.exists_extension hD B hB
  refine ⟨H, hH, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (congrArg Subtype.val (hHB ⟨(t, 0), Or.inl (Or.inl ⟨t.property, rfl⟩)⟩)).trans (hB₀ t)
  · intro t
    exact (congrArg Subtype.val (hHB ⟨(t, 1), Or.inl (Or.inr ⟨t.property, rfl⟩)⟩)).trans (hB₁ t)
  · intro t
    exact (congrArg Subtype.val (hHB ⟨(0, t), Or.inr (Or.inl ⟨rfl, t.property⟩)⟩)).trans (hBl t)
  · intro t
    exact (congrArg Subtype.val (hHB ⟨(1, t), Or.inr (Or.inr ⟨rfl, t.property⟩)⟩)).trans (hBr t)

end PoincareConjecture.M76.Dehn
