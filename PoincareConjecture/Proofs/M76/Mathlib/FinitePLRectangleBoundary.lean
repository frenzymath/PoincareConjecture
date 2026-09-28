import PoincareConjecture.Proofs.M76.Mathlib.FinitePLRectangleSides
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem union_disjoint {s u : Set E} {t v : Set F}
    (e : s ≃ₜ t) (d : u ≃ₜ v) (he : e.IsFinitePL) (hd : d.IsFinitePL)
    (hs : Disjoint s u) (ht : Disjoint t v) :
    ∃ H : (s ∪ u : Set E) ≃ₜ (t ∪ v : Set F), H.IsFinitePL ∧
      (∀ x : s, (H ⟨x, Or.inl x.property⟩ : F) = e x) ∧
      (∀ x : u, (H ⟨x, Or.inr x.property⟩ : F) = d x) := by
  apply exists_union_finitePL e d he hd
  · intro x
    exact iff_of_false (disjoint_left.mp hs x.property)
      (disjoint_left.mp ht (e x).property)
  · intro x hx hu
    exact (disjoint_left.mp hs hx hu).elim

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]







theorem exists_height_preserving_rectangle_boundary
    {α β : ℝ} (hαβ : α < β) {s₀ s₁ l r : Set X}
    (e₀ : Icc (0 : ℝ) 1 ≃ₜ s₀) (e₁ : Icc (0 : ℝ) 1 ≃ₜ s₁)
    (d₀ : Icc α β ≃ₜ l) (d₁ : Icc α β ≃ₜ r)
    (he₀ : e₀.IsFinitePL) (he₁ : e₁.IsFinitePL)
    (hd₀ : d₀.IsFinitePL) (hd₁ : d₁.IsFinitePL)
    (A : X → ℝ) (h₀ : ∀ x, A (e₀ x) = α) (h₁ : ∀ x, A (e₁ x) = β)
    (hleft : ∀ x, A (d₀ x) = (x : ℝ))
    (hright : ∀ x, A (d₁ x) = (x : ℝ)) (hdisj : Disjoint l r)
    (h₀₀ : (e₀ ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : X) = d₀ ⟨α, ⟨le_rfl, hαβ.le⟩⟩)
    (h₀₁ : (e₀ ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : X) = d₁ ⟨α, ⟨le_rfl, hαβ.le⟩⟩)
    (h₁₀ : (e₁ ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : X) = d₀ ⟨β, ⟨hαβ.le, le_rfl⟩⟩)
    (h₁₁ : (e₁ ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : X) = d₁ ⟨β, ⟨hαβ.le, le_rfl⟩⟩) :
    ∃ H : (((Icc (0 : ℝ) 1 ×ˢ {α}) ∪ (Icc (0 : ℝ) 1 ×ˢ {β})) ∪
        (({0} ×ˢ Icc α β) ∪ ({1} ×ˢ Icc α β)) : Set (ℝ × ℝ)) ≃ₜ
        ((s₀ ∪ s₁) ∪ (l ∪ r) : Set X),
      H.IsFinitePL ∧ (∀ x, A (H x) = (x : ℝ × ℝ).2) ∧
      (∀ x : Icc (0 : ℝ) 1,
        (H ⟨(x, α), Or.inl (Or.inl ⟨x.property, rfl⟩)⟩ : X) = e₀ x) ∧
      (∀ x : Icc (0 : ℝ) 1,
        (H ⟨(x, β), Or.inl (Or.inr ⟨x.property, rfl⟩)⟩ : X) = e₁ x) ∧
      (∀ y : Icc α β,
        (H ⟨(0, y), Or.inr (Or.inl ⟨rfl, y.property⟩)⟩ : X) = d₀ y) ∧
      (∀ y : Icc α β,
        (H ⟨(1, y), Or.inr (Or.inr ⟨rfl, y.property⟩)⟩ : X) = d₁ y) := by
  let B : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ {α}
  let T : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ {β}
  let L : Set (ℝ × ℝ) := {0} ×ˢ Icc α β
  let R : Set (ℝ × ℝ) := {1} ×ˢ Icc α β
  obtain ⟨b, hb, hbval⟩ := he₀.exists_horizontal_interval_chart α
  obtain ⟨t, ht, htval⟩ := he₁.exists_horizontal_interval_chart β
  obtain ⟨j, hj, hjval⟩ := hd₀.exists_vertical_interval_chart 0
  obtain ⟨k, hk, hkval⟩ := hd₁.exists_vertical_interval_chart 1
  have hBT : Disjoint B T := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hαβ.ne (hx.2.symm.trans hy.2)
  have hLR : Disjoint L R := by
    apply disjoint_left.mpr
    intro x hx hy
    exact zero_ne_one (hx.1.symm.trans hy.1)
  have hs : Disjoint s₀ s₁ := by
    apply disjoint_left.mpr
    intro x hx hy
    have ha : A x = α := by
      simpa only [apply_symm_apply] using h₀ (e₀.symm ⟨x, hx⟩)
    have hb' : A x = β := by
      simpa only [apply_symm_apply] using h₁ (e₁.symm ⟨x, hy⟩)
    exact hαβ.ne (ha.symm.trans hb')
  obtain ⟨u, hu, hub, hut⟩ := union_disjoint b t hb ht hBT hs
  obtain ⟨v, hv, hvj, hvk⟩ := union_disjoint j k hj hk hLR hdisj
  have hbL (x : B) : (b x : X) ∈ l ↔ (x : ℝ × ℝ).1 = 0 := by
    rw [hbval]
    exact (mem_side_iff_of_height e₀ d₀ A ⟨0, ⟨le_rfl, zero_le_one⟩⟩
      ⟨α, ⟨le_rfl, hαβ.le⟩⟩ h₀ hleft h₀₀ _).trans Subtype.ext_iff
  have hbR (x : B) : (b x : X) ∈ r ↔ (x : ℝ × ℝ).1 = 1 := by
    rw [hbval]
    exact (mem_side_iff_of_height e₀ d₁ A ⟨1, ⟨zero_le_one, le_rfl⟩⟩
      ⟨α, ⟨le_rfl, hαβ.le⟩⟩ h₀ hright h₀₁ _).trans Subtype.ext_iff
  have htL (x : T) : (t x : X) ∈ l ↔ (x : ℝ × ℝ).1 = 0 := by
    rw [htval]
    exact (mem_side_iff_of_height e₁ d₀ A ⟨0, ⟨le_rfl, zero_le_one⟩⟩
      ⟨β, ⟨hαβ.le, le_rfl⟩⟩ h₁ hleft h₁₀ _).trans Subtype.ext_iff
  have htR (x : T) : (t x : X) ∈ r ↔ (x : ℝ × ℝ).1 = 1 := by
    rw [htval]
    exact (mem_side_iff_of_height e₁ d₁ A ⟨1, ⟨zero_le_one, le_rfl⟩⟩
      ⟨β, ⟨hαβ.le, le_rfl⟩⟩ h₁ hright h₁₁ _).trans Subtype.ext_iff
  have hside (x : (B ∪ T : Set (ℝ × ℝ))) : (x : ℝ × ℝ) ∈ L ∪ R ↔
      (x : ℝ × ℝ).1 = 0 ∨ (x : ℝ × ℝ).1 = 1 := by
    have hheight : (x : ℝ × ℝ).2 ∈ Icc α β := by
      rcases x.property with h | h
      · rw [h.2]
        exact ⟨le_rfl, hαβ.le⟩
      · rw [h.2]
        exact ⟨hαβ.le, le_rfl⟩
    simp only [L, R, mem_union, mem_prod, mem_singleton_iff, hheight, and_true]
  have hoverlap (x : (B ∪ T : Set (ℝ × ℝ))) :
      (x : ℝ × ℝ) ∈ L ∪ R ↔ (u x : X) ∈ l ∪ r := by
    rw [hside]
    rcases x.property with hx | hx
    · rw [hub ⟨x, hx⟩, mem_union, hbL, hbR]
    · rw [hut ⟨x, hx⟩, mem_union, htL, htR]
  have hagree (x : ℝ × ℝ) (hx : x ∈ B ∪ T) (hy : x ∈ L ∪ R) :
      (u ⟨x, hx⟩ : X) = v ⟨x, hy⟩ := by
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hub ⟨x, hx⟩, hvj ⟨x, hy⟩, hbval, hjval]
      have hx0 : (⟨x.1, hx.1⟩ : Icc (0 : ℝ) 1) = ⟨0, ⟨le_rfl, zero_le_one⟩⟩ :=
        Subtype.ext hy.1
      have hya : (⟨x.2, hy.2⟩ : Icc α β) = ⟨α, ⟨le_rfl, hαβ.le⟩⟩ :=
        Subtype.ext hx.2
      rw [hx0, hya]
      exact h₀₀
    · rw [hub ⟨x, hx⟩, hvk ⟨x, hy⟩, hbval, hkval]
      have hx1 : (⟨x.1, hx.1⟩ : Icc (0 : ℝ) 1) = ⟨1, ⟨zero_le_one, le_rfl⟩⟩ :=
        Subtype.ext hy.1
      have hya : (⟨x.2, hy.2⟩ : Icc α β) = ⟨α, ⟨le_rfl, hαβ.le⟩⟩ :=
        Subtype.ext hx.2
      rw [hx1, hya]
      exact h₀₁
    · rw [hut ⟨x, hx⟩, hvj ⟨x, hy⟩, htval, hjval]
      have hx0 : (⟨x.1, hx.1⟩ : Icc (0 : ℝ) 1) = ⟨0, ⟨le_rfl, zero_le_one⟩⟩ :=
        Subtype.ext hy.1
      have hyb : (⟨x.2, hy.2⟩ : Icc α β) = ⟨β, ⟨hαβ.le, le_rfl⟩⟩ :=
        Subtype.ext hx.2
      rw [hx0, hyb]
      exact h₁₀
    · rw [hut ⟨x, hx⟩, hvk ⟨x, hy⟩, htval, hkval]
      have hx1 : (⟨x.1, hx.1⟩ : Icc (0 : ℝ) 1) = ⟨1, ⟨zero_le_one, le_rfl⟩⟩ :=
        Subtype.ext hy.1
      have hyb : (⟨x.2, hy.2⟩ : Icc α β) = ⟨β, ⟨hαβ.le, le_rfl⟩⟩ :=
        Subtype.ext hx.2
      rw [hx1, hyb]
      exact h₁₁
  obtain ⟨H, hH, hHu, hHv⟩ := exists_union_finitePL u v hu hv hoverlap hagree
  refine ⟨H, hH, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rcases x.property with (hx | hx) | (hx | hx)
    · rw [hHu ⟨x, Or.inl hx⟩, hub ⟨x, hx⟩, hbval, h₀]
      exact hx.2.symm
    · rw [hHu ⟨x, Or.inr hx⟩, hut ⟨x, hx⟩, htval, h₁]
      exact hx.2.symm
    · rw [hHv ⟨x, Or.inl hx⟩, hvj ⟨x, hx⟩, hjval, hleft]
    · rw [hHv ⟨x, Or.inr hx⟩, hvk ⟨x, hx⟩, hkval, hright]
  · intro x
    exact (hHu ⟨(x, α), Or.inl ⟨x.property, rfl⟩⟩).trans
      ((hub ⟨(x, α), ⟨x.property, rfl⟩⟩).trans (hbval _))
  · intro x
    exact (hHu ⟨(x, β), Or.inr ⟨x.property, rfl⟩⟩).trans
      ((hut ⟨(x, β), ⟨x.property, rfl⟩⟩).trans (htval _))
  · intro y
    exact (hHv ⟨(0, y), Or.inl ⟨rfl, y.property⟩⟩).trans
      ((hvj ⟨(0, y), ⟨rfl, y.property⟩⟩).trans (hjval _))
  · intro y
    exact (hHv ⟨(1, y), Or.inr ⟨rfl, y.property⟩⟩).trans
      ((hvk ⟨(1, y), ⟨rfl, y.property⟩⟩).trans (hkval _))

end Homeomorph
