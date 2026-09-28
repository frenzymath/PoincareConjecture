import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Strips.RimIntervals
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.FourIntervalDiskChart

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem exists_retained_disk_square_chart
    {E Q₀ Q₁ W₀ W₁ : Set P2} {a₀ b₀ a₁ b₁ : P2}
    (hE : IsFinitePLBallPair P2 E (((E ∩ (Q₀ ∪ Q₁)) ∪ W₀) ∪ W₁))
    (hW₀ : IsFinitePLBallPair ℝ W₀ {a₀, b₀})
    (hW₁ : IsFinitePLBallPair ℝ W₁ {a₁, b₁})
    (hdisW : Disjoint W₀ W₁) (hQ₀ : IsClosed Q₀) (hQ₁ : IsClosed Q₁)
    (hdisQ : Disjoint Q₀ Q₁)
    (hW₀Q₀ : W₀ ∩ Q₀ = {a₀}) (hW₀Q₁ : W₀ ∩ Q₁ = {b₀})
    (hW₁Q₀ : W₁ ∩ Q₀ = {a₁}) (hW₁Q₁ : W₁ ∩ Q₁ = {b₁})
    (l : I ≃ₜ W₀) (r : I ≃ₜ W₁) (hl : l.IsFinitePL) (hr : r.IsFinitePL)
    (hl0 : (l ⟨0, by norm_num⟩ : P2) = a₀)
    (hl1 : (l ⟨1, by norm_num⟩ : P2) = b₀)
    (hr0 : (r ⟨0, by norm_num⟩ : P2) = a₁)
    (hr1 : (r ⟨1, by norm_num⟩ : P2) = b₁) :
    ∃ H : Sq ≃ₜ E, H.IsFinitePL ∧
      (∀ t : I, (H ⟨(0, t), by norm_num, t.property⟩ : P2) = l t) ∧
      (∀ t : I, (H ⟨(1, t), by norm_num, t.property⟩ : P2) = r t) ∧
      (∀ z : Sq, (H z : P2) ∈ Q₀ ↔ (z : P2).2 = 0) ∧
      (∀ z : Sq, (H z : P2) ∈ Q₁ ↔ (z : P2).2 = 1) := by
  obtain ⟨h₀, h₁⟩ := exists_retained_disk_rim_intervals hE hW₀ hW₁ hdisW
    hQ₀ hQ₁ hdisQ hW₀Q₀ hW₀Q₁ hW₁Q₀ hW₁Q₁
  have haa : a₀ ≠ a₁ := fun h ↦ disjoint_left.mp hdisW
    (hW₀.1 (Or.inl rfl)) (h ▸ hW₁.1 (Or.inl rfl))
  have hbb : b₀ ≠ b₁ := fun h ↦ disjoint_left.mp hdisW
    (hW₀.1 (Or.inr rfl)) (h ▸ hW₁.1 (Or.inr rfl))
  obtain ⟨p, hp, hp0, hp1⟩ := h₀.exists_unitInterval_chart_with_endpoints haa
  obtain ⟨q, hq, hq0, hq1⟩ := h₁.exists_unitInterval_chart_with_endpoints hbb
  have hWE₀ : W₀ ⊆ E := fun _ h ↦ hE.1 (Or.inl (Or.inr h))
  have hWE₁ : W₁ ⊆ E := fun _ h ↦ hE.1 (Or.inr h)
  have hcontact {W Q : Set P2} {a : P2} (hWE : W ⊆ E) (hWQ : W ∩ Q = {a}) :
      (E ∩ Q) ∩ W = {a} := by
    rw [← hWQ]
    ext x
    constructor
    · rintro ⟨⟨_, hQ⟩, hW⟩
      exact ⟨hW, hQ⟩
    · rintro ⟨hW, hQ⟩
      exact ⟨⟨hWE hW, hQ⟩, hW⟩
  have hball : IsFinitePLBallPair P2 E (((E ∩ Q₀) ∪ (E ∩ Q₁)) ∪ (W₀ ∪ W₁)) := by
    convert hE using 1
    ext x
    simp only [mem_union, mem_inter_iff]
    tauto
  obtain ⟨H, hH, hHp, hHq, hHl, hHr⟩ := exists_four_interval_disk_chart hball
    p q l r hp hq hl hr hp0 hp1 hq0 hq1 hl0 hl1 hr0 hr1
    (hdisQ.mono inter_subset_right inter_subset_right) hdisW
    (hcontact hWE₀ hW₀Q₀) (hcontact hWE₁ hW₁Q₀)
    (hcontact hWE₀ hW₀Q₁) (hcontact hWE₁ hW₁Q₁)
  refine ⟨H, hH, hHl, hHr, ?_, ?_⟩
  · intro z
    simpa only [mem_inter_iff, (H z).property, true_and] using
      square_chart_horizontal_mem_iff H p (by norm_num) hHp z
  · intro z
    simpa only [mem_inter_iff, (H z).property, true_and] using
      square_chart_horizontal_mem_iff H q (by norm_num) hHq z

end PoincareConjecture.M76.Dehn
