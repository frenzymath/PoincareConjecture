import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.MarkedAttachment



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "Q" => sphere (0 : Fin 2 → ℝ) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)
local notation "Ann" => squareAnnulus 8 1
local notation "Band" => squareAnnulus 1 (1 / 8 : ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_marked_square_collar_attachment {A S B M₀ M₁ : Set E}
    (a : Band ≃ₜ A) (c : Ann ≃ₜ S) (b : Band ≃ₜ B)
    (ha : a.IsFinitePL) (hc : c.IsFinitePL) (hb : b.IsFinitePL)
    (hdis : Disjoint A B) (σ τ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1)
    (hac : ∀ x : Band, (a x : E) ∈ S ↔ depth 1 x = σ / 8)
    (hca : ∀ x : Ann, (c x : E) ∈ A ↔ depth 8 x = -1)
    (hcb : ∀ x : Ann, (c x : E) ∈ B ↔ depth 8 x = 1)
    (hbc : ∀ x : Band, (b x : E) ∈ S ↔ depth 1 x = τ / 8)
    (hM₀ : M₀ ⊆ A) (hM₁ : M₁ ⊆ B)
    (haM : ∀ x : Band, (a x : E) ∈ M₀ ↔ depth 1 x = 0)
    (hbM : ∀ x : Band, (b x : E) ∈ M₁ ↔ depth 1 x = 0) :
    ∃ (T : Set E) (H : Ann ≃ₜ T), H.IsFinitePL ∧
      S ⊆ T ∧ T ⊆ (A ∪ S) ∪ B ∧ M₀ ⊆ T ∧ M₁ ⊆ T ∧
      (∀ x, (H x : E) ∈ M₀ ↔ depth 8 x = -1) ∧
      ∀ x, (H x : E) ∈ M₁ ↔ depth 8 x = 1 := by
  obtain ⟨D, hD, hDv⟩ := exists_finitePL_square_annulus_cylinder
  obtain ⟨C, hC, hCv⟩ := exists_selected_annulus_cylinder
  have hDi (x : Cyl) : depth 1 (D.symm x) = x.val.2 / 8 := by
    have h := hDv (D.symm x)
    rw [D.apply_symm_apply] at h
    linarith
  have hCi (x : Cyl) : depth 8 (C.symm x) = x.val.2 := by
    have h := hCv (C.symm x)
    rw [C.apply_symm_apply] at h
    exact h.symm
  refine exists_marked_half_collar_attachment (D.symm.trans a) (C.symm.trans c)
    (D.symm.trans b) (hD.symm.trans ha) (hC.symm.trans hc) (hD.symm.trans hb)
    hdis σ τ hσ hτ ?_ ?_ ?_ ?_ hM₀ hM₁ ?_ ?_
  · intro x
    change (a (D.symm x) : E) ∈ S ↔ _
    rw [hac, hDi]
    constructor <;> intro h <;> linarith
  · intro x
    change (c (C.symm x) : E) ∈ A ↔ _
    rw [hca, hCi]
  · intro x
    change (c (C.symm x) : E) ∈ B ↔ _
    rw [hcb, hCi]
  · intro x
    change (b (D.symm x) : E) ∈ S ↔ _
    rw [hbc, hDi]
    constructor <;> intro h <;> linarith
  · intro x
    change (a (D.symm x) : E) ∈ M₀ ↔ _
    rw [haM, hDi]
    constructor <;> intro h <;> linarith
  · intro x
    change (b (D.symm x) : E) ∈ M₁ ↔ _
    rw [hbM, hDi]
    constructor <;> intro h <;> linarith

end PoincareConjecture.M76.Dehn.Annuli
