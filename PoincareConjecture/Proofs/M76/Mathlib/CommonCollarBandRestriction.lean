import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBandTransport










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem IsFinitePL.exists_common_collarBand_restrictions
    {B : Set E} {T₀ T₁ : Set F} {lower₀ lower₁ upper : E → ℝ}
    {C₀ : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower₀ p.1) (upper p.1)} ≃ₜ T₀}
    {C₁ : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower₁ p.1) (upper p.1)} ≃ₜ T₁}
    (hC₀ : C₀.IsFinitePL) (hC₁ : C₁.IsFinitePL) (A : F →ᵃ[ℝ] ℝ)
    (hheight₀ : ∀ p, A (C₀ p) = (p : E × ℝ).2)
    (hheight₁ : ∀ p, A (C₁ p) = (p : E × ℝ).2)
    {a b : ℝ} (hbound₀ : ∀ x ∈ B, lower₀ x ≤ a)
    (hbound₁ : ∀ x ∈ B, lower₁ x ≤ a) :
    ∃ D₀ : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc a b ∧ p.2 ≤ upper p.1} ≃ₜ
        (T₀ ∩ {y | A y ∈ Icc a b} : Set F),
      ∃ D₁ : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc a b ∧ p.2 ≤ upper p.1} ≃ₜ
          (T₁ ∩ {y | A y ∈ Icc a b} : Set F),
        D₀.IsFinitePL ∧ D₁.IsFinitePL ∧
        (∀ p, A (D₀ p) = (p : E × ℝ).2) ∧
        (∀ p, A (D₁ p) = (p : E × ℝ).2) ∧
        (∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc a b ∧ p.2 ≤ upper p.1},
          (D₀ p : F) = C₀ ⟨p, p.property.1,
            (hbound₀ _ p.property.1).trans p.property.2.1.1, p.property.2.2⟩) ∧
        ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc a b ∧ p.2 ≤ upper p.1},
          (D₁ p : F) = C₁ ⟨p, p.property.1,
            (hbound₁ _ p.property.1).trans p.property.2.1.1, p.property.2.2⟩ := by
  let W : Set (E × ℝ) := {p | p.1 ∈ B ∧ p.2 ∈ Icc a b ∧ p.2 ≤ upper p.1}
  let L : E × ℝ →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ E ℝ).toAffineMap
  have heq {lower : E → ℝ} (hbound : ∀ x ∈ B, lower x ≤ a) :
      ({p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} ∩
        {p | L p ∈ Icc a b}) = W := by
    ext p
    constructor
    · exact fun hp => ⟨hp.1.1, hp.2, hp.1.2.2⟩
    · exact fun hp => ⟨⟨hp.1, (hbound p.1 hp.1).trans hp.2.1.1, hp.2.2⟩, hp.2.1⟩
  obtain ⟨G₀, hG₀, hG₀val, hG₀height⟩ :=
    hC₀.exists_affineBand_restriction L A hheight₀ a b
  obtain ⟨G₁, hG₁, hG₁val, hG₁height⟩ :=
    hC₁.exists_affineBand_restriction L A hheight₁ a b
  let D₀ := (Homeomorph.setCongr (heq hbound₀).symm).trans
    (G₀.trans (Homeomorph.setCongr rfl))
  let D₁ := (Homeomorph.setCongr (heq hbound₁).symm).trans
    (G₁.trans (Homeomorph.setCongr rfl))
  exact ⟨D₀, D₁, hG₀.setCongr (heq hbound₀) rfl,
    hG₁.setCongr (heq hbound₁) rfl,
    fun p => hG₀height ⟨p, (heq hbound₀).symm ▸ p.property⟩,
    fun p => hG₁height ⟨p, (heq hbound₁).symm ▸ p.property⟩,
    fun p => hG₀val ⟨p, (heq hbound₀).symm ▸ p.property⟩,
    fun p => hG₁val ⟨p, (heq hbound₁).symm ▸ p.property⟩⟩

end Homeomorph
