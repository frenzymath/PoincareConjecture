import PoincareConjecture.Proofs.M76.Mathlib.AlexanderCollarWidthRestriction
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarTransport











set_option autoImplicit false

open Set

namespace Geometry.AlexanderCollarSlab

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem exists_small_supported_capped_cut
    {S s₀ s₁ d : Set E} {B : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S B q β)
    (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁) (hunion : s₀ ∪ s₁ = S)
    (hq : q ∈ s₀) (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hKs : K.space = s₀)
    (L : E → ℝ) {δ c : ℝ} (hδ : 0 < δ) (hc : δ < |c|)
    (hdistance : ∀ x : E, |B x| = |L x - c|)
    (hcut : s₀ ∩ s₁ ⊆ {x | L x = 0}) (hd : d ⊆ {x | L x = 0})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, γ ∈ Ioo 0 ε ∧ γ ≤ β ∧
      ∀ H : E ≃ₜ E, (∀ x, δ ≤ |L x| → H x = x) →
        (H '' (s₀ ∪ d)) ∩ {x | B x ∈ Icc 0 γ} =
          s₀ ∩ {x | B x ∈ Icc 0 γ} ∧
        Nonempty (AlexanderCollarSlab (H '' (s₀ ∪ d)) B q γ) := by
  let m := min β (min ε (|c| - δ))
  have hm : 0 < m := lt_min M.width_pos (lt_min hε (sub_pos.mpr hc))
  have hmβ : m ≤ β := min_le_left _ _
  have hmε : m ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hmd : m ≤ |c| - δ := (min_le_right _ _).trans (min_le_right _ _)
  let γ := m / 2
  have hγ : γ ∈ Ioo 0 ε := by
    dsimp only [γ]
    constructor <;> linarith
  have hγβ : γ ≤ β := by dsimp only [γ]; linarith
  have hsep : δ + γ ≤ |c| := by dsimp only [γ]; linarith
  obtain ⟨N, _, _, _⟩ := M.exists_width_restriction hγ.1 hγβ
  have hband : ∀ x : E, B x ∈ Icc 0 γ → δ ≤ |L x| := by
    intro x hx
    have hnear : |L x - c| ≤ γ := by
      rw [← hdistance x, abs_of_nonneg hx.1]
      exact hx.2
    have htriangle : |c| ≤ |L x| + |L x - c| := by
      calc
        |c| = |L x + (c - L x)| := by congr 1; ring
        _ ≤ |L x| + |c - L x| := abs_add_le _ _
        _ = |L x| + |L x - c| := by rw [abs_sub_comm c (L x)]
    linarith
  refine ⟨γ, hγ, hγβ, ?_⟩
  intro H hfix
  exact N.nonempty_supported_capped_cut hs₀ hs₁ hunion hq K hK hKs L hδ
    hcut hd hband H hfix

end Geometry.AlexanderCollarSlab
