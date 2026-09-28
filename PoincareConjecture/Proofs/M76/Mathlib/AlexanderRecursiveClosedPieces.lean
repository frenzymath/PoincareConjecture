import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarSlab










set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem AlexanderCollarSlab.isCompact_piece_of_closed_base
    {S X TX : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β) (hX : IsClosed X)
    (hTX : TX ⊆ M.collar)
    (hmem : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (M.chart p : E) ∈ TX ↔ (p : E × ℝ).1 ∈ X) : IsCompact TX := by
  let D : Set (E × ℝ) :=
    {p | p.1 ∈ S ∩ {x | A x = 0} ∧ p.2 ∈ Icc 0 (M.upper p.1)}
  have hcopy := M.chart_finitePL
  obtain ⟨_, ⟨K, hK, hKD, _⟩, _⟩ := hcopy
  have hD : IsCompact D := by
    dsimp only [D]
    rw [← hKD]
    exact K.isCompact_space_of_finite hK
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let B : Set D := {p | (p : E × ℝ).1 ∈ X}
  have hB : IsClosed B := hX.preimage (continuous_fst.comp continuous_subtype_val)
  let f : D → E := fun p => M.chart p
  have hf : Continuous f := continuous_subtype_val.comp M.chart.continuous
  have himage : f '' B = TX := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (hmem p).mpr hp
    · intro hx
      let p := M.chart.symm ⟨x, hTX hx⟩
      have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
      exact ⟨p, (hmem p).mp (hp.symm ▸ hx), hp⟩
  exact himage ▸ hB.isCompact.image hf

end Geometry
