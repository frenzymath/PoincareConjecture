import PoincareConjecture.Proofs.M76.Mathlib.CollarLevelResidualGluing











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {V E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]






theorem IsFinitePL.exists_height_preserving_union_fixing_residual
    {S q : Set V} {T₀ T₁ R : Set E} {L₀ : S ≃ₜ T₀} (hL₀ : L₀.IsFinitePL)
    {L₁ : S ≃ₜ T₁} (hL₁ : L₁.IsFinitePL)
    (hcontact₀ : ∀ x : S, (L₀ x : E) ∈ R ↔ (x : V) ∈ q)
    (hcontact₁ : ∀ x : S, (L₁ x : E) ∈ R ↔ (x : V) ∈ q)
    (hcontact : ∀ x : S, (x : V) ∈ q → (L₀ x : E) = L₁ x)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (A : E → ℝ) (hheight : ∀ x : S, A (L₁ x) = A (L₀ x)) :
    ∃ F : (T₀ ∪ R : Set E) ≃ₜ (T₁ ∪ R : Set E), F.IsFinitePL ∧
      (∀ x : (T₀ ∪ R : Set E), A (F x) = A x) ∧
      (∀ x : R, (F ⟨x, Or.inr x.property⟩ : E) = x) ∧
      (∀ x : S, (F ⟨L₀ x, Or.inl (L₀ x).property⟩ : E) = L₁ x) ∧
      (∀ x : (T₀ ∪ R : Set E), (x : E) ∈ T₀ ↔ (F x : E) ∈ T₁) ∧
      ∀ x : (T₀ ∪ R : Set E), (x : E) ∈ R ↔ (F x : E) ∈ R := by
  obtain ⟨F, hF, hFR, hFC, hF₀, hFRmem⟩ :=
    hL₀.exists_union_homeomorph_fixing_residual hL₁ hcontact₀ hcontact₁
      hcontact J hJ hJR
  refine ⟨F, hF, ?_, hFR, hFC, hF₀, hFRmem⟩
  intro x
  rcases x.property with hx | hx
  · let p := L₀.symm ⟨x, hx⟩
    have hp : (L₀ p : E) = x := congrArg Subtype.val (L₀.apply_symm_apply _)
    have hxp : (⟨L₀ p, Or.inl (L₀ p).property⟩ : (T₀ ∪ R : Set E)) = x :=
      Subtype.ext hp
    have hFx : (F x : E) = L₁ p := hxp ▸ hFC p
    exact (congrArg A hFx).trans ((hheight p).trans (congrArg A hp))
  · exact congrArg A (hFR ⟨x, hx⟩)

end Homeomorph
