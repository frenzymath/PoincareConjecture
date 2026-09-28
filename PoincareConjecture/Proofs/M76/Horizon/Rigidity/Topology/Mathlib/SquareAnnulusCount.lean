import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceEulerValuation










set_option autoImplicit false

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem surfaceEulerCount_four_strip_cover_eq_zero
    (K C₀ C₁ C₂ C₃ U₀₁ U₂₃ W : SimplicialComplex ℝ E)
    (hC₀ : C₀.faces.Finite) (hC₁ : C₁.faces.Finite)
    (hC₂ : C₂.faces.Finite) (hC₃ : C₃.faces.Finite)
    (hU₀₁ : U₀₁.faces = C₀.faces ∪ C₁.faces)
    (hU₂₃ : U₂₃.faces = C₂.faces ∪ C₃.faces)
    (hK : K.faces = U₀₁.faces ∪ U₂₃.faces)
    (hW : W.faces = (C₀ ⊓ C₃).faces ∪ (C₁ ⊓ C₂).faces)
    (hC₀count : C₀.surfaceEulerCount = 1)
    (hC₁count : C₁.surfaceEulerCount = 1)
    (hC₂count : C₂.surfaceEulerCount = 1)
    (hC₃count : C₃.surfaceEulerCount = 1)
    (h₀₁ : (C₀ ⊓ C₁).surfaceEulerCount = 1)
    (h₂₃ : (C₂ ⊓ C₃).surfaceEulerCount = 1)
    (h₀₃ : (C₀ ⊓ C₃).surfaceEulerCount = 1)
    (h₁₂ : (C₁ ⊓ C₂).surfaceEulerCount = 1)
    (hdisj₀₂ : (C₀ ⊓ C₂).faces = ∅)
    (hdisj₁₃ : (C₁ ⊓ C₃).faces = ∅)
    (hdisjW : ((C₀ ⊓ C₃) ⊓ (C₁ ⊓ C₂)).faces = ∅) :
    K.surfaceEulerCount = 0 := by
  have hU₀₁f : U₀₁.faces.Finite := hU₀₁ ▸ hC₀.union hC₁
  have hU₂₃f : U₂₃.faces.Finite := hU₂₃ ▸ hC₂.union hC₃
  have hI₀₁ : U₀₁.surfaceEulerCount + (C₀ ⊓ C₁).surfaceEulerCount =
      C₀.surfaceEulerCount + C₁.surfaceEulerCount :=
    surfaceEulerCount_union_add_inter C₀ C₁ U₀₁ hC₀ hC₁ hU₀₁
  have hI₂₃ : U₂₃.surfaceEulerCount + (C₂ ⊓ C₃).surfaceEulerCount =
      C₂.surfaceEulerCount + C₃.surfaceEulerCount :=
    surfaceEulerCount_union_add_inter C₂ C₃ U₂₃ hC₂ hC₃ hU₂₃
  have hU₀₁c : U₀₁.surfaceEulerCount = 1 := by
    omega
  have hU₂₃c : U₂₃.surfaceEulerCount = 1 := by
    omega
  have hWc : W.surfaceEulerCount = 2 := by
    have hWunion := surfaceEulerCount_union_add_inter
      (C₀ ⊓ C₃) (C₁ ⊓ C₂) W
      (hC₀.subset inf_le_left) (hC₁.subset inf_le_left) hW
    have hEmpty : ((C₀ ⊓ C₃) ⊓ (C₁ ⊓ C₂)).surfaceEulerCount = 0 := by
      unfold surfaceEulerCount
      have hface (n : ℕ) : IsEmpty (((C₀ ⊓ C₃) ⊓ (C₁ ⊓ C₂)).FaceOfCard n) := by
        exact ⟨fun s => by
          have hs : (s.1 : Finset E) ∈ ((C₀ ⊓ C₃) ⊓ (C₁ ⊓ C₂)).faces := s.2.1
          have hs' : (s.1 : Finset E) ∈ (∅ : Set (Finset E)) := hdisjW ▸ hs
          exact hs'⟩
      letI := hface 1
      have h1 : Nat.card (((C₀ ⊓ C₃) ⊓ (C₁ ⊓ C₂)).FaceOfCard 1) = 0 := Nat.card_of_isEmpty
      letI := hface 2
      have h2 : Nat.card (((C₀ ⊓ C₃) ⊓ (C₁ ⊓ C₂)).FaceOfCard 2) = 0 := Nat.card_of_isEmpty
      letI := hface 3
      have h3 : Nat.card (((C₀ ⊓ C₃) ⊓ (C₁ ⊓ C₂)).FaceOfCard 3) = 0 := Nat.card_of_isEmpty
      simp only [h1, h2, h3, Nat.cast_zero, sub_self, add_zero]
    omega
  have hcross : (U₀₁ ⊓ U₂₃).faces = W.faces := by
    rw [hW]
    ext s
    change ((s ∈ U₀₁.faces ∧ s ∈ U₂₃.faces) ↔ _)
    rw [hU₀₁, hU₂₃]
    change ((s ∈ C₀.faces ∨ s ∈ C₁.faces) ∧
      (s ∈ C₂.faces ∨ s ∈ C₃.faces)) ↔
      ((s ∈ C₀.faces ∧ s ∈ C₃.faces) ∨
        (s ∈ C₁.faces ∧ s ∈ C₂.faces))
    constructor
    · rintro ⟨hleft, hright⟩
      rcases hleft with hleft | hleft <;> rcases hright with hright | hright
      · have hs : s ∈ (C₀ ⊓ C₂).faces := ⟨hleft, hright⟩
        rw [hdisj₀₂] at hs
        exact hs.elim
      · exact Or.inl ⟨hleft, hright⟩
      · exact Or.inr ⟨hleft, hright⟩
      · have hs : s ∈ (C₁ ⊓ C₃).faces := ⟨hleft, hright⟩
        rw [hdisj₁₃] at hs
        exact hs.elim
    · intro hs
      rcases hs with hs | hs
      · exact ⟨Or.inl hs.1, Or.inr hs.2⟩
      · exact ⟨Or.inr hs.1, Or.inl hs.2⟩
  have hKunion := surfaceEulerCount_union_add_inter U₀₁ U₂₃ K hU₀₁f hU₂₃f hK
  have hcrosscount : (U₀₁ ⊓ U₂₃).surfaceEulerCount = W.surfaceEulerCount := by
    have hface (n : ℕ) : (U₀₁ ⊓ U₂₃).FaceOfCard n = W.FaceOfCard n :=
      congrArg (fun f : Set (Finset E) => {s // s ∈ f ∧ s.card = n}) hcross
    unfold surfaceEulerCount
    rw [hface 1, hface 2, hface 3]
  rw [hcrosscount, hU₀₁c, hU₂₃c, hWc] at hKunion
  omega

end Geometry.SimplicialComplex
