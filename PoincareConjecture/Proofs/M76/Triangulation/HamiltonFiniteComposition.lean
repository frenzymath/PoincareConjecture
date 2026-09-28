import PoincareConjecture.Proofs.M76.Triangulation.HamiltonAtlasHandleStep










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76





theorem exists_finite_supported_atlas_composition
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ι → OpenPartialHomeomorph X E) (d : OpenPartialHomeomorph X E)
    (hd : d.source = univ) (P : ℕ → Set X) (hP0 : P 0 = ∅)
    (n : ℕ) (W : Set X)
    (hstep : ∀ k < n, ∀ d' : OpenPartialHomeomorph X E,
      d'.source = univ → ∀ U : Set X, IsOpen U → P k ⊆ U →
      (∀ i, LocallyPiecewiseAffineOn (d' ∘ (c i).symm)
        ((c i).target ∩ (c i).symm ⁻¹' U)) →
      ∃ (F : X ≃ₜ X) (V S : Set X),
        IsOpen V ∧ IsCompact S ∧ S ⊆ W ∧ EqOn F id Sᶜ ∧ P (k + 1) ⊆ V ∧
        ∀ i, LocallyPiecewiseAffineOn ((d' ∘ F) ∘ (c i).symm)
          ((c i).target ∩ (c i).symm ⁻¹' V)) :
    ∃ (G : X ≃ₜ X) (U S : Set X),
      IsOpen U ∧ IsCompact S ∧ S ⊆ W ∧ EqOn G id Sᶜ ∧ P n ⊆ U ∧
      ∀ i, LocallyPiecewiseAffineOn ((d ∘ G) ∘ (c i).symm)
        ((c i).target ∩ (c i).symm ⁻¹' U) := by
  have hrec : ∀ k, k ≤ n →
      ∃ (G : X ≃ₜ X) (U S : Set X),
        IsOpen U ∧ IsCompact S ∧ S ⊆ W ∧ EqOn G id Sᶜ ∧ P k ⊆ U ∧
        ∀ i, LocallyPiecewiseAffineOn ((d ∘ G) ∘ (c i).symm)
          ((c i).target ∩ (c i).symm ⁻¹' U) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Homeomorph.refl X, ∅, ∅, isOpen_empty, isCompact_empty,
        empty_subset W, fun _ _ => rfl, hP0.subset, ?_⟩
      intro i x hx
      exact False.elim hx.2
    | succ k ih =>
      intro hk
      obtain ⟨G, U, S, hU, hS, hSW, hG, hPU, hPL⟩ := ih (Nat.le_of_succ_le hk)
      let d' := G.toOpenPartialHomeomorph.trans d
      have hd' : d'.source = univ := by
        change univ ∩ G ⁻¹' d.source = univ
        rw [hd, preimage_univ, inter_self]
      have hPL' (i : ι) : LocallyPiecewiseAffineOn (d' ∘ (c i).symm)
          ((c i).target ∩ (c i).symm ⁻¹' U) := hPL i
      obtain ⟨F, V, T, hV, hT, hTW, hF, hPV, hPLnew⟩ :=
        hstep k (Nat.lt_of_succ_le hk) d' hd' U hU hPU hPL'
      refine ⟨F.trans G, V, S ∪ T, hV, hS.union hT,
        union_subset hSW hTW, ?_, hPV, ?_⟩
      · intro x hx
        have hxS : x ∉ S := fun h => hx (Or.inl h)
        have hxT : x ∉ T := fun h => hx (Or.inr h)
        change G (F x) = x
        exact (congrArg G (hF hxT)).trans (hG hxS)
      · exact hPLnew
  exact hrec n le_rfl

end PoincareConjecture.M76
