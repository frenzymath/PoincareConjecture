import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CollarComponents

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem disjoint_collar_component_retained_piece_on_source
    {A₀ A₁ U S : Set P2} {l₀ r₀ l₁ r₁ : ℝ}
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hU : IsPreconnected U) (hUS : U ⊆ S)
    (havoid₀ : Disjoint U A₀) (havoid₁ : Disjoint U A₁) :
    U ⊆ B₀.inner.inside ∨ U ⊆ B₁.inner.inside ∨
      U ⊆ S \ (closure B₀.outer.inside ∪ closure B₁.outer.inside) := by
  rcases oriented_collar_component_sides B₀ hU havoid₀ with hi | ho₀
  · exact Or.inl hi
  rcases oriented_collar_component_sides B₁ hU havoid₁ with hi | ho₁
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr (fun x hx ↦ ⟨hUS hx, fun h ↦ h.elim (ho₀ hx) (ho₁ hx)⟩))

theorem SourceCircleDecomposition.disjoint_planar_component_retention
    {X : Type*} {f : P2 → X} {S A₀ A₁ : Set P2} {l₀ r₀ l₁ r₁ : ℝ}
    (M : SourceCircleDecomposition f S) (i k : M.Index)
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hdis : Disjoint (closure B₀.outer.inside) (closure B₁.outer.inside))
    (hmiddle₀ : (fun p : squareAnnulus l₀ r₀ ↦ (B₀.chart p : P2)) ''
      {p | depth l₀ p = 0} = M.pieces i)
    (hmiddle₁ : (fun p : squareAnnulus l₁ r₁ ↦ (B₁.chart p : P2)) ''
      {p | depth l₁ p = 0} = M.pieces k)
    (htrace₀ : ∀ x ∈ A₀, x ∈ doubleLocusOn f S → x ∈ M.pieces i)
    (htrace₁ : ∀ x ∈ A₁, x ∈ doubleLocusOn f S → x ∈ M.pieces k) :
    let K := (closure B₀.inner.inside ∪ closure B₁.inner.inside) ∪
      (S \ (B₀.outer.inside ∪ B₁.outer.inside))
    (∀ a, a ≠ i → a ≠ k → M.pieces a ⊆ K) ∧
      (∀ a, M.pieces a ⊆ K ∨ Disjoint (M.pieces a) K) ∧
      Disjoint (M.pieces i ∪ M.pieces k) K ∧
      ¬ M.pieces i ⊆ K ∧ ¬ M.pieces k ⊆ K := by
  dsimp only
  let K := (closure B₀.inner.inside ∪ closure B₁.inner.inside) ∪
    (S \ (B₀.outer.inside ∪ B₁.outer.inside))
  have hs₀ : M.pieces i ⊆ B₀.outer.inside \ closure B₀.inner.inside := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hmiddle₀.symm.subset hx
    exact oriented_collar_middle_separated B₀ hr₀ p hp
  have hs₁ : M.pieces k ⊆ B₁.outer.inside \ closure B₁.inner.inside := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hmiddle₁.symm.subset hx
    exact oriented_collar_middle_separated B₁ hr₁ p hp
  have hi : Disjoint (M.pieces i) K := by
    apply disjoint_left.mpr
    rintro x hx ((hi | hi) | ho)
    · exact (hs₀ hx).2 hi
    · exact disjoint_left.mp hdis (subset_closure (hs₀ hx).1)
        (subset_closure (B₁.nested hi))
    · exact ho.2 (Or.inl (hs₀ hx).1)
  have hk : Disjoint (M.pieces k) K := by
    apply disjoint_left.mpr
    rintro x hx ((hi | hi) | ho)
    · exact disjoint_left.mp hdis (subset_closure (B₀.nested hi))
        (subset_closure (hs₁ hx).1)
    · exact (hs₁ hx).2 hi
    · exact ho.2 (Or.inr (hs₁ hx).1)
  have hothers : ∀ a, a ≠ i → a ≠ k → M.pieces a ⊆ K := by
    intro a hai hak
    rcases disjoint_collar_component_retained_piece_on_source B₀ B₁
      (M.pieces_isConnected a).isPreconnected (M.piece_subset_source a)
      (M.component_avoids_collar i a hai htrace₀)
      (M.component_avoids_collar k a hak htrace₁) with hi₀ | hi₁ | ho
    · exact fun x hx ↦ Or.inl (Or.inl (subset_closure (hi₀ hx)))
    · exact fun x hx ↦ Or.inl (Or.inr (subset_closure (hi₁ hx)))
    · intro x hx
      exact Or.inr ⟨(ho hx).1, fun h ↦ (ho hx).2
        (h.elim (fun h ↦ Or.inl (subset_closure h)) (fun h ↦ Or.inr (subset_closure h)))⟩
  refine ⟨hothers, ?_, hi.union_left hk, ?_, ?_⟩
  · intro a
    by_cases hai : a = i
    · subst a
      exact Or.inr hi
    by_cases hak : a = k
    · subst a
      exact Or.inr hk
    exact Or.inl (hothers a hai hak)
  · intro hh
    obtain ⟨x, hx⟩ := (M.pieces_isConnected i).nonempty
    exact disjoint_left.mp hi hx (hh hx)
  · intro hh
    obtain ⟨x, hx⟩ := (M.pieces_isConnected k).nonempty
    exact disjoint_left.mp hk hx (hh hx)

end PoincareConjecture.M76.Dehn.Annuli
