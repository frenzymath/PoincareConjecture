import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Collars.NestedRetention
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.SelectedComponent

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)



theorem oriented_collar_middle_separated
    {A : Set P2} {l r : ℝ} (B : OrientedPolygonCollar l r A) (hr : 0 < r)
    (p : squareAnnulus l r) (hp : depth l p = 0) :
    (B.chart p : P2) ∈ B.outer.inside \ closure B.inner.inside := by
  have hx := B.carrier.subset (B.chart p).property
  have ho : B.outer.boundary ℝ = closure B.outer.inside \ B.outer.inside := by
    rw [← B.outer.frontier_inside B.outer_simplicial B.outer_injective, frontier,
      (B.outer.isOpen_inside B.outer_simplicial B.outer_injective).interior_eq]
  have hi : B.inner.boundary ℝ = closure B.inner.inside \ B.inner.inside := by
    rw [← B.inner.frontier_inside B.inner_simplicial B.inner_injective, frontier,
      (B.inner.isOpen_inside B.inner_simplicial B.inner_injective).interior_eq]
  constructor
  · by_contra hh
    have hz := (B.outer_depth p).mp (ho.symm.subset ⟨hx.1, hh⟩)
    linarith
  · intro hh
    have hz := (B.inner_depth p).mp (hi.symm.subset ⟨hh, hx.2⟩)
    linarith


theorem SourceCircleDecomposition.component_avoids_collar
    {X : Type*} {f : P2 → X} {S A : Set P2} (M : SourceCircleDecomposition f S)
    (i k : M.Index) (hki : k ≠ i)
    (htrace : ∀ x ∈ A, x ∈ doubleLocusOn f S → x ∈ M.pieces i) :
    Disjoint (M.pieces k) A := by
  apply disjoint_left.mpr
  intro x hx hA
  exact disjoint_left.mp (M.disjoint hki) hx (htrace x hA (M.piece_subset_double k hx))



theorem SourceCircleDecomposition.nested_essential_component_retention
    {X : Type*} {f : P2 → X} {A₀ A₁ : Set P2} {l₀ r₀ l₁ r₁ L d : ℝ}
    (M : SourceCircleDecomposition f (squareAnnulus L d)) (i k : M.Index)
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hnested : closure B₁.outer.inside ⊆ B₀.inner.inside)
    (hmiddle₀ : (fun p : squareAnnulus l₀ r₀ ↦ (B₀.chart p : P2)) ''
      {p | depth l₀ p = 0} = M.pieces i)
    (hmiddle₁ : (fun p : squareAnnulus l₁ r₁ ↦ (B₁.chart p : P2)) ''
      {p | depth l₁ p = 0} = M.pieces k)
    (htrace₀ : ∀ x ∈ A₀, x ∈ doubleLocusOn f (squareAnnulus L d) → x ∈ M.pieces i)
    (htrace₁ : ∀ x ∈ A₁, x ∈ doubleLocusOn f (squareAnnulus L d) → x ∈ M.pieces k) :
    let O := annulusSquare L (-d) \ B₀.outer.inside
    let I := closure B₁.inner.inside \ interior (annulusSquare L d)
    let K := O ∪ I
    (∀ a, M.pieces a ⊆ K ∨ Disjoint (M.pieces a) K) ∧
      Disjoint (M.pieces i ∪ M.pieces k) K ∧
      ¬ M.pieces i ⊆ K ∧ ¬ M.pieces k ⊆ K := by
  dsimp only
  let O := annulusSquare L (-d) \ B₀.outer.inside
  let I := closure B₁.inner.inside \ interior (annulusSquare L d)
  let K := O ∪ I
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
    rintro x hx (ho | hi)
    · exact ho.2 (hs₀ hx).1
    · exact (hs₀ hx).2 (subset_closure (hnested (subset_closure (B₁.nested hi.1))))
  have hk : Disjoint (M.pieces k) K := by
    apply disjoint_left.mpr
    rintro x hx (ho | hi)
    · exact ho.2 (B₀.nested (subset_closure (hnested (subset_closure (hs₁ hx).1))))
    · exact (hs₁ hx).2 hi.1
  have hmid : Disjoint (closure B₀.inner.inside \ B₁.outer.inside) K := by
    apply disjoint_left.mpr
    rintro x hx (ho | hi)
    · exact ho.2 (B₀.nested hx.1)
    · exact hx.2 (B₁.nested hi.1)
  refine ⟨?_, hi.union_left hk, ?_, ?_⟩
  · intro a
    by_cases hai : a = i
    · subst a
      exact Or.inr hi
    by_cases hak : a = k
    · subst a
      exact Or.inr hk
    have ha₀ := M.component_avoids_collar i a hai htrace₀
    have ha₁ := M.component_avoids_collar k a hak htrace₁
    rcases nested_collar_retained_component_location B₀ B₁
      (M.pieces_isConnected a).isPreconnected (M.piece_subset_source a) ha₀ ha₁ with
      ho | hm | hi'
    · exact Or.inl (ho.trans subset_union_left)
    · exact Or.inr (hmid.mono_left hm)
    · exact Or.inl (hi'.trans subset_union_right)
  · intro hh
    obtain ⟨x, hx⟩ := (M.pieces_isConnected i).nonempty
    exact disjoint_left.mp hi hx (hh hx)
  · intro hh
    obtain ⟨x, hx⟩ := (M.pieces_isConnected k).nonempty
    exact disjoint_left.mp hk hx (hh hx)

end PoincareConjecture.M76.Dehn.Annuli
