import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CollarComponents
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.NestedSourceGeometry

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem nested_collar_component_retention_on_source
    {A₀ A₁ U S : Set P2} {l₀ r₀ l₁ r₁ : ℝ}
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hU : IsPreconnected U) (hUS : U ⊆ S)
    (havoid₀ : Disjoint U A₀) (havoid₁ : Disjoint U A₁) :
    U ⊆ closure B₁.inner.inside ∪ (S \ B₀.outer.inside) ∨
      Disjoint U (closure B₁.inner.inside ∪ (S \ B₀.outer.inside)) := by
  rcases oriented_collar_component_sides B₁ hU havoid₁ with hi | ho₁
  · exact Or.inl (fun x hx ↦ Or.inl (subset_closure (hi hx)))
  rcases oriented_collar_component_sides B₀ hU havoid₀ with hi₀ | ho₀
  · apply Or.inr
    apply disjoint_left.mpr
    rintro x hx (hi | ho)
    · exact ho₁ hx (subset_closure (B₁.nested hi))
    · exact ho.2 (B₀.nested (subset_closure (hi₀ hx)))
  · exact Or.inl (fun x hx ↦ Or.inr ⟨hUS hx, fun h ↦ ho₀ hx (subset_closure h)⟩)

theorem SourceCircleDecomposition.nested_planar_component_retention
    {X : Type*} {f : P2 → X} {S A₀ A₁ : Set P2} {l₀ r₀ l₁ r₁ : ℝ}
    (M : SourceCircleDecomposition f S) (i k : M.Index)
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hnested : closure B₁.outer.inside ⊆ B₀.inner.inside)
    (hmiddle₀ : (fun p : squareAnnulus l₀ r₀ ↦ (B₀.chart p : P2)) ''
      {p | depth l₀ p = 0} = M.pieces i)
    (hmiddle₁ : (fun p : squareAnnulus l₁ r₁ ↦ (B₁.chart p : P2)) ''
      {p | depth l₁ p = 0} = M.pieces k)
    (htrace₀ : ∀ x ∈ A₀, x ∈ doubleLocusOn f S → x ∈ M.pieces i)
    (htrace₁ : ∀ x ∈ A₁, x ∈ doubleLocusOn f S → x ∈ M.pieces k) :
    let K := closure B₁.inner.inside ∪ (S \ B₀.outer.inside)
    (∀ a, M.pieces a ⊆ K ∨ Disjoint (M.pieces a) K) ∧
      Disjoint (M.pieces i ∪ M.pieces k) K ∧
      ¬ M.pieces i ⊆ K ∧ ¬ M.pieces k ⊆ K := by
  dsimp only
  let K := closure B₁.inner.inside ∪ (S \ B₀.outer.inside)
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
    rintro x hx (hi | ho)
    · exact (hs₀ hx).2 (subset_closure (hnested (subset_closure (B₁.nested hi))))
    · exact ho.2 (hs₀ hx).1
  have hk : Disjoint (M.pieces k) K := by
    apply disjoint_left.mpr
    rintro x hx (hi | ho)
    · exact (hs₁ hx).2 hi
    · exact ho.2 (B₀.nested (subset_closure (hnested (subset_closure (hs₁ hx).1))))
  refine ⟨?_, hi.union_left hk, ?_, ?_⟩
  · intro a
    by_cases hai : a = i
    · subst a
      exact Or.inr hi
    by_cases hak : a = k
    · subst a
      exact Or.inr hk
    exact nested_collar_component_retention_on_source B₀ B₁
      (M.pieces_isConnected a).isPreconnected (M.piece_subset_source a)
      (M.component_avoids_collar i a hai htrace₀) (M.component_avoids_collar k a hak htrace₁)
  · intro hh
    obtain ⟨x, hx⟩ := (M.pieces_isConnected i).nonempty
    exact disjoint_left.mp hi hx (hh hx)
  · intro hh
    obtain ⟨x, hx⟩ := (M.pieces_isConnected k).nonempty
    exact disjoint_left.mp hk hx (hh hx)

theorem nested_planar_retained_closed_band
    {A₀ A₁ S G : Set P2} {l₀ r₀ l₁ r₁ : ℝ}
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (htrace₀ : ∀ p : squareAnnulus l₀ r₀, (B₀.chart p : P2) ∈ G → depth l₀ p = 0)
    (htrace₁ : ∀ p : squareAnnulus l₁ r₁, (B₁.chart p : P2) ∈ G → depth l₁ p = 0) :
    let K := closure B₁.inner.inside ∪ (S \ B₀.outer.inside)
    let B := closure B₀.outer.inside \ B₁.inner.inside
    IsClosed B ∧ S ⊆ K ∪ B ∧ Disjoint (K ∩ G) B := by
  dsimp only
  have hseam₀ := oriented_collar_seams_avoid_of_middle_trace B₀ hr₀ htrace₀
  have hseam₁ := oriented_collar_seams_avoid_of_middle_trace B₁ hr₁ htrace₁
  have ho : B₀.outer.boundary ℝ = closure B₀.outer.inside \ B₀.outer.inside := by
    rw [← B₀.outer.frontier_inside B₀.outer_simplicial B₀.outer_injective, frontier,
      (B₀.outer.isOpen_inside B₀.outer_simplicial B₀.outer_injective).interior_eq]
  have hi : B₁.inner.boundary ℝ = closure B₁.inner.inside \ B₁.inner.inside := by
    rw [← B₁.inner.frontier_inside B₁.inner_simplicial B₁.inner_injective, frontier,
      (B₁.inner.isOpen_inside B₁.inner_simplicial B₁.inner_injective).interior_eq]
  refine ⟨isClosed_closure.sdiff
    (B₁.inner.isOpen_inside B₁.inner_simplicial B₁.inner_injective), ?_, ?_⟩
  · intro x hx
    by_cases hxo : x ∈ B₀.outer.inside
    · by_cases hxi : x ∈ B₁.inner.inside
      · exact Or.inl (Or.inl (subset_closure hxi))
      · exact Or.inr ⟨subset_closure hxo, hxi⟩
    · exact Or.inl (Or.inr ⟨hx, hxo⟩)
  · apply disjoint_left.mpr
    rintro x ⟨(hx | hx), hg⟩ hb
    · exact disjoint_left.mp hseam₁ hg (Or.inr (hi.symm.subset ⟨hx, hb.2⟩))
    · exact disjoint_left.mp hseam₀ hg (Or.inl (ho.symm.subset ⟨hb.1, hx.2⟩))

end PoincareConjecture.M76.Dehn.Annuli
