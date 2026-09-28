import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.NestedSource



set_option autoImplicit false
open Set Geometry
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem nested_collar_retained_contacts
    {S A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (hP : closure B₀.outer.inside ⊆ S)
    (hnest : closure B₁.outer.inside ⊆ B₀.inner.inside) :
    (A₀ ∪ A₁) ∩ (S \ B₀.outer.inside) = B₀.outer.boundary ℝ ∧
      (A₀ ∪ A₁) ∩ closure B₁.inner.inside = B₁.inner.boundary ℝ ∧
      Disjoint A₀ A₁ := by
  have h10 : A₁ ⊆ B₀.inner.inside := fun _ hx ↦ hnest (B₁.carrier.subset hx).1
  have hPfront := B₀.outer.frontier_inside B₀.outer_simplicial B₀.outer_injective
  have hIfront := B₁.inner.frontier_inside B₁.inner_simplicial B₁.inner_injective
  have hPI := B₀.outer.isOpen_inside B₀.outer_simplicial B₀.outer_injective
  have hII := B₁.inner.isOpen_inside B₁.inner_simplicial B₁.inner_injective
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hx | hx, hxS, hxP⟩
      · rw [← hPfront, frontier, hPI.interior_eq]
        exact ⟨(B₀.carrier.subset hx).1, hxP⟩
      · exact (hxP (B₀.nested (subset_closure (h10 hx)))).elim
    · intro hx
      have hxF : x ∈ closure B₀.outer.inside ∧ x ∉ B₀.outer.inside := by
        simpa only [frontier, hPI.interior_eq, mem_sdiff] using hPfront.symm.subset hx
      exact ⟨Or.inl ((oriented_collar_boundary_subsets B₀).1 hx), hP hxF.1, hxF.2⟩
  · ext x
    constructor
    · rintro ⟨hx | hx, hxI⟩
      · exact ((B₀.carrier.subset hx).2
          (hnest (subset_closure (B₁.nested hxI)))).elim
      · rw [← hIfront, frontier, hII.interior_eq]
        exact ⟨hxI, (B₁.carrier.subset hx).2⟩
    · intro hx
      exact ⟨Or.inr ((oriented_collar_boundary_subsets B₁).2 hx),
        (B₁.inner.isFinitePLBallPair_closed_inside B₁.inner_simplicial B₁.inner_injective).1 hx⟩
  · exact disjoint_left.mpr fun x hx₀ hx₁ ↦ (B₀.carrier.subset hx₀).2 (h10 hx₁)

end PoincareConjecture.M76.Dehn.Annuli
