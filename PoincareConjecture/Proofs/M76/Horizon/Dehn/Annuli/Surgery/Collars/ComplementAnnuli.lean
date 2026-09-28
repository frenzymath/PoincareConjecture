import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Collars.SourceAlternatives
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.EssentialRegions



set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem oriented_collar_interior {A : Set P2} {l r : ℝ}
    (B : OrientedPolygonCollar l r A) :
    interior A = B.outer.inside \ closure B.inner.inside := by
  conv_lhs => rw [B.carrier]
  rw [sdiff_eq, interior_inter, interior_compl,
    B.outer.interior_closure_inside B.outer_simplicial B.outer_injective]
  rfl




theorem exists_essential_collar_complement_annuli
    {A : Set P2} {l r L d : ℝ} (B : OrientedPolygonCollar l r A)
    (hA : A ⊆ {p : P2 | -d < depth L p ∧ depth L p < d})
    (henclosing : annulusSquare L d ⊆ B.outer.inside)
    (hd : 0 < d) (hwidth : 2 * d < L) :
    ∃ (outer : Ann ≃ₜ (annulusSquare L (-d) \ B.outer.inside : Set P2))
      (inner : Ann ≃ₜ (closure B.inner.inside \ interior (annulusSquare L d) : Set P2)),
      outer.IsFinitePL ∧ inner.IsFinitePL ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ depth L (outer z : P2) = -d) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ (outer z : P2) ∈ B.outer.boundary ℝ) ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ (inner z : P2) ∈ B.inner.boundary ℝ) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ depth L (inner z : P2) = d) ∧
      (annulusSquare L (-d) \ B.outer.inside) ∪
        (closure B.inner.inside \ interior (annulusSquare L d)) =
          squareAnnulus L d \ interior A ∧
      Disjoint (annulusSquare L (-d) \ B.outer.inside)
        (closure B.inner.inside \ interior (annulusSquare L d)) := by
  have hb := oriented_collar_boundary_subsets B
  have hinner := (oriented_collar_enclosing_iff B hA).mp henclosing
  obtain ⟨outer, _, ho, _, ho0, ho1, _, _, hu, _⟩ :=
    exists_enclosing_polygon_complementary_annuli B.outer B.outer_simplicial
      B.outer_injective hd hwidth (fun x hx ↦ hA (hb.1 hx)) henclosing
  obtain ⟨_, inner, _, hi, _, _, hi0, hi1, hv, _⟩ :=
    exists_enclosing_polygon_complementary_annuli B.inner B.inner_simplicial
      B.inner_injective hd hwidth (fun x hx ↦ hA (hb.2 hx)) hinner
  refine ⟨outer, inner, ho, hi, ho0, ho1, hi0, hi1, ?_, ?_⟩
  · rw [oriented_collar_interior B]
    ext x
    constructor
    · rintro (hx | hx)
      · exact ⟨hu.subset (Or.inl hx), fun hh ↦ hx.2 hh.1⟩
      · exact ⟨hv.subset (Or.inr hx), fun hh ↦ hh.2 hx.1⟩
    · rintro ⟨hx, hnot⟩
      have hh := mem_squareAnnulus_iff_depth.mp hx
      by_cases hp : x ∈ B.outer.inside
      · exact Or.inr ⟨by by_contra hn; exact hnot ⟨hp, hn⟩,
          fun h ↦ (not_lt_of_ge hh.2) ((mem_interior_annulusSquare_iff L d x).mp h)⟩
      · exact Or.inl ⟨(mem_annulusSquare_iff L (-d) x).mpr hh.1, hp⟩
  · exact disjoint_left.mpr fun x hx hy ↦ hx.2 (B.nested hy.1)

end PoincareConjecture.M76.Dehn.Annuli
