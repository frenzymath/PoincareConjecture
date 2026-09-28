import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Collars.ComplementAnnuli

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem nested_collar_retained_component_location
    {A₀ A₁ U : Set P2} {l₀ r₀ l₁ r₁ L d : ℝ}
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hU : IsPreconnected U) (hUS : U ⊆ squareAnnulus L d)
    (havoid₀ : Disjoint U A₀) (havoid₁ : Disjoint U A₁) :
    U ⊆ annulusSquare L (-d) \ B₀.outer.inside ∨
    U ⊆ closure B₀.inner.inside \ B₁.outer.inside ∨
    U ⊆ closure B₁.inner.inside \ interior (annulusSquare L d) := by
  rcases oriented_collar_component_sides B₁ hU havoid₁ with hi₁ | ho₁
  · refine Or.inr (Or.inr fun x hx ↦ ⟨subset_closure (hi₁ hx), ?_⟩)
    intro h
    exact (not_lt_of_ge (mem_squareAnnulus_iff_depth.mp (hUS hx)).2)
      ((mem_interior_annulusSquare_iff L d x).mp h)
  rcases oriented_collar_component_sides B₀ hU havoid₀ with hi₀ | ho₀
  · exact Or.inr (Or.inl fun x hx ↦ ⟨subset_closure (hi₀ hx),
      fun h ↦ ho₁ hx (subset_closure h)⟩)
  · exact Or.inl fun x hx ↦ ⟨(mem_annulusSquare_iff L (-d) x).mpr
      (mem_squareAnnulus_iff_depth.mp (hUS hx)).1, fun h ↦ ho₀ hx (subset_closure h)⟩

theorem exists_nested_essential_collars_retained_annuli
    {A₀ A₁ : Set P2} {l₀ r₀ l₁ r₁ L d : ℝ}
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hA₀ : A₀ ⊆ {p : P2 | -d < depth L p ∧ depth L p < d})
    (hA₁ : A₁ ⊆ {p : P2 | -d < depth L p ∧ depth L p < d})
    (henclosing : annulusSquare L d ⊆ B₁.outer.inside)
    (hnested : closure B₁.outer.inside ⊆ B₀.inner.inside)
    (hd : 0 < d) (hwidth : 2 * d < L) :
    ∃ (outer : Ann ≃ₜ (annulusSquare L (-d) \ B₀.outer.inside : Set P2))
      (middle : Ann ≃ₜ (closure B₀.inner.inside \ B₁.outer.inside : Set P2))
      (inner : Ann ≃ₜ (closure B₁.inner.inside \ interior (annulusSquare L d) : Set P2)),
      outer.IsFinitePL ∧ middle.IsFinitePL ∧ inner.IsFinitePL ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ depth L (outer z : P2) = -d) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ (outer z : P2) ∈ B₀.outer.boundary ℝ) ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ (middle z : P2) ∈ B₀.inner.boundary ℝ) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ (middle z : P2) ∈ B₁.outer.boundary ℝ) ∧
      (∀ z : Ann, depth 8 (z : P2) = -1 ↔ (inner z : P2) ∈ B₁.inner.boundary ℝ) ∧
      (∀ z : Ann, depth 8 (z : P2) = 1 ↔ depth L (inner z : P2) = d) ∧
      ((annulusSquare L (-d) \ B₀.outer.inside) ∪
        (closure B₀.inner.inside \ B₁.outer.inside)) ∪
        (closure B₁.inner.inside \ interior (annulusSquare L d)) =
          squareAnnulus L d \ (interior A₀ ∪ interior A₁) ∧
      Disjoint (annulusSquare L (-d) \ B₀.outer.inside)
        (closure B₀.inner.inside \ B₁.outer.inside) ∧
      Disjoint (annulusSquare L (-d) \ B₀.outer.inside)
        (closure B₁.inner.inside \ interior (annulusSquare L d)) ∧
      Disjoint (closure B₀.inner.inside \ B₁.outer.inside)
        (closure B₁.inner.inside \ interior (annulusSquare L d)) := by
  have h₀ : annulusSquare L d ⊆ B₀.outer.inside :=
    henclosing.trans (subset_closure.trans (hnested.trans (subset_closure.trans B₀.nested)))
  obtain ⟨outer, _, ho, _, ho0, ho1, _, _, hu₀, _⟩ :=
    exists_essential_collar_complement_annuli B₀ hA₀ h₀ hd hwidth
  obtain ⟨_, inner, _, hi, _, _, hi0, hi1, hu₁, _⟩ :=
    exists_essential_collar_complement_annuli B₁ hA₁ henclosing hd hwidth
  have hp₁ : IsFinitePLBallPair P2 (closure B₁.outer.inside)
      (frontier (closure B₁.outer.inside)) := by
    rw [B₁.outer.frontier_closure_inside B₁.outer_simplicial B₁.outer_injective]
    exact B₁.outer.isFinitePLBallPair_closed_inside B₁.outer_simplicial B₁.outer_injective
  have hi₀ : IsFinitePLBallPair P2 (closure B₀.inner.inside)
      (frontier (closure B₀.inner.inside)) := by
    rw [B₀.inner.frontier_closure_inside B₀.inner_simplicial B₀.inner_injective]
    exact B₀.inner.isFinitePLBallPair_closed_inside B₀.inner_simplicial B₀.inner_injective
  have hn : closure B₁.outer.inside ⊆ interior (closure B₀.inner.inside) := by
    rwa [B₀.inner.interior_closure_inside B₀.inner_simplicial B₀.inner_injective]
  have hmdata := exists_square_annulus_nested_disks hp₁ hi₀ hn
    (L := 8) (d := 1) (by norm_num) (by norm_num)
  rw [B₁.outer.interior_closure_inside B₁.outer_simplicial B₁.outer_injective] at hmdata
  obtain ⟨middle, hm, hm0, hm1⟩ := hmdata
  have hmiddle : closure B₀.inner.inside \ B₁.outer.inside ⊆ squareAnnulus L d := by
    intro x hx
    have houter := (oriented_collar_disk_or_enclosing B₀ hA₀).2.2.1
    apply mem_squareAnnulus_iff_depth.mpr
    exact ⟨((mem_interior_annulusSquare_iff L (-d) x).mp
      (houter (subset_closure (B₀.nested hx.1)))).le,
      (lt_of_not_ge fun h ↦ hx.2 (henclosing ((mem_annulusSquare_iff L d x).mpr h))).le⟩
  refine ⟨outer, middle, inner, ho, hm, hi, ho0, ho1, ?_, ?_, hi0, hi1, ?_, ?_, ?_, ?_⟩
  · intro z
    simpa only [B₀.inner.frontier_closure_inside B₀.inner_simplicial B₀.inner_injective] using hm0 z
  · intro z
    simpa only [B₁.outer.frontier_closure_inside B₁.outer_simplicial B₁.outer_injective] using hm1 z
  · rw [oriented_collar_interior B₀] at hu₀
    rw [oriented_collar_interior B₁] at hu₁
    rw [oriented_collar_interior B₀, oriented_collar_interior B₁]
    ext x
    constructor
    · rintro ((hx | hx) | hx)
      · refine ⟨(hu₀.subset (Or.inl hx)).1, ?_⟩
        rintro (hh | hh)
        · exact hx.2 hh.1
        · exact hx.2 (B₀.nested (subset_closure (hnested (subset_closure hh.1))))
      · refine ⟨hmiddle hx, ?_⟩
        rintro (hh | hh)
        · exact hh.2 hx.1
        · exact hx.2 hh.1
      · refine ⟨(hu₁.subset (Or.inr hx)).1, ?_⟩
        rintro (hh | hh)
        · exact hh.2 (subset_closure (hnested (subset_closure (B₁.nested hx.1))))
        · exact hh.2 hx.1
    · rintro ⟨hx, hn⟩
      have hh := mem_squareAnnulus_iff_depth.mp hx
      by_cases hp₀ : x ∈ B₀.outer.inside
      · have hx₀ : x ∈ closure B₀.inner.inside := by
          by_contra h
          exact hn (Or.inl ⟨hp₀, h⟩)
        by_cases hp₁ : x ∈ B₁.outer.inside
        · refine Or.inr ⟨?_, fun h ↦ (not_lt_of_ge hh.2)
            ((mem_interior_annulusSquare_iff L d x).mp h)⟩
          by_contra h
          exact hn (Or.inr ⟨hp₁, h⟩)
        · exact Or.inl (Or.inr ⟨hx₀, hp₁⟩)
      · exact Or.inl (Or.inl ⟨(mem_annulusSquare_iff L (-d) x).mpr hh.1, hp₀⟩)
  · exact disjoint_left.mpr fun x hx hy ↦ hx.2 (B₀.nested hy.1)
  · exact disjoint_left.mpr fun x hx hy ↦ hx.2
      (B₀.nested (subset_closure (hnested (subset_closure (B₁.nested hy.1)))))
  · exact disjoint_left.mpr fun x hx hy ↦ hx.2 (B₁.nested hy.1)

end PoincareConjecture.M76.Dehn.Annuli
