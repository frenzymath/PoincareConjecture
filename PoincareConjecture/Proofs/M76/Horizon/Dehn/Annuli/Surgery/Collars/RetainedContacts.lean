import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Collars.NestedRetention



set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem oriented_collar_retained_contacts {A : Set P2} {l r L d : ℝ}
    (B : OrientedPolygonCollar l r A)
    (hA : A ⊆ {p : P2 | -d < depth L p ∧ depth L p < d}) :
    A ∩ (annulusSquare L (-d) \ B.outer.inside) = B.outer.boundary ℝ ∧
      A ∩ (closure B.inner.inside \ interior (annulusSquare L d)) = B.inner.boundary ℝ := by
  have hPo : B.outer.boundary ℝ = closure B.outer.inside \ B.outer.inside := by
    rw [← B.outer.frontier_inside B.outer_simplicial B.outer_injective, frontier,
      (B.outer.isOpen_inside B.outer_simplicial B.outer_injective).interior_eq]
  have hPi : B.inner.boundary ℝ = closure B.inner.inside \ B.inner.inside := by
    rw [← B.inner.frontier_inside B.inner_simplicial B.inner_injective, frontier,
      (B.inner.isOpen_inside B.inner_simplicial B.inner_injective).interior_eq]
  have hb := oriented_collar_boundary_subsets B
  constructor
  · ext x
    constructor
    · rintro ⟨hx, ho⟩
      exact hPo.symm.subset ⟨(B.carrier.subset hx).1, ho.2⟩
    · intro hx
      exact ⟨hb.1 hx, (mem_annulusSquare_iff L (-d) x).mpr (hA (hb.1 hx)).1.le,
        (hPo.subset hx).2⟩
  · ext x
    constructor
    · rintro ⟨hx, hi⟩
      exact hPi.symm.subset ⟨hi.1, (B.carrier.subset hx).2⟩
    · intro hx
      refine ⟨hb.2 hx, (hPi.subset hx).1, ?_⟩
      intro hi
      have h := (mem_interior_annulusSquare_iff L d x).mp hi
      linarith [(hA (hb.2 hx)).2]

theorem essential_collar_retained_source_bounds {A : Set P2} {l r L d : ℝ}
    (B : OrientedPolygonCollar l r A)
    (hA : A ⊆ {p : P2 | -d < depth L p ∧ depth L p < d})
    (henclosing : annulusSquare L d ⊆ B.outer.inside) :
    (∀ x ∈ annulusSquare L (-d) \ B.outer.inside,
      x ∈ squareAnnulus L d ∧ depth L x < d) ∧
      ∀ x ∈ closure B.inner.inside \ interior (annulusSquare L d),
        x ∈ squareAnnulus L d ∧ -d < depth L x := by
  have houter := (oriented_collar_disk_or_enclosing B hA).2.2.1
  constructor
  · intro x hx
    have hlo := (mem_annulusSquare_iff L (-d) x).mp hx.1
    have hhi : depth L x < d := lt_of_not_ge fun h ↦
      hx.2 (henclosing ((mem_annulusSquare_iff L d x).mpr h))
    exact ⟨mem_squareAnnulus_iff_depth.mpr ⟨hlo, hhi.le⟩, hhi⟩
  · intro x hx
    have hlo := (mem_interior_annulusSquare_iff L (-d) x).mp
      (houter (subset_closure (B.nested hx.1)))
    have hhi : depth L x ≤ d := le_of_not_gt fun h ↦
      hx.2 ((mem_interior_annulusSquare_iff L d x).mpr h)
    exact ⟨mem_squareAnnulus_iff_depth.mpr ⟨hlo.le, hhi⟩, hlo⟩

theorem nested_collars_retained_union_contacts
    {A₀ A₁ : Set P2} {l₀ r₀ l₁ r₁ L d : ℝ}
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hA₀ : A₀ ⊆ {p : P2 | -d < depth L p ∧ depth L p < d})
    (hA₁ : A₁ ⊆ {p : P2 | -d < depth L p ∧ depth L p < d})
    (hnested : closure B₁.outer.inside ⊆ B₀.inner.inside) :
    (A₀ ∪ A₁) ∩ (annulusSquare L (-d) \ B₀.outer.inside) = B₀.outer.boundary ℝ ∧
      (A₀ ∪ A₁) ∩ (closure B₁.inner.inside \ interior (annulusSquare L d)) =
        B₁.inner.boundary ℝ := by
  have hO := (oriented_collar_retained_contacts B₀ hA₀).1
  have hI := (oriented_collar_retained_contacts B₁ hA₁).2
  constructor
  · ext x
    constructor
    · rintro ⟨(hx | hx), ho⟩
      · exact hO.subset ⟨hx, ho⟩
      · exact (ho.2 (B₀.nested (subset_closure (hnested (B₁.carrier.subset hx).1)))).elim
    · intro hx
      exact ⟨Or.inl (hO.symm.subset hx).1, (hO.symm.subset hx).2⟩
  · ext x
    constructor
    · rintro ⟨(hx | hx), hi⟩
      · exact ((B₀.carrier.subset hx).2
          (hnested (subset_closure (B₁.nested hi.1)))).elim
      · exact hI.subset ⟨hx, hi⟩
    · intro hx
      exact ⟨Or.inr (hI.symm.subset hx).1, (hI.symm.subset hx).2⟩

end PoincareConjecture.M76.Dehn.Annuli
