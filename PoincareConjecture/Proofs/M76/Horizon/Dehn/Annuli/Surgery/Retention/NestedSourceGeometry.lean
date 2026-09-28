import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Collars.RetainedContacts

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)


theorem oriented_collar_seams_avoid_of_middle_trace
    {A G : Set P2} {l r : ℝ} (B : OrientedPolygonCollar l r A) (hr : 0 < r)
    (htrace : ∀ p : squareAnnulus l r, (B.chart p : P2) ∈ G → depth l p = 0) :
    Disjoint G (B.outer.boundary ℝ ∪ B.inner.boundary ℝ) := by
  apply disjoint_left.mpr
  intro x hx hb
  have hxA : x ∈ A := hb.elim (fun h ↦ (oriented_collar_boundary_subsets B).1 h)
    (fun h ↦ (oriented_collar_boundary_subsets B).2 h)
  let p := B.chart.symm ⟨x, hxA⟩
  have hp : (B.chart p : P2) = x := congrArg Subtype.val (B.chart.apply_symm_apply _)
  have hz := htrace p (hp.symm ▸ hx)
  rcases hb with ho | hi
  · have hh := (B.outer_depth p).mp (hp.symm ▸ ho)
    linarith
  · have hh := (B.inner_depth p).mp (hp.symm ▸ hi)
    linarith



theorem nested_retained_closed_band
    {A₀ A₁ G : Set P2} {l₀ r₀ l₁ r₁ L d : ℝ}
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (htrace₀ : ∀ p : squareAnnulus l₀ r₀, (B₀.chart p : P2) ∈ G → depth l₀ p = 0)
    (htrace₁ : ∀ p : squareAnnulus l₁ r₁, (B₁.chart p : P2) ∈ G → depth l₁ p = 0) :
    let O := annulusSquare L (-d) \ B₀.outer.inside
    let I := closure B₁.inner.inside \ interior (annulusSquare L d)
    let B := closure B₀.outer.inside \ B₁.inner.inside
    IsClosed B ∧ squareAnnulus L d ⊆ (O ∪ I) ∪ B ∧
      Disjoint ((O ∪ I) ∩ G) B := by
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
    have hd := mem_squareAnnulus_iff_depth.mp hx
    by_cases hxo : x ∈ B₀.outer.inside
    · by_cases hxi : x ∈ B₁.inner.inside
      · refine Or.inl (Or.inr ⟨subset_closure hxi, ?_⟩)
        intro hh
        exact (not_lt_of_ge hd.2) ((mem_interior_annulusSquare_iff L d x).mp hh)
      · exact Or.inr ⟨subset_closure hxo, hxi⟩
    · exact Or.inl (Or.inl ⟨(mem_annulusSquare_iff L (-d) x).mpr hd.1, hxo⟩)
  · apply disjoint_left.mpr
    rintro x ⟨(hx | hx), hg⟩ hb
    · exact disjoint_left.mp hseam₀ hg (Or.inl (ho.symm.subset ⟨hb.1, hx.2⟩))
    · exact disjoint_left.mp hseam₁ hg (Or.inr (hi.symm.subset ⟨hx.1, hb.2⟩))

end PoincareConjecture.M76.Dehn.Annuli
