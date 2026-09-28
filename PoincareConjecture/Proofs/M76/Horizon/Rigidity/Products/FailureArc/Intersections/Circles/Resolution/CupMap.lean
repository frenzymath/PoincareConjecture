import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.CollarDiskMap



set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_cup_map
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {A₀ A₁ : Set P2} {L d : ℝ}
    (B₀ : OrientedPolygonCollar L d A₀) (B₁ : OrientedPolygonCollar L d A₁)
    (f a : P2 → X) (hf : PolyhedralPLInCharts e f (closure B₁.inner.inside))
    (ha : PolyhedralPLInCharts e a (squareAnnulus L d))
    (hainner : ∀ p : squareAnnulus L d, depth L p = d → a p = f (B₁.chart p)) :
    ∃ (H : closure B₁.inner.inside ≃ₜ closure B₀.inner.inside) (v : P2 → X),
      H.IsFinitePL ∧ PolyhedralPLInCharts e v (closure B₀.outer.inside) ∧
      (∀ x : closure B₁.inner.inside, v (H x) = f x) ∧
      (∀ p : squareAnnulus L d, v (B₀.chart p) = a p) ∧
      (∀ (p : squareAnnulus L d) (hp : depth L p = d),
        (H ⟨B₁.chart p, (B₁.inner.isFinitePLBallPair_closed_inside
          B₁.inner_simplicial B₁.inner_injective).1 ((B₁.inner_depth p).mpr hp)⟩ : P2) =
          B₀.chart p) ∧
      v '' closure B₀.outer.inside = f '' closure B₁.inner.inside ∪ a '' squareAnnulus L d := by
  obtain ⟨H, hH, _, hperiod, _⟩ := exists_synchronized_inner_disk_exchange B₁ B₀
  obtain ⟨rI, hrI, hrIH⟩ := hH.symm
  obtain ⟨rC, hrC, hrCc⟩ := B₀.chart_PL.symm
  have hI := B₀.inner.isFinitePLBallPair_closed_inside B₀.inner_simplicial B₀.inner_injective
  have hi : closure B₀.inner.inside ⊆ closure B₀.outer.inside := B₀.nested.trans subset_closure
  have hrImap : MapsTo rI (closure B₀.inner.inside) (closure B₁.inner.inside) := by
    intro x hx
    rw [← hrIH ⟨x, hx⟩]
    exact (H.symm ⟨x, hx⟩).property
  have hrCmap : MapsTo rC A₀ (squareAnnulus L d) := by
    intro x hx
    rw [← hrCc ⟨x, hx⟩]
    exact (B₀.chart.symm ⟨x, hx⟩).property
  have hrCH (p : squareAnnulus L d) : rC (B₀.chart p) = p := by
    rw [← hrCc, B₀.chart.symm_apply_apply]
  have hcoord (x : A₀) : (B₀.chart ⟨rC x, hrCmap x.property⟩ : P2) = x := by
    have hp : (⟨rC x, hrCmap x.property⟩ : squareAnnulus L d) = B₀.chart.symm x :=
      Subtype.ext (hrCc x).symm
    rw [hp, B₀.chart.apply_symm_apply]
  have hcover : closure B₀.inner.inside ∪ A₀ = closure B₀.outer.inside := by
    conv_lhs => rhs; rw [B₀.carrier]
    ext x
    constructor
    · rintro (hx | hx)
      exacts [hi hx, hx.1]
    · intro hx
      by_cases h : x ∈ B₀.inner.inside
      · exact Or.inl (subset_closure h)
      · exact Or.inr ⟨hx, h⟩
  obtain ⟨KI, hKI, hKIs, hKIaff⟩ := hrI
  obtain ⟨KC, hKC, hKCs, hKCaff⟩ := hrC
  have hfi : PolyhedralPLInCharts e (f ∘ rI) KI.space :=
    hf.comp_finitePiecewiseAffineOn KI hKI ⟨KI, hKI, rfl, hKIaff⟩
      (fun _ hx ↦ hrImap (hKIs.subset hx))
  have hfa : PolyhedralPLInCharts e (a ∘ rC) KC.space :=
    ha.comp_finitePiecewiseAffineOn KC hKC ⟨KC, hKC, rfl, hKCaff⟩
      (fun _ hx ↦ hrCmap (hKCs.subset hx))
  obtain ⟨v, hv, hvi, hvc⟩ := exists_circle_attachment_map_union hcompat KI KC hKI hKC hfi hfa (by
    intro x hxi hxc
    have hxI := hKIs.subset hxi
    have hxC := hKCs.subset hxc
    have hxb : x ∈ B₀.inner.boundary ℝ := by
      rw [← B₀.inner.frontier_inside B₀.inner_simplicial B₀.inner_injective,
        frontier, (B₀.inner.isOpen_inside B₀.inner_simplicial B₀.inner_injective).interior_eq]
      exact ⟨hxI, (B₀.carrier.subset hxC).2⟩
    let p : squareAnnulus L d := ⟨rC x, hrCmap hxC⟩
    have hcp : (B₀.chart p : P2) = x := hcoord ⟨x, hxC⟩
    have hp : depth L p = d := (B₀.inner_depth p).mp (hcp.symm ▸ hxb)
    have hh : rI x = B₁.chart p := by
      rw [← hcp, ← hperiod p hp, ← hrIH, H.symm_apply_apply]
    exact (congrArg f hh).trans (hainner p hp).symm)
  have hdom : KI.space ∪ KC.space = closure B₀.outer.inside := by
    rwa [hKIs, hKCs]
  have hvi' (x : closure B₁.inner.inside) : v (H x) = f x := by
    rw [hvi (hKIs.symm.subset (H x).property)]
    change f (rI (H x)) = f x
    rw [← hrIH, H.symm_apply_apply]
  have hvc' (p : squareAnnulus L d) : v (B₀.chart p) = a p := by
    rw [hvc (hKCs.symm.subset (B₀.chart p).property)]
    change a (rC (B₀.chart p)) = a p
    rw [hrCH]
  refine ⟨H, v, hH, hdom ▸ hv, hvi', hvc', hperiod, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hcover.symm.subset hx with hxI | hxC
    · exact Or.inl ⟨rI x, hrImap hxI, (hvi (hKIs.symm.subset hxI)).symm⟩
    · exact Or.inr ⟨rC x, hrCmap hxC, (hvc (hKCs.symm.subset hxC)).symm⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨H ⟨x, hx⟩, hi (H ⟨x, hx⟩).property, hvi' ⟨x, hx⟩⟩
    · exact ⟨B₀.chart ⟨p, hp⟩, hcover.subset (Or.inr (B₀.chart ⟨p, hp⟩).property),
        hvc' ⟨p, hp⟩⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
