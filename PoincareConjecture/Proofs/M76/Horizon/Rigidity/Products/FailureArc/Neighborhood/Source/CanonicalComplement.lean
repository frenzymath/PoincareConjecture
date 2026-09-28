import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.UnorientedComplement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.Canonical

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_planar_annulus_strip_complement
    (c : P2 → P2) (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hin : MapsTo c source Ann)
    (hproper : ∀ p ∈ source, c p ∈ frontier Ann ↔ p.1 = 0 ∨ p.1 = 1)
    (houter : (c '' arm 0 ∩ {p : P2 | depth 8 p = -1}).Nonempty)
    (hinner : (c '' arm 0 ∩ {p : P2 | depth 8 p = 1}).Nonempty) :
    ∃ E : Set P2, IsFinitePLBallPair P2 E (frontier E) ∧
      E ∪ c '' source = Ann ∧ E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1) ∧
      E ⊆ Ann ∧ frontier E = (E ∩ frontier Ann) ∪ c '' (arm (-1) ∪ arm 1) := by
  have hrim : frontier spanningOuterSquare ∪ frontier spanningInnerSquare = frontier Ann := by
    ext p
    simp only [mem_union,spanning_outer_frontier,spanning_inner_frontier,
      mem_frontier_planar_annulus_iff]
  have houter' : (c '' arm 0 ∩ frontier spanningOuterSquare).Nonempty := by
    rcases houter with ⟨x,⟨p,hp,rfl⟩,hx⟩
    exact ⟨c p,⟨⟨p,hp,rfl⟩,(spanning_outer_frontier _).mpr hx⟩⟩
  have hinner' : (c '' arm 0 ∩ frontier spanningInnerSquare).Nonempty := by
    rcases hinner with ⟨x,⟨p,hp,rfl⟩,hx⟩
    exact ⟨c p,⟨⟨p,hp,rfl⟩,(spanning_inner_frontier _).mpr hx⟩⟩
  simpa only [spanning_squares_source,hrim] using exists_unoriented_spanning_strip_complement
    spanningInnerSquare_ball spanningOuterSquare_ball spanning_squares_nested c hc hci
      (spanning_squares_source.symm ▸ hin) (hrim.symm ▸ hproper) houter' hinner'

theorem spanning_strip_complement_avoids_center
    {E : Set P2} {c : P2 → P2} (hci : InjOn c source)
    (hcontact : E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1)) :
    Disjoint E (c '' arm 0) := by
  apply disjoint_left.mpr
  rintro x hx ⟨p,hp,rfl⟩
  have hpS : p ∈ source := ⟨hp.1,by rw [show p.2 = 0 from hp.2]; norm_num⟩
  obtain ⟨q,hq,hqp⟩ := hcontact.subset ⟨hx,⟨p,hpS,rfl⟩⟩
  have hqS : q ∈ source := by
    rcases hq with h|h <;> exact ⟨h.1,by rw [show q.2 = _ from h.2]; norm_num⟩
  have heq : q = p := hci hqS hpS hqp
  subst q
  rcases hq with h|h
  all_goals
    have h0 : p.2 = 0 := hp.2
    have h1 : p.2 = _ := h.2
    linarith

end PoincareConjecture.M76.Dehn.Annuli
