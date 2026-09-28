import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.FourSides
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.CanonicalComplement

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Q₀" => frontier spanningOuterSquare
local notation "Q₁" => frontier spanningInnerSquare

theorem planar_annulus_strip_complement_rim_markings
    {E : Set P2} {c : P2 → P2}
    (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hproper : ∀ p ∈ source, c p ∈ frontier Ann ↔ p.1 = 0 ∨ p.1 = 1)
    (houter : (c '' arm 0 ∩ {p : P2 | depth 8 p = -1}).Nonempty)
    (hinner : (c '' arm 0 ∩ {p : P2 | depth 8 p = 1}).Nonempty)
    (hcover : E ∪ c '' source = Ann)
    (hcontact : E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1)) :
    ∃ t₀ t₁ : ℝ, ((t₀ = 0 ∧ t₁ = 1) ∨ (t₀ = 1 ∧ t₁ = 0)) ∧
      (∀ p ∈ source, c p ∈ Q₀ ↔ p.1 = t₀) ∧
      (∀ p ∈ source, c p ∈ Q₁ ↔ p.1 = t₁) ∧
      IsFinitePLBallPair ℝ (E ∩ Q₀) {c (t₀,-1),c (t₀,1)} ∧
      IsFinitePLBallPair ℝ (E ∩ Q₁) {c (t₁,-1),c (t₁,1)} := by
  have hQA₀ : Q₀ ⊆ Ann := by
    intro x hx
    rw [← spanning_squares_source]
    exact ⟨spanningOuterSquare_ball.1 hx,
      fun h => hx.2 (spanning_squares_nested (interior_subset h))⟩
  have hQA₁ : Q₁ ⊆ Ann := by
    intro x hx
    rw [← spanning_squares_source]
    exact ⟨interior_subset (spanning_squares_nested (spanningInnerSquare_ball.1 hx)),hx.2⟩
  have hrim : Q₀ ∪ Q₁ = frontier Ann := by
    ext p
    simp only [mem_union,spanning_outer_frontier,spanning_inner_frontier,
      mem_frontier_planar_annulus_iff]
  have houter' : (c '' arm 0 ∩ Q₀).Nonempty := by
    obtain ⟨x,hx,hdepth⟩ := houter
    exact ⟨x,hx,(spanning_outer_frontier x).mpr hdepth⟩
  have hinner' : (c '' arm 0 ∩ Q₁).Nonempty := by
    obtain ⟨x,hx,hdepth⟩ := hinner
    exact ⟨x,hx,(spanning_inner_frontier x).mpr hdepth⟩
  exact strip_complement_rim_markings spanningOuterSquare_ball spanningInnerSquare_ball
    hQA₀ hQA₁ spanning_squares_disjoint hc hci (hrim.symm ▸ hproper)
    houter' hinner' hcover hcontact

theorem exists_planar_annulus_four_sided_complement
    (c : P2 → P2) (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hin : MapsTo c source Ann)
    (hproper : ∀ p ∈ source, c p ∈ frontier Ann ↔ p.1 = 0 ∨ p.1 = 1)
    (houter : (c '' arm 0 ∩ {p : P2 | depth 8 p = -1}).Nonempty)
    (hinner : (c '' arm 0 ∩ {p : P2 | depth 8 p = 1}).Nonempty) :
    ∃ (E : Set P2) (t₀ t₁ : ℝ), IsFinitePLBallPair P2 E (frontier E) ∧
      E ∪ c '' source = Ann ∧ E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1) ∧
      E ⊆ Ann ∧ ((t₀ = 0 ∧ t₁ = 1) ∨ (t₀ = 1 ∧ t₁ = 0)) ∧
      (∀ p ∈ source, c p ∈ Q₀ ↔ p.1 = t₀) ∧
      (∀ p ∈ source, c p ∈ Q₁ ↔ p.1 = t₁) ∧
      frontier E = ((E ∩ Q₀) ∪ (E ∩ Q₁)) ∪ ((c '' arm (-1)) ∪ (c '' arm 1)) ∧
      IsFinitePLBallPair ℝ (E ∩ Q₀) {c (t₀,-1),c (t₀,1)} ∧
      IsFinitePLBallPair ℝ (E ∩ Q₁) {c (t₁,-1),c (t₁,1)} ∧
      IsFinitePLBallPair ℝ (c '' arm (-1)) {c (t₀,-1),c (t₁,-1)} ∧
      IsFinitePLBallPair ℝ (c '' arm 1) {c (t₀,1),c (t₁,1)} ∧
      Disjoint (E ∩ Q₀) (E ∩ Q₁) ∧ Disjoint (c '' arm (-1)) (c '' arm 1) ∧
      (∀ v, v = -1 ∨ v = 1 → (E ∩ Q₀) ∩ (c '' arm v) = {c (t₀,v)}) ∧
      (∀ v, v = -1 ∨ v = 1 → (E ∩ Q₁) ∩ (c '' arm v) = {c (t₁,v)}) := by
  obtain ⟨E,hE,hcover,hcontact,hEA,hfront⟩ :=
    exists_planar_annulus_strip_complement c hc hci hin hproper houter hinner
  obtain ⟨t₀,t₁,horder,h0,h1,hB₀,hB₁⟩ :=
    planar_annulus_strip_complement_rim_markings hc hci hproper houter hinner hcover hcontact
  have h0I : t₀ ∈ Icc (0 : ℝ) 1 := by
    rcases horder with ⟨rfl,_⟩|⟨rfl,_⟩ <;> norm_num
  have h1I : t₁ ∈ Icc (0 : ℝ) 1 := by
    rcases horder with ⟨_,rfl⟩|⟨_,rfl⟩ <;> norm_num
  have harm (v : ℝ) (hv : v = -1 ∨ v = 1) :
      IsFinitePLBallPair ℝ (c '' arm v) {c (t₀,v),c (t₁,v)} := by
    have hh := strip_far_arm_ball hc hci hv
    rcases horder with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hh
    · simpa only [pair_comm] using hh
  have hrim : Q₀ ∪ Q₁ = frontier Ann := by
    ext p
    simp only [mem_union,spanning_outer_frontier,spanning_inner_frontier,
      mem_frontier_planar_annulus_iff]
  refine ⟨E,t₀,t₁,hE,hcover,hcontact,hEA,horder,h0,h1,?_,hB₀,hB₁,
    harm (-1) (Or.inl rfl),harm 1 (Or.inr rfl),
    spanning_squares_disjoint.mono inter_subset_right inter_subset_right,
    strip_far_arms_disjoint hci,?_,?_⟩
  · rw [hfront,← hrim,inter_union_distrib_left,image_union]
  · intro v hv
    exact strip_complement_rim_arm_inter h0I hv h0 hcontact
  · intro v hv
    exact strip_complement_rim_arm_inter h1I hv h1 hcontact

end PoincareConjecture.M76.Dehn.Annuli
