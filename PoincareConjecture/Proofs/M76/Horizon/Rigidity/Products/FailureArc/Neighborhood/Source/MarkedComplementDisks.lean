import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.CanonicalFourSides
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.SourceContact

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Q₀" => frontier spanningOuterSquare
local notation "Q₁" => frontier spanningInnerSquare

structure FourSidedProperComplementDisk {X : Type*} [TopologicalSpace X]
    (c : P2 → P2) (f : P2 → X) (exterior : Set X) (center : Set P2) where
  carrier : Set P2
  outerEnd : ℝ
  innerEnd : ℝ
  ball : IsFinitePLBallPair P2 carrier (frontier carrier)
  subset_annulus : carrier ⊆ Ann
  cover : carrier ∪ c '' source = Ann
  contact : carrier ∩ (c '' source) = c '' (arm (-1) ∪ arm 1)
  endpoint_order : (outerEnd = 0 ∧ innerEnd = 1) ∨ (outerEnd = 1 ∧ innerEnd = 0)
  outer_preimage : ∀ p ∈ source, c p ∈ Q₀ ↔ p.1 = outerEnd
  inner_preimage : ∀ p ∈ source, c p ∈ Q₁ ↔ p.1 = innerEnd
  frontier_eq : frontier carrier = ((carrier ∩ Q₀) ∪ (carrier ∩ Q₁)) ∪
    ((c '' arm (-1)) ∪ (c '' arm 1))
  outer_interval : IsFinitePLBallPair ℝ (carrier ∩ Q₀) {c (outerEnd,-1), c (outerEnd,1)}
  inner_interval : IsFinitePLBallPair ℝ (carrier ∩ Q₁) {c (innerEnd,-1), c (innerEnd,1)}
  negative_interval : IsFinitePLBallPair ℝ (c '' arm (-1)) {c (outerEnd,-1), c (innerEnd,-1)}
  positive_interval : IsFinitePLBallPair ℝ (c '' arm 1) {c (outerEnd,1), c (innerEnd,1)}
  opposite_rims : Disjoint (carrier ∩ Q₀) (carrier ∩ Q₁)
  opposite_arms : Disjoint (c '' arm (-1)) (c '' arm 1)
  outer_contacts : ∀ v, v = -1 ∨ v = 1 →
    (carrier ∩ Q₀) ∩ (c '' arm v) = {c (outerEnd,v)}
  inner_contacts : ∀ v, v = -1 ∨ v = 1 →
    (carrier ∩ Q₁) ∩ (c '' arm v) = {c (innerEnd,v)}
  avoids_center : Disjoint carrier center
  mapsTo_exterior : MapsTo f carrier exterior
  proper : ∀ x ∈ carrier, f x ∈ frontier exterior ↔ x ∈ frontier carrier

namespace TubeExterior

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {C D : Set P2} {f₀ f₁ : P2 → X}

theorem OriginalIntervalTube.nonempty_first_four_sided_complement_disk
    (U : OriginalIntervalTube e R W Ann Ann C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    (hfR : MapsTo f₀ Ann R)
    (hfproper : ∀ x ∈ Ann, f₀ x ∈ frontier R ↔ x ∈ frontier Ann)
    (houter : (C ∩ {p : P2 | depth 8 p = -1}).Nonempty)
    (hinner : (C ∩ {p : P2 | depth 8 p = 1}).Nonempty) :
    Nonempty (FourSidedProperComplementDisk U.first f₀ (R \ U.map '' openTube 1) C) := by
  have hi : InjOn U.first source := fun x hx y hy h =>
    congrArg Subtype.val (U.first_embedding.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) h)
  have hp : ∀ p ∈ source, U.first p ∈ frontier Ann ↔ p.1 = 0 ∨ p.1 = 1 := by
    intro p hp
    rw [← hfproper _ (U.first_mapsTo hp), U.first_sheet p hp,
      U.frontier_iff _ (originalStripSheet_mem_tube false hp)]
    rfl
  obtain ⟨E,t₀,t₁,hE,hcover,hcontact,hEA,horder,h0,h1,hfront,hB₀,hB₁,hBneg,hBpos,
      hrims,harms,hcontact₀,hcontact₁⟩ := exists_planar_annulus_four_sided_complement
    U.first U.first_pl hi U.first_mapsTo hp (U.first_center.symm ▸ houter)
      (U.first_center.symm ▸ hinner)
  have hrim : Q₀ ∪ Q₁ = frontier Ann := by
    ext p
    simp only [mem_union, spanning_outer_frontier, spanning_inner_frontier,
      mem_frontier_planar_annulus_iff]
  have hfront' : frontier E = (E ∩ frontier Ann) ∪ U.first '' (arm (-1) ∪ arm 1) := by
    rw [← hrim, inter_union_distrib_left, image_union]
    exact hfront
  obtain ⟨hmaps,hproper⟩ := TubeExterior.OriginalIntervalTube.first_complement_proper
    U hR he hfR hfproper hEA hcontact hfront'
  exact ⟨{
    carrier := E
    outerEnd := t₀
    innerEnd := t₁
    ball := hE
    subset_annulus := hEA
    cover := hcover
    contact := hcontact
    endpoint_order := horder
    outer_preimage := h0
    inner_preimage := h1
    frontier_eq := hfront
    outer_interval := hB₀
    inner_interval := hB₁
    negative_interval := hBneg
    positive_interval := hBpos
    opposite_rims := hrims
    opposite_arms := harms
    outer_contacts := hcontact₀
    inner_contacts := hcontact₁
    avoids_center := U.first_center ▸ spanning_strip_complement_avoids_center hi hcontact
    mapsTo_exterior := hmaps
    proper := hproper }⟩

theorem OriginalIntervalTube.nonempty_second_four_sided_complement_disk
    (U : OriginalIntervalTube e R W Ann Ann C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    (hfR : MapsTo f₁ Ann R)
    (hfproper : ∀ x ∈ Ann, f₁ x ∈ frontier R ↔ x ∈ frontier Ann)
    (houter : (D ∩ {p : P2 | depth 8 p = -1}).Nonempty)
    (hinner : (D ∩ {p : P2 | depth 8 p = 1}).Nonempty) :
    Nonempty (FourSidedProperComplementDisk U.second f₁ (R \ U.map '' openTube 1) D) := by
  have hi : InjOn U.second source := fun x hx y hy h =>
    congrArg Subtype.val (U.second_embedding.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) h)
  have hp : ∀ p ∈ source, U.second p ∈ frontier Ann ↔ p.1 = 0 ∨ p.1 = 1 := by
    intro p hp
    rw [← hfproper _ (U.second_mapsTo hp), U.second_sheet p hp,
      U.frontier_iff _ (originalStripSheet_mem_tube true hp)]
    rfl
  obtain ⟨E,t₀,t₁,hE,hcover,hcontact,hEA,horder,h0,h1,hfront,hB₀,hB₁,hBneg,hBpos,
      hrims,harms,hcontact₀,hcontact₁⟩ := exists_planar_annulus_four_sided_complement
    U.second U.second_pl hi U.second_mapsTo hp (U.second_center.symm ▸ houter)
      (U.second_center.symm ▸ hinner)
  have hrim : Q₀ ∪ Q₁ = frontier Ann := by
    ext p
    simp only [mem_union, spanning_outer_frontier, spanning_inner_frontier,
      mem_frontier_planar_annulus_iff]
  have hfront' : frontier E = (E ∩ frontier Ann) ∪ U.second '' (arm (-1) ∪ arm 1) := by
    rw [← hrim, inter_union_distrib_left, image_union]
    exact hfront
  obtain ⟨hmaps,hproper⟩ := TubeExterior.OriginalIntervalTube.second_complement_proper
    U hR he hfR hfproper hEA hcontact hfront'
  exact ⟨{
    carrier := E
    outerEnd := t₀
    innerEnd := t₁
    ball := hE
    subset_annulus := hEA
    cover := hcover
    contact := hcontact
    endpoint_order := horder
    outer_preimage := h0
    inner_preimage := h1
    frontier_eq := hfront
    outer_interval := hB₀
    inner_interval := hB₁
    negative_interval := hBneg
    positive_interval := hBpos
    opposite_rims := hrims
    opposite_arms := harms
    outer_contacts := hcontact₀
    inner_contacts := hcontact₁
    avoids_center := U.second_center ▸ spanning_strip_complement_avoids_center hi hcontact
    mapsTo_exterior := hmaps
    proper := hproper }⟩

end TubeExterior
end PoincareConjecture.M76.Dehn.Annuli
