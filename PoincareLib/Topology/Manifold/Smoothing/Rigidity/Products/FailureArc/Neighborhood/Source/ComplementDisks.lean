import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.SourceContact

/-! # Proper complementary disks constructed from the spanning annuli

Cut each original source annulus along its actual spanning strip. The
resulting finite PL disk is proper in the physical tube exterior.
This is the disk-cut stage of Waldhausen Lemma 5.1, pp. 72--73.
-/

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareMT.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {C D : Set P2} {f₀ f₁ : P2 → X}

theorem OriginalIntervalTube.exists_first_complement_disk
    (U : OriginalIntervalTube e R W Ann Ann C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    (hfR : MapsTo f₀ Ann R)
    (hfproper : ∀ x ∈ Ann, f₀ x ∈ frontier R ↔ x ∈ frontier Ann)
    (houter : (C ∩ {p : P2 | depth 8 p = -1}).Nonempty)
    (hinner : (C ∩ {p : P2 | depth 8 p = 1}).Nonempty) :
    ∃ E : Set P2, IsFinitePLBallPair P2 E (frontier E) ∧ E ⊆ Ann ∧
      E ∪ U.first '' source = Ann ∧
      E ∩ (U.first '' source) = U.first '' (arm (-1) ∪ arm 1) ∧
      Disjoint E C ∧ MapsTo f₀ E (R \ U.map '' openTube 1) ∧
      ∀ x ∈ E, f₀ x ∈ frontier (R \ U.map '' openTube 1) ↔ x ∈ frontier E := by
  have hi : InjOn U.first source := fun x hx y hy h =>
    congrArg Subtype.val (U.first_embedding.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) h)
  have hp : ∀ p ∈ source, U.first p ∈ frontier Ann ↔ p.1 = 0 ∨ p.1 = 1 := by
    intro p hp
    rw [← hfproper _ (U.first_mapsTo hp),U.first_sheet p hp,
      U.frontier_iff _ (originalStripSheet_mem_tube false hp)]
    rfl
  obtain ⟨E,hE,hcover,hcontact,hES,hfront⟩ := exists_planar_annulus_strip_complement
    U.first U.first_pl hi U.first_mapsTo hp (U.first_center.symm ▸ houter)
      (U.first_center.symm ▸ hinner)
  have hproper := OriginalIntervalTube.first_complement_proper U hR he hfR hfproper
    hES hcontact hfront
  exact ⟨E,hE,hES,hcover,hcontact,U.first_center ▸
    spanning_strip_complement_avoids_center hi hcontact,hproper⟩

theorem OriginalIntervalTube.exists_second_complement_disk
    (U : OriginalIntervalTube e R W Ann Ann C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    (hfR : MapsTo f₁ Ann R)
    (hfproper : ∀ x ∈ Ann, f₁ x ∈ frontier R ↔ x ∈ frontier Ann)
    (houter : (D ∩ {p : P2 | depth 8 p = -1}).Nonempty)
    (hinner : (D ∩ {p : P2 | depth 8 p = 1}).Nonempty) :
    ∃ E : Set P2, IsFinitePLBallPair P2 E (frontier E) ∧ E ⊆ Ann ∧
      E ∪ U.second '' source = Ann ∧
      E ∩ (U.second '' source) = U.second '' (arm (-1) ∪ arm 1) ∧
      Disjoint E D ∧ MapsTo f₁ E (R \ U.map '' openTube 1) ∧
      ∀ x ∈ E, f₁ x ∈ frontier (R \ U.map '' openTube 1) ↔ x ∈ frontier E := by
  have hi : InjOn U.second source := fun x hx y hy h =>
    congrArg Subtype.val (U.second_embedding.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) h)
  have hp : ∀ p ∈ source, U.second p ∈ frontier Ann ↔ p.1 = 0 ∨ p.1 = 1 := by
    intro p hp
    rw [← hfproper _ (U.second_mapsTo hp),U.second_sheet p hp,
      U.frontier_iff _ (originalStripSheet_mem_tube true hp)]
    rfl
  obtain ⟨E,hE,hcover,hcontact,hES,hfront⟩ := exists_planar_annulus_strip_complement
    U.second U.second_pl hi U.second_mapsTo hp (U.second_center.symm ▸ houter)
      (U.second_center.symm ▸ hinner)
  have hproper := OriginalIntervalTube.second_complement_proper U hR he hfR hfproper
    hES hcontact hfront
  exact ⟨E,hE,hES,hcover,hcontact,U.second_center ▸
    spanning_strip_complement_avoids_center hi hcontact,hproper⟩

end PoincareMT.M76.Dehn.Annuli.TubeExterior
