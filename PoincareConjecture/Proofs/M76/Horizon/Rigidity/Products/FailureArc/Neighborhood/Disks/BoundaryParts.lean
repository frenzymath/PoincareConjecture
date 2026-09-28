import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.MarkedRectangle

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)
local notation "Ann" => squareAnnulus 8 1

theorem rectangle_horizontal_preimage_of_image
    {g : P2 → P2} {A : Set P2} {t : ℝ} (ht : t ∈ I)
    (hi : InjOn g Rect) (himage : g '' (I ×ˢ {t}) = A)
    {p : P2} (hp : p ∈ Rect) : g p ∈ A ↔ p.2 = t := by
  rw [← himage,hi.mem_image_iff (prod_mono Subset.rfl (singleton_subset_iff.mpr ht)) hp]
  exact and_iff_right hp.1

theorem rectangle_vertical_preimage_of_image
    {g : P2 → P2} {A : Set P2} {t : ℝ} (ht : t ∈ I)
    (hi : InjOn g Rect) (himage : g '' ({t} ×ˢ I) = A)
    {p : P2} (hp : p ∈ Rect) : g p ∈ A ↔ p.1 = t := by
  rw [← himage,hi.mem_image_iff (prod_mono (singleton_subset_iff.mpr ht) Subset.rfl) hp]
  exact and_iff_left hp.2

theorem strip_rectangle_boundary_parts
    {X : Type*} [TopologicalSpace X] {R Q : Set X} {center : Set P2}
    {f : P2 → X} {c g : P2 → P2} {τ : C3 → X}
    (M : FourSidedProperComplementDisk c f Q center)
    (j : Bool) (hτ : InjOn τ tube)
    (hpre : Ann ∩ f ⁻¹' (τ '' tube) = c '' source)
    (hsheet : ∀ p ∈ source, f (c p) = τ (originalStripSheet j p))
    (hfproper : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hg : BijOn g Rect M.carrier)
    (houter : g '' (I ×ˢ {(0 : ℝ)}) = M.carrier ∩ frontier spanningOuterSquare)
    (hinner : g '' (I ×ˢ {(1 : ℝ)}) = M.carrier ∩ frontier spanningInnerSquare)
    (hnegative : g '' ({(0 : ℝ)} ×ˢ I) = c '' arm (-1))
    (hpositive : g '' ({(1 : ℝ)} ×ˢ I) = c '' arm 1) :
    ∀ p ∈ Rect,
      (f (g p) ∈ frontier R ↔ p.2 = 0 ∨ p.2 = 1) ∧
      (f (g p) ∈ τ '' TubeExterior.lateral 1 ↔ p.1 = 0 ∨ p.1 = 1) ∧
      (f (g p) ∈ frontier R ∩ (τ '' TubeExterior.lateral 1) ↔
        (p.1 = 0 ∨ p.1 = 1) ∧ (p.2 = 0 ∨ p.2 = 1)) := by
  have hcontact := TubeExterior.strip_complement_contacts j hτ hpre hsheet
    M.subset_annulus M.contact
  have hrim : frontier Ann = frontier spanningOuterSquare ∪ frontier spanningInnerSquare := by
    ext x
    simp only [mem_union,spanning_outer_frontier,spanning_inner_frontier,
      mem_frontier_planar_annulus_iff]
  intro p hp
  have hpM := hg.1 hp
  have h0 := rectangle_horizontal_preimage_of_image (by norm_num) hg.2.1 houter hp
  have h1 := rectangle_horizontal_preimage_of_image (by norm_num) hg.2.1 hinner hp
  have hm := rectangle_vertical_preimage_of_image (by norm_num) hg.2.1 hnegative hp
  have hplus := rectangle_vertical_preimage_of_image (by norm_num) hg.2.1 hpositive hp
  have hR : f (g p) ∈ frontier R ↔ p.2 = 0 ∨ p.2 = 1 := by
    rw [hfproper _ (M.subset_annulus hpM),hrim]
    simpa only [mem_union,mem_inter_iff,hpM,true_and] using or_congr h0 h1
  have hL : f (g p) ∈ τ '' TubeExterior.lateral 1 ↔ p.1 = 0 ∨ p.1 = 1 := by
    rw [(hcontact _ hpM).2,image_union]
    exact or_congr hm hplus
  exact ⟨hR,hL,by rw [mem_inter_iff,hR,hL,and_comm]⟩

end PoincareConjecture.M76.Dehn.Annuli
