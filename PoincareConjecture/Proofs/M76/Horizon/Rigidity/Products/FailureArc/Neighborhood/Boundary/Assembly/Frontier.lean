import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.LateralCut
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.FinalFrontier



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem final_frontier_of_marked_products
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w/ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w/ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (Q₁ : OriginalDiskProduct e (P false).cutCarrier (j true))
    (hmap : Q₁.map = (P true).map)
    (hdis : Disjoint (P false).closedStrip Q₁.closedStrip)
    (hopen₀ : IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
      (P false).openStrip))
    (hopen₁ : IsOpen ((Subtype.val : (P false).cutCarrier → X) ⁻¹' Q₁.openStrip)) :
    frontier Q₁.cutCarrier =
      (frontier R \ (U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip)) ∪
      ((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
        ((P false).endDisks ∪ (P true).endDisks)) ∧
    Q₁.cutCarrier = R \ (U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip) := by
  have hr : 0 < r := (hρ false).trans (hρr false)
  have hQ := TubeExterior.OriginalIntervalTube.isCompact_exterior U hR he hr hr1
  obtain ⟨hc₀,_,hf₀,hi₀,hu₀,_⟩ := (P false).cut_geometry hQ hopen₀
  obtain ⟨_,_,hf₁,hi₁,hu₁,_⟩ := Q₁.cut_geometry hc₀ hopen₁
  obtain ⟨hfront,hcarrier,_,_,_⟩ :=
    TubeExterior.OriginalIntervalTube.final_frontier_inventory U hR he hr hr1
      (P false) Q₁ hdis hf₀ hf₁ hi₀ hu₀ hi₁ hu₁
  have hopen : Q₁.openStrip = (P true).openStrip := by
    simp only [OriginalDiskProduct.openStrip,hmap]
  have hend : Q₁.endDisks = (P true).endDisks := by
    simp only [OriginalDiskProduct.endDisks,hmap]
  rw [← BoundaryInventory.endDisks_eq_slice_images,
    ← BoundaryInventory.endDisks_eq_slice_images,hopen,hend,
    lateral_sdiff_two_openStrips U hR he hw hr1 P F ρ hρ hρr hwρ hmark harms hlateral] at hfront
  exact ⟨by simpa only [union_assoc] using hfront,by simpa only [hopen] using hcarrier⟩

end PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
