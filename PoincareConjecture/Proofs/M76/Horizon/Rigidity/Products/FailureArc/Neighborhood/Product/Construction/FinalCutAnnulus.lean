import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PanelCylinderPeriod
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PairCylinder
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Contacts.CutOverlap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.Assembly

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution
open BoundaryAssembly ProductPieces AnnularParameter

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem exists_final_cut_annulus
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
    ∃ b : V2 × ℝ → X,
      PolyhedralPLInCharts e b (Rim ×ˢ I) ∧ InjOn b (Rim ×ˢ I) ∧
      ((⋃ k, range (pieceParameter U P r k)) ∩ Q₁.cutCarrier = b '' (Rim ×ˢ I)) ∧
      ((⋃ k, range (pieceParameter U P r k)) ∪ Q₁.cutCarrier = R) ∧
      PolyhedralPLInCharts e (pairCylinder b) ((sphere (0 : P2) 1) ×ˢ I) ∧
      InjOn (pairCylinder b) ((sphere (0 : P2) 1) ×ˢ I) ∧
      pairCylinder b '' ((sphere (0 : P2) 1) ×ˢ I) =
        (⋃ k, range (pieceParameter U P r k)) ∩ Q₁.cutCarrier ∧
      (∀ i (s : ℝ), s ∈ Icc (i.val : ℝ) (i.val + 1) → ∀ t ∈ I,
        b (HamiltonIndexOne.squareCircle
          ((s : ℝ) : AddCircle (4 * (2 : ℝ))), t) =
          panelFamily U (P false) (P true) r w i (s - i.val, t)) ∧
      ∀ t ∈ I, pairCylinder b '' ((sphere (0 : P2) 1) ×ˢ {t}) =
        ⋃ i : Fin 8, panelFamily U (P false) (P true) r w i '' (I ×ˢ {t}) := by
  have hdis' : Disjoint (P false).closedStrip (P true).closedStrip := by
    simpa only [OriginalDiskProduct.closedStrip, hmap] using hdis
  obtain ⟨b, hb, hbi, hbimage, hperiod, hslice⟩ :=
    exists_marked_panel_cylinder_with_period U hR he hw hr1 P F ρ
      hρ hρr hwρ hmark harms hlateral hdis'
  obtain ⟨hinter, hcover, _⟩ := neighborhood_final_cut_overlap U hR he hw hr1 P F ρ
    hρ hρr hwρ hmark harms hlateral Q₁ hmap hdis hopen₀ hopen₁
  have hi : (⋃ k, range (pieceParameter U P r k)) ∩ Q₁.cutCarrier =
      b '' (Rim ×ˢ I) := by
    rw [pieceParameter_range U P, hbimage]
    exact hinter
  obtain ⟨ha, hai, haimage, haslice⟩ := pairCylinder_properties hb hbi
  refine ⟨b, hb, hbi, hi, ?_, ha, hai, haimage.trans hi.symm, hperiod, ?_⟩
  · rw [pieceParameter_range U P]
    exact hcover
  · intro t ht
    exact (haslice t).trans (hslice t ht)

end PoincareConjecture.M76.Dehn.Annuli.ProductConstruction
