import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.PanelGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.Incidence
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Construction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.OriginalCylinder



set_option autoImplicit false
noncomputable section
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.AnnularParameter

open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution
open BoundaryAssembly

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Rect" => (I ×ˢ I : Set P2)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}








theorem exists_marked_panel_cylinder_with_period
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r)
    (hwρ : ∀ b, w / ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w / ρ b) * s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) =
        prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔
        ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint (P false).closedStrip (P true).closedStrip) :
    ∃ b : V2 × ℝ → X,
      PolyhedralPLInCharts e b (Rim ×ˢ I) ∧
      InjOn b (Rim ×ˢ I) ∧
      b '' (Rim ×ˢ I) =
        (⋃ i : Bool × Bool, U.map '' panel r (w / 2) i) ∪
          ((P false).endDisks ∪ (P true).endDisks) ∧
      (∀ i (s : ℝ), s ∈ Icc (i.val : ℝ) (i.val + 1) →
        ∀ t ∈ I,
          b (HamiltonIndexOne.squareCircle
            ((s : ℝ) : AddCircle (4 * (2 : ℝ))), t) =
            panelFamily U (P false) (P true) r w i (s - i.val, t)) ∧
      ∀ t ∈ I,
        b '' (Rim ×ˢ {t}) =
          ⋃ i : Fin 8,
            panelFamily U (P false) (P true) r w i '' (I ×ˢ {t}) := by
  have hwr : w / 2 < r := by
    have h := (div_le_iff₀ (hρ false)).mp (hwρ false)
    linarith [hρr false]
  let f : Fin 8 → P2 → X := panelFamily U (P false) (P true) r w
  have hfp : ∀ i, PolyhedralPLInCharts e (f i) Rect ∧ InjOn (f i) Rect := by
    intro i
    simpa only [f] using panelFamily_pl_injective U (P false) (P true)
      hR he hw hwr hr1 i
  obtain ⟨hseam,hclose⟩ := panelFamily_seams_of_marked_products U P F ρ
    hw hρ hwρ hmark harms
  obtain ⟨hcontact,hend,hfar⟩ := panelFamily_incidence U hR he hw hr1 P F ρ
    hρ hρr hwρ hmark harms hlateral hdis
  obtain ⟨g,hg,hgi,hgimage,hperiod,_,_⟩ :=
    CyclicPanels.exists_original_eight_panel_annulus he.cover he.compatible f
      (fun i => (hfp i).1) (fun i => (hfp i).2) hseam hclose hcontact hend hfar
  obtain ⟨b,hb,hbi,hbimage,hbperiod,hbslice⟩ :=
    exists_original_cylinder f g hg hgi hperiod
  have hfimage : (⋃ i, f i '' Rect) =
      (⋃ i : Bool × Bool, U.map '' panel r (w / 2) i) ∪
        ((P false).endDisks ∪ (P true).endDisks) := by
    simpa only [f] using panelFamily_image U (P false) (P true) hR he hw hwr hr1
  refine ⟨b,hb,hbi,?_,hbperiod,?_⟩
  · rw [hbimage,hgimage,hfimage]
  · intro t ht
    simpa only [f] using hbslice t ht

end PoincareConjecture.M76.Dehn.Annuli.AnnularParameter
