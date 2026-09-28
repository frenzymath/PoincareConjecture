import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.Incidence
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Sphere

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
local notation "Rect" => (I ×ˢ I : Set P2)

theorem nonempty_original_sphere_of_marked_disk_products
    {X ι E₀ E₁ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
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
    (hdis : Disjoint (P false).closedStrip (P true).closedStrip)
    {g₀ : E₀ → X} {g₁ : E₁ → X} {c₀ q₀ : Set E₀} {c₁ q₁ : Set E₁}
    (hc₀ : IsFinitePLBallPair P2 c₀ q₀) (hc₁ : IsFinitePLBallPair P2 c₁ q₁)
    (hg₀ : PolyhedralPLInCharts e g₀ c₀) (hg₁ : PolyhedralPLInCharts e g₁ c₁)
    (hi₀ : InjOn g₀ c₀) (hi₁ : InjOn g₁ c₁)
    (hrim₀ : (⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {0})) = g₀ '' q₀)
    (hrim₁ : (⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {1})) = g₁ '' q₁)
    (hcontact₀ : ((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks)) ∩ (g₀ '' c₀) = g₀ '' q₀)
    (hcontact₁ : ((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks)) ∩ (g₁ '' c₁) = g₁ '' q₁)
    (hgdis : Disjoint (g₀ '' c₀) (g₁ '' c₁)) :
    Nonempty (ChartwisePLSphere e
      (((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
        ((P false).endDisks ∪ (P true).endDisks)) ∪ ((g₀ '' c₀) ∪ (g₁ '' c₁)))) := by
  have hwr : w/2 < r := by
    have h := (div_le_iff₀ (hρ false)).mp (hwρ false)
    linarith [hρr false]
  have hmaps := panelFamily_pl_injective U (P false) (P true) hR he hw hwr hr1
  obtain ⟨hseam,hclose⟩ := panelFamily_seams_of_marked_products U P F ρ hw hρ hwρ hmark harms
  obtain ⟨hcontact,hend,hfar⟩ := panelFamily_incidence U hR he hw hr1 P F ρ hρ hρr
    hwρ hmark harms hlateral hdis
  have himage := panelFamily_image U (P false) (P true) hR he hw hwr hr1
  have hs := CyclicPanels.nonempty_original_sphere_of_eight_panels he.cover he.compatible
    (panelFamily U (P false) (P true) r w) (fun i => (hmaps i).1) (fun i => (hmaps i).2)
    hseam hclose hcontact hend hfar hc₀ hc₁ hg₀ hg₁ hi₀ hi₁ hrim₀ hrim₁
    (by rw [himage]; exact hcontact₀) (by rw [himage]; exact hcontact₁) hgdis
  simpa only [himage] using hs

end PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
