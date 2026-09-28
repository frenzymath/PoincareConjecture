import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.LateralCut

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution BoundaryAssembly

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem final_panel_annulus_disjoint_removed
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r ≤ 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w / ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w / ρ b) * s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J))) :
    Disjoint ((⋃ i : Bool × Bool, U.map '' panel r (w / 2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks))
      (U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip) := by
  have hr : 0 < r := (hρ false).trans (hρr false)
  have hpanels := lateral_sdiff_two_openStrips U hR he hw hr1 P F ρ
    hρ hρr hwρ hmark harms hlateral
  have hclosed (b : Bool) : (P b).closedStrip ⊆ (P b).map '' (Disk ×ˢ J) := by
    apply image_mono
    rintro z ⟨hz,hs⟩
    exact ⟨hz, by constructor <;> linarith [hs.1,hs.2]⟩
  have hopen (b : Bool) : (P b).openStrip ⊆ (P b).map '' (Disk ×ˢ J) :=
    (image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self)).trans (hclosed b)
  have hend (b : Bool) : (P b).endDisks ⊆ (P b).map '' (Disk ×ˢ J) :=
    (P b).closedStrip_sdiff_openStrip.symm.subset.trans (sdiff_subset.trans (hclosed b))
  have havoidTube (b : Bool) {x : X} (hx : x ∈ (P b).endDisks) :
      x ∉ U.map '' openTube r := by
    obtain ⟨z,hz,rfl⟩ := hend b hx
    exact ((P b).inside hz).2
  have havoidOwn (b : Bool) {x : X} (hx : x ∈ (P b).endDisks) :
      x ∉ (P b).openStrip := ((P b).closedStrip_sdiff_openStrip.symm.subset hx).2
  apply disjoint_left.mpr
  intro x hx hxO
  rcases hx with hx | hx
  · have hp := hpanels.symm.subset hx
    have ht := (TubeExterior.OriginalIntervalTube.closedTube_sdiff_openTube U hr hr1).symm.subset hp.1
    rcases hxO with (hxT | hx₀) | hx₁
    · exact ht.2 hxT
    · exact hp.2 (Or.inl hx₀)
    · exact hp.2 (Or.inr hx₁)
  · rcases hx with hx₀ | hx₁
    · rcases hxO with (hxT | ho₀) | ho₁
      · exact havoidTube false hx₀ hxT
      · exact havoidOwn false hx₀ ho₀
      · exact disjoint_left.mp hdis (hend false hx₀) (hopen true ho₁)
    · rcases hxO with (hxT | ho₀) | ho₁
      · exact havoidTube true hx₁ hxT
      · exact disjoint_left.mp hdis (hopen false ho₀) (hend true hx₁)
      · exact havoidOwn true hx₁ ho₁

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
