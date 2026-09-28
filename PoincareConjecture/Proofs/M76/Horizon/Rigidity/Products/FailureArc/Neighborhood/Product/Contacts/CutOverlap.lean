import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.Frontier



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

theorem neighborhood_final_cut_overlap
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
    let N := U.map '' closedTube r ∪ ((P false).closedStrip ∪ (P true).closedStrip)
    let A := (⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks)
    N ∩ Q₁.cutCarrier = A ∧ N ∪ Q₁.cutCarrier = R ∧
      (U.map '' closedTube r) ∩ Q₁.cutCarrier = ⋃ i : Bool × Bool, U.map '' panel r (w/2) i ∧
      (∀ b, (P b).closedStrip ∩ Q₁.cutCarrier = (P b).endDisks) ∧
      (∀ x ∈ U.map '' closedTube r, x ∈ Q₁.cutCarrier ↔
        x ∈ ⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∧
      ∀ b x, x ∈ (P b).closedStrip → (x ∈ Q₁.cutCarrier ↔ x ∈ (P b).endDisks) := by
  dsimp only
  have hr : 0 < r := (hρ false).trans (hρr false)
  have hQ := TubeExterior.OriginalIntervalTube.isCompact_exterior U hR he hr hr1
  obtain ⟨hc₀,_,hf₀,hi₀,hu₀,_⟩ := (P false).cut_geometry hQ hopen₀
  obtain ⟨_,_,hf₁,hi₁,hu₁,_⟩ := Q₁.cut_geometry hc₀ hopen₁
  obtain ⟨_,_,htube,hstrips,hcover⟩ :=
    TubeExterior.OriginalIntervalTube.final_frontier_inventory U hR he hr hr1
      (P false) Q₁ hdis hf₀ hf₁ hi₀ hu₀ hi₁ hu₁
  have hopenEq : Q₁.openStrip = (P true).openStrip := by
    simp only [OriginalDiskProduct.openStrip,hmap]
  have hendEq : Q₁.endDisks = (P true).endDisks := by
    simp only [OriginalDiskProduct.endDisks,hmap]
  have hclosedEq : Q₁.closedStrip = (P true).closedStrip := by
    simp only [OriginalDiskProduct.closedStrip,hmap]
  rw [hopenEq,lateral_sdiff_two_openStrips U hR he hw hr1 P F ρ hρ hρr
    hwρ hmark harms hlateral] at htube
  rw [← BoundaryInventory.endDisks_eq_slice_images,← BoundaryInventory.endDisks_eq_slice_images,
    hclosedEq,hendEq] at hstrips
  rw [hclosedEq] at hcover
  have hfirst : (P false).closedStrip ∩ Q₁.cutCarrier = (P false).endDisks := by
    have hendsub : (P false).endDisks ⊆ (P false).closedStrip := by
      rw [← (P false).closedStrip_sdiff_openStrip]
      exact sdiff_subset
    have hopenSub : Q₁.openStrip ⊆ Q₁.closedStrip :=
      image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
    ext x
    constructor
    · intro hx
      exact hi₀.subset ⟨hx.1,hx.2.1⟩
    · intro hx
      have hh := hi₀.symm.subset hx
      exact ⟨hh.1,hh.2,fun hopen ↦ disjoint_left.mp hdis (hendsub hx) (hopenSub hopen)⟩
  have hsingle (b : Bool) : (P b).closedStrip ∩ Q₁.cutCarrier = (P b).endDisks := by
    cases b
    · exact hfirst
    · simpa only [hclosedEq,hendEq] using hi₁
  refine ⟨?_,hcover,htube,hsingle,?_,?_⟩
  · rw [union_inter_distrib_right,htube,hstrips]
  · intro x hx
    exact ⟨fun hy ↦ htube.subset ⟨hx,hy⟩,fun hy ↦ (htube.symm.subset hy).2⟩
  · intro b x hx
    exact ⟨fun hy ↦ (hsingle b).subset ⟨hx,hy⟩,fun hy ↦ ((hsingle b).symm.subset hy).2⟩

end PoincareConjecture.M76.Dehn.Annuli.BoundaryAssembly
