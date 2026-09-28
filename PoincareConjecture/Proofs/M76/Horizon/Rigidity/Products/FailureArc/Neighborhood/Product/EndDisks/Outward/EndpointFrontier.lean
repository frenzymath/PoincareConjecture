import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.Outward.PanelRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.Outward.RegularOpen
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.NeighborhoodFrontier

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution ProductPieces
open BoundaryAssembly

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem endpoint_neighborhood_regular_open
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r w : ℝ} (hw : 0 < w) (hr1 : r < 1)
    {j : Bool → V2 → X}
    (P : ∀ b, OriginalDiskProduct e (R \ U.map '' openTube r) (j b))
    (F : Bool → V2 × ℝ → X) (ρ : Bool → ℝ)
    (hρ : ∀ b, 0 < ρ b) (hρr : ∀ b, ρ b < r) (hwρ : ∀ b, w / ρ b ≤ 1)
    (hmark : ∀ b, ∀ z ∈ Rim, ∀ s ∈ J,
      (P b).map (z,s) = F b (z,(w / ρ b)*s))
    (harms : ∀ side b : Bool, ∀ t ∈ I, ∀ s ∈ J,
      F side (rimArmPoint b t,s) = prescribedArmBand U r (ρ side) 0 1 side b (s,t))
    (hlateral : ∀ side, ∀ z ∈ Rim, ∀ s ∈ J,
      F side (z,s) ∈ U.map '' lateral r ↔ ∃ b : Bool, ∃ t ∈ I, z = rimArmPoint b t)
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (hopen : ∀ b v, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹'
        ((P b).map '' (Disk ×ˢ Ioo (-v) v))))
    (hdistinct : connectedComponentIn (frontier R) (U.map ((0,0),0)) ≠
      connectedComponentIn (frontier R) (U.map ((0,0),1)))
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    let Z := connectedComponentIn (frontier R) (U.map ((0,0),t))
    let O := (Subtype.val : Z → X) ⁻¹' removedLongitudinalSlice U r P t
    let N := (Subtype.val : Z → X) ⁻¹'
      (⋃ i, range (fun z => pieceParameter U P r i (z,t)))
    IsOpen O ∧ closure O = N ∧ interior N = O ∧
      frontier N = (Subtype.val : Z → X) ⁻¹'
        (⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {(t : ℝ)})) ∧
      closure Nᶜ = Oᶜ := by
  dsimp only
  let Z := connectedComponentIn (frontier R) (U.map ((0,0),t))
  let O := (Subtype.val : Z → X) ⁻¹' removedLongitudinalSlice U r P t
  obtain ⟨hO,hclosure,hfront⟩ := removed_longitudinal_slice_relative_frontier U hR he
    hw hr1.le P F ρ hρ hρr hwρ hmark harms hlateral hr1 hdis hopen hdistinct t ht
  have hout := panel_rim_subset_closure_component_complement U hR he hw hr1
    P F ρ hρ hρr hwρ hmark harms hlateral hdis t ht
  have hslice := closed_neighborhood_inter_component U hR he hw hr1.le P F ρ hρ
    hρr hwρ hmark harms hlateral hdistinct t ht
  rw [ProductConstruction.pieceParameter_range U P] at hslice
  have hpre : (Subtype.val : Z → X) ⁻¹'
      (U.map '' closedTube r ∪ ((P false).closedStrip ∪ (P true).closedStrip)) =
      Subtype.val ⁻¹' (⋃ i, range (fun z => pieceParameter U P r i (z,t))) := by
    ext x
    exact ⟨fun hx => hslice.subset ⟨hx,x.property⟩,
      fun hx => (hslice.symm.subset hx).1⟩
  have hout' : frontier O ⊆ closure (closure O)ᶜ := by
    rw [hfront,hclosure,← hpre]
    simpa only [preimage_compl] using hout
  refine ⟨hO,hclosure,?_,?_,?_⟩
  · rw [← hclosure]
    exact interior_closure_eq_of_frontier_outward_density hO hout'
  · rw [← hclosure,frontier_closure_eq_of_frontier_outward_density hO hout',hfront]
  · rw [← hclosure]
    exact closure_compl_closure_eq_of_frontier_outward_density hO hout'

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
