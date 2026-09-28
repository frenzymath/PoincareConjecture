import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.RemovedComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.RemovedAvoidance
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.NeighborhoodFrontier

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
open TubeExterior TubeExterior.CornerBands RimBands PolygonalCrossingResolution
open BoundaryAssembly ProductPieces

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1

theorem endpoint_complement_contacts
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
    (hdis : Disjoint ((P false).map '' (Disk ×ˢ J)) ((P true).map '' (Disk ×ˢ J)))
    (hdistinct : connectedComponentIn (frontier R) (U.map ((0,0),0)) ≠
      connectedComponentIn (frontier R) (U.map ((0,0),1)))
    (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    let Z := connectedComponentIn (frontier R) (U.map ((0,0),t))
    let B := Z \ removedLongitudinalSlice U r P t
    ((⋃ i : Bool × Bool, U.map '' panel r (w/2) i) ∪
      ((P false).endDisks ∪ (P true).endDisks)) ∩ B =
        ⋃ i, panelFamily U (P false) (P true) r w i '' (I ×ˢ {(t : ℝ)}) ∧
    B ⊆ frontier R \ (U.map '' openTube r ∪ (P false).openStrip ∪ (P true).openStrip) ∧
    (⋃ i, range (fun z => pieceParameter U P r i (z,t))) ∪ B = Z := by
  dsimp only
  have hr : 0 < r := (hρ false).trans (hρr false)
  have hwr : w/2 < r := by
    have h := (div_le_iff₀ (hρ false)).mp (hwρ false)
    linarith [hρr false]
  have hslice := removed_neighborhood_inter_component U hR he hw hr1 P F ρ hρ hρr
    hwρ hmark harms hlateral hdistinct t ht
  have hAnn := final_panel_annulus_inter_component_eq_rim U hR he hw hr1 P F ρ hρ hρr
    hwρ hmark harms hlateral hwr hdistinct t ht
  have havoid := final_panel_annulus_disjoint_removed U hR he hw hr1 P F ρ hρ hρr
    hwρ hmark harms hlateral hdis
  refine ⟨?_,?_,?_⟩
  · apply Subset.antisymm
    · exact fun x hx => hAnn.subset ⟨hx.1,hx.2.1⟩
    · intro x hx
      obtain ⟨hxA,hxZ⟩ := hAnn.symm.subset hx
      refine ⟨hxA,hxZ,?_⟩
      intro hxO
      exact disjoint_left.mp havoid hxA (hslice.symm.subset hxO).1
  · intro x hx
    exact ⟨connectedComponentIn_subset _ _ hx.1,fun hxO =>
      hx.2 (hslice.subset ⟨hxO,hx.1⟩)⟩
  · apply Subset.antisymm
    · exact union_subset
        (closed_longitudinal_slice_subset_component U hR he hw hr1 P F ρ hρ hρr
          hwρ hmark harms hlateral t ht) sdiff_subset
    · intro x hx
      by_cases hxO : x ∈ removedLongitudinalSlice U r P t
      · exact Or.inl ((closure_removed_longitudinal_slice U hr hr1 P t).subset
          (subset_closure hxO))
      · exact Or.inr ⟨hx,hxO⟩

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
