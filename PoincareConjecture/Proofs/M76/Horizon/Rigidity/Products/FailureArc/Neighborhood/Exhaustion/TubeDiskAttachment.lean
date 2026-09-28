import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Exhaustion.ComponentReattachment
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Boundary.FinalFrontier

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open TubeExterior PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem final_cut_component_eq_of_attachment_faces
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X} {j₀ j₁ : V2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R) (hconn : IsPreconnected R)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (P₀ : OriginalDiskProduct e (R \ U.map '' openTube r) j₀)
    (P₁ : OriginalDiskProduct e P₀.cutCarrier j₁)
    (hdis : Disjoint P₀.closedStrip P₁.closedStrip)
    (hopen₀ : IsOpen ((Subtype.val : ↥(R \ U.map '' openTube r) → X) ⁻¹' P₀.openStrip))
    (hopen₁ : IsOpen ((Subtype.val : P₀.cutCarrier → X) ⁻¹' P₁.openStrip))
    (hecut : PLDomain e P₁.cutCarrier) {x : X} (hx : x ∈ P₁.cutCarrier)
    (hlateral : U.map '' lateral r \ (P₀.openStrip ∪ P₁.openStrip) ⊆
      connectedComponentIn P₁.cutCarrier x)
    (hend : P₀.endDisks ∪ P₁.endDisks ⊆ connectedComponentIn P₁.cutCarrier x) :
    connectedComponentIn P₁.cutCarrier x = P₁.cutCarrier := by
  have hQ := TubeExterior.OriginalIntervalTube.isCompact_exterior U hR he hr hr1
  obtain ⟨hc₀,_,hf₀,hi₀,hu₀,_⟩ := P₀.cut_geometry hQ hopen₀
  obtain ⟨hc₁,_,hf₁,hi₁,hu₁,_⟩ := P₁.cut_geometry hc₀ hopen₁
  obtain ⟨_,_,htube,hstrip,hcover⟩ :=
    TubeExterior.OriginalIntervalTube.final_frontier_inventory U hR he hr hr1
      P₀ P₁ hdis hf₀ hf₁ hi₀ hu₀ hi₁ hu₁
  have hclosedTube : IsClosed (U.map '' closedTube r) :=
    ((isCompact_closedTube r).image_of_continuousOn
      (U.pl.continuousOn.mono (closedTube_subset hr1))).isClosed
  have hclosed₀ : IsClosed P₀.closedStrip :=
    (P₀.isCompact_closed_strip (by norm_num : (1/2 : ℝ) ≤ 1)).isClosed
  have hclosed₁ : IsClosed P₁.closedStrip :=
    (P₁.isCompact_closed_strip (by norm_num : (1/2 : ℝ) ≤ 1)).isClosed
  apply connectedComponent_eq_of_all_attachment_faces hconn
    (hclosedTube.union (hclosed₀.union hclosed₁)) hc₁ hecut hx hcover
  rw [union_inter_distrib_right,htube,hstrip,
    ← BoundaryInventory.endDisks_eq_slice_images,← BoundaryInventory.endDisks_eq_slice_images]
  exact union_subset hlateral hend

end PoincareConjecture.M76.Dehn.Annuli
