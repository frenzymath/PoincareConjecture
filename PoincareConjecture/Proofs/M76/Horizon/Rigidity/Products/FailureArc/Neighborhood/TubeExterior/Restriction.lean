import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.SourceBox

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem OriginalIntervalTube.restrict_closedTube
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    PolyhedralPLInCharts e (fun z : C3 => U.map z) (closedTube r) ∧
    InjOn U.map (closedTube r) ∧ MapsTo U.map (closedTube r) R ∧
    MapsTo U.map (closedTube r) W ∧
    (∀ z ∈ closedTube r, U.map z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1) := by
  have hsub := closedTube_subset hr1
  obtain ⟨_, ⟨_,_,_,_, c, hc, _⟩⟩ := isFinitePLBallPair_closedTube hr
  obtain ⟨_, ⟨K,hK,hKs,_⟩, _⟩ := hc
  have hpl : PolyhedralPLInCharts e U.map (closedTube r) := by
    rw [← hKs]
    exact U.pl.restrict_finite K hK (hKs.subset.trans hsub)
  refine ⟨hpl,?_,?_,?_,?_⟩
  · intro x hx
    intro y hy hxy
    exact congrArg Subtype.val (U.embedding.injective (a₁ := ⟨x,hsub hx⟩)
      (a₂ := ⟨y,hsub hy⟩) hxy)
  · intro x hx
    exact U.mapsTo_region (hsub hx)
  · intro x hx
    exact U.mapsTo_neighborhood (hsub hx)
  · exact fun z hz => U.frontier_iff z (hsub hz)

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
