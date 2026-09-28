import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Restriction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.PanelMaps

set_option autoImplicit false
noncomputable section
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductPieces
open TubeExterior PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

def tubePiece (U : OriginalIntervalTube e R W S T C D f₀ f₁) : C3 → X := U.map

theorem tubePiece_properties (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    PolyhedralPLInCharts e (tubePiece U) (transverseSquare r ×ˢ I) ∧
      IsEmbedding (fun p : transverseSquare r ×ˢ I => tubePiece U p) ∧
      MapsTo (tubePiece U) (transverseSquare r ×ˢ I) R ∧
      tubePiece U '' (transverseSquare r ×ˢ I) = U.map '' closedTube r ∧
      (∀ p ∈ transverseSquare r ×ˢ I, tubePiece U p ∈ frontier R ↔ p.2 = 0 ∨ p.2 = 1) := by
  have hsub := closedTube_subset hr1
  have hPL := (TubeExterior.OriginalIntervalTube.restrict_closedTube U hr hr1).1
  let : CompactSpace (closedTube r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedTube r)
  have hinj : InjOn (tubePiece U) (transverseSquare r ×ˢ I) := by
    intro p hp q hq hpq
    exact congrArg Subtype.val (U.embedding.injective
      (a₁ := ⟨p,hsub hp⟩) (a₂ := ⟨q,hsub hq⟩) hpq)
  refine ⟨hPL,(hPL.continuousOn.domRestrict.isClosedEmbedding
    (fun p q h => Subtype.ext (hinj p.property q.property h))).isEmbedding,
    ?_,rfl,fun p hp => U.frontier_iff p (hsub hp)⟩
  exact fun p hp => U.mapsTo_region (hsub hp)

omit [T2Space X] in
theorem tubePiece_depth_image (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (r t : ℝ) :
    tubePiece U '' (transverseSquare r ×ˢ {t}) = U.map '' (transverseSquare r ×ˢ {t}) := rfl

omit [T2Space X] in
theorem tubePiece_band (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (r : ℝ) (i : Bool × Bool) (s t : ℝ) :
    tubePiece U (CornerBands.arcMap r i s,t) = CornerBands.originalBandMap U r i (s,t) := rfl

omit [T2Space X] in
theorem tubePiece_panel (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (r : ℝ) (i : Bool × Bool) (p : P2) :
    tubePiece U (CornerBands.panelAffine r i p) = CornerBands.originalPanelMap U r i p := rfl

end PoincareConjecture.M76.Dehn.Annuli.ProductPieces
