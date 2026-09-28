import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalBoundaryOrientationConsumer

set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}
  (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)

local notation "CutSpace" => (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)
local notation "sm" => A.sourceMap K P D hD hcofaces hP labels

theorem scalar_bridge_chart
    (i : Fin 4) (f : (ℝ × ℝ) → CutSpace)
    (hfPL : FinitePiecewiseAffineOn f (PeriodicSquare.squareCarrier 1))
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    (himage : (f ∘ unitSquareSide i) '' Icc α β = A.boundaryBridge i)
    (hsourceInj : InjOn (sm ∘ (f ∘ unitSquareSide i)) (Icc α β))
    (ell : E →L[ℝ] ℝ)
    (helli : InjOn ell (range (AffineMap.lineMap
      (((A.bands (A.bridgeLabelling i).1).ends 0).val)
      (((A.bands (A.bridgeLabelling i).1).ends 1).val) : ℝ → E))) :
    ContinuousOn (fun r => ell (sm (f (unitSquareSide i r)))) (Icc α β) ∧
      InjOn (fun r => ell (sm (f (unitSquareSide i r)))) (Icc α β) := by
  have hsub : Icc α β ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc hα.le hβ.le
  have hs := ((unitSquareSide_isFinitePL i).continuousOn).mono hsub
  have hf := hfPL.continuousOn.comp hs (fun r hr => unitSquareSide_mem_square i (hsub hr))
  have hcont : Continuous (fun p : CutSpace => ell (sm p)) := by
    change Continuous (fun p : CutSpace => ell p.1.1)
    fun_prop
  refine ⟨hcont.comp_continuousOn hf, ?_⟩
  have hrange (r : ℝ) (hr : r ∈ Icc α β) :
      sm (f (unitSquareSide i r)) ∈ range (AffineMap.lineMap
        (((A.bands (A.bridgeLabelling i).1).ends 0).val)
        (((A.bands (A.bridgeLabelling i).1).ends 1).val) : ℝ → E) := by
    have hb : f (unitSquareSide i r) ∈ A.boundaryBridge i :=
      himage.subset (mem_image_of_mem _ hr)
    have hp := (A.sourceMap_boundaryBridge i).subset (mem_image_of_mem sm hb)
    have he := residualBridge_subset_openEdge K _
      (A.bands (A.bridgeLabelling i).1).edge_eq hp
    rw [openSegment_eq_image_lineMap] at he
    exact image_subset_range _ _ he
  intro r hr s hs heq
  exact hsourceInj hr hs (helli (hrange r hr) (hrange s hs) heq)

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData
