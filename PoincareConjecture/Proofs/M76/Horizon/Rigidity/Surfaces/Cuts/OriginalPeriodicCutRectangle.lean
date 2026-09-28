import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutBoundaryFibers
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrescribedRectangle
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutRectangle
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalCutCornerConnectivity

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
  (hbound : ∀ s ∈ K.faces, s.card ≤ 3)

local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => PeriodicSquare.squareCarrier 1

include hbound

theorem exists_matched_original_rectangle
    (hrev : ∀ i : Fin 4, (A.sourceMap) (A.bridgeBegin (A.arcPairing i)) =
      (A.sourceMap) (A.bridgeEnd i)) :
    ∃ (C : Sq ≃ₜ A.carrier)
      (H : A.longBoundaryArc 0 ≃ₜ A.longBoundaryArc 2)
      (G : A.longBoundaryArc 3 ≃ₜ A.longBoundaryArc 1)
      (e : I ≃ₜ A.longBoundaryArc 0) (d : I ≃ₜ A.longBoundaryArc 3),
      C.IsFinitePL ∧
      (∀ p, (A.sourceMap) (H p) = (A.sourceMap) p) ∧
      (∀ p, (A.sourceMap) (G p) = (A.sourceMap) p) ∧
      (∀ t : I, (C ⟨(t, 0), t.property, by norm_num⟩).val = e t) ∧
      (∀ t : I, (C ⟨(t, 1), t.property, by norm_num⟩).val = H (e t)) ∧
      (∀ t : I, (C ⟨(0, t), by norm_num, t.property⟩).val = d t) ∧
      (∀ t : I, (C ⟨(1, t), by norm_num, t.property⟩).val = G (d t)) := by
  have hop := A.arcPairing_opposite_of_source_reversal hrev
  have hp0 : A.arcPairing 0 = 2 := hop 0
  have hp3 : A.arcPairing 3 = 1 := hop 3
  have hexH := A.exists_reversing_longBoundaryArc_pairing hbound 0 (hrev 0)
  have hexG := A.exists_reversing_longBoundaryArc_pairing hbound 3 (hrev 3)
  rw [hp0] at hexH
  rw [hp3] at hexG
  obtain ⟨H, hH, hvH, hsH, htH, _⟩ := hexH
  obtain ⟨G, hG, hvG, hsG, htG, _⟩ := hexG
  have hcover : (A.longBoundaryArc 0 ∪ A.longBoundaryArc 2) ∪
      (A.longBoundaryArc 3 ∪ A.longBoundaryArc 1) = A.rim := by
    rw [← A.longBoundaryArcs_cover]
    ext p
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro ((h | h) | (h | h))
      · exact ⟨0, h⟩
      · exact ⟨2, h⟩
      · exact ⟨3, h⟩
      · exact ⟨1, h⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> tauto
  have hM : IsFinitePLBallPair (ℝ × ℝ) A.carrier
      ((A.longBoundaryArc 0 ∪ A.longBoundaryArc 2) ∪
        (A.longBoundaryArc 3 ∪ A.longBoundaryArc 1)) := hcover.symm ▸ A.disk
  have hW := A.longBoundaryArc_isFinitePLInterval hbound 0
  have hL := A.longBoundaryArc_isFinitePLInterval hbound 3
  have hWL := A.longBoundaryArc_inter_next hbound 3
  have hWR := A.longBoundaryArc_inter_next hbound 0
  have hZL := A.longBoundaryArc_inter_next hbound 2
  have hZR := A.longBoundaryArc_inter_next hbound 1
  have hWZ := A.longBoundaryArc_disjoint_opposite hbound 0
  have hLR := A.longBoundaryArc_disjoint_opposite hbound 3
  simp only [show (0 : Fin 4) - 1 = 3 from rfl,
    show (3 : Fin 4) - 1 = 2 from rfl, show (3 : Fin 4) + 1 = 0 from rfl,
    show (0 : Fin 4) + 1 = 1 from rfl, show (2 : Fin 4) + 1 = 3 from rfl,
    show (1 : Fin 4) + 1 = 2 from rfl, show (0 : Fin 4) + 2 = 2 from rfl,
    show (3 : Fin 4) + 2 = 1 from rfl] at hW hL hWL hWR hZL hZR hWZ hLR
  have hL' : IsFinitePLBallPair ℝ (A.longBoundaryArc 3)
      {A.gapCenter 3, A.gapCenter 2} := by rw [Set.pair_comm]; exact hL
  obtain ⟨C, e, d, hC, _, _, hw, hz, hl, hr⟩ := exists_rectangle_respecting_pairings
    (p₀ := A.gapCenter 3) (p₁ := A.gapCenter 0)
    (q₀ := A.gapCenter 2) (q₁ := A.gapCenter 1)
    hM hW hL' (A.gapCenters_injective.ne (by decide : (3 : Fin 4) ≠ 0))
    (A.gapCenters_injective.ne (by decide : (3 : Fin 4) ≠ 2)) H G hH hG
    (congrArg Subtype.val hsH) (congrArg Subtype.val htH)
    (congrArg Subtype.val htG) (congrArg Subtype.val hsG)
    hWZ hLR (by simpa only [inter_comm] using hWL) hWR hZL
    (by simpa only [inter_comm] using hZR)
  exact ⟨C, H, G, e, d, hC, hvH, hvG, hw, hz, hl, hr⟩

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData
