import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalPrimalCutDisk
import PoincareConjecture.Proofs.M76.Mathlib.NestedPLBallBoundary

set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  (P : SimpleGraph K.vertices)
  (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
  (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
  (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
  [Fintype (ResidualComplementaryEdge K P D)]
  (B : ∀ s : ResidualComplementaryEdge K P D,
    OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
  (h : ResidualHalfBandIndex K P D → E → ℝ)
  (labels : ResidualComplementaryEdge K P D ≃ Fin 2)
  (C : ExteriorGapCoordinates K P D hD hcofaces B h labels)

theorem exteriorGap_inter_bridgeCopies (i : Fin 4) :
    C.gap i ∩ complementaryBridgeCopies K P D hcofaces B h =
      {C.bridgeFinish i,C.bridgeStart (i+1)} := by
  apply Subset.antisymm
  · intro z hz
    by_contra he
    exact Set.disjoint_left.mp
      (exteriorGapInterior_disjoint_copies K P D hD hcofaces B h labels C i)
      ⟨hz.1,he⟩ hz.2
  · intro z hz
    have hcopied {k : Fin 4}
        (hx : z ∈ exteriorCopiedBridge K P D hcofaces B h
          (exteriorFourIndex K P D labels k)) :
        z ∈ complementaryBridgeCopies K P D hcofaces B h := by
      exact mem_iUnion₂.mpr ⟨(exteriorFourIndex K P D labels k).1,
        (exteriorFourIndex K P D labels k).2,hx⟩
    rcases hz with he | he
    · have hc := (C.gap_inter_bridge_cyclic_iff i i z).mpr (Or.inl ⟨rfl,he⟩)
      exact ⟨hc.1,hcopied hc.2⟩
    · have hc := (C.gap_inter_bridge_cyclic_iff i (i+1) z).mpr (Or.inr ⟨rfl,he⟩)
      exact ⟨hc.1,hcopied hc.2⟩

theorem complementaryCutRim_eq_bridgeCopies_union_gaps :
    complementaryCutRim K P D hD hcofaces B h =
      complementaryBridgeCopies K P D hcofaces B h ∪ ⋃ i : Fin 4,C.gap i := by
  apply Subset.antisymm
  · intro z hz
    rcases C.gaps_cover.symm.subset hz with ⟨i,hi⟩ | ⟨i,hi⟩
    · exact Or.inl (mem_iUnion₂.mpr ⟨(exteriorFourIndex K P D labels i).1,
        (exteriorFourIndex K P D labels i).2,hi⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨i,hi⟩)
  · rintro z (hz | hz)
    · obtain ⟨s,j,hz⟩ := mem_iUnion₂.mp hz
      apply C.gaps_cover.subset
      left
      refine ⟨(exteriorFourIndex K P D labels).symm (s,j),?_⟩
      rw [(exteriorFourIndex K P D labels).apply_symm_apply (s,j)]
      exact hz
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      exact C.gap_subset i hi

variable (hP : P ≤ K.vertexAbstractComplex.edgeGraph)

theorem OriginalPrimalCutDiskData.sectorGraph_endpoints
    (T : OriginalPrimalCutDiskData K P D hD hcofaces hP labels) (i : Fin 4) :
    ({heightGraph (T.sectorHeight i)
        (originalExteriorMarks K P D hcofaces T.bands labels (T.sectors.order i)),
      heightGraph (T.sectorHeight i)
        (originalExteriorMarks K P D hcofaces T.bands labels (T.sectors.order (i+1)))} : Set _) =
      {T.gaps.bridgeFinish (T.matching.symm i),
        T.gaps.bridgeStart (T.matching.symm i+1)} := by
  have hsub : T.sectors.rim i ⊆ T.sectors.sector i :=
    subset_union_left.trans (T.sectors.sector_ball i).1
  have hgraph := (T.sectors.rim_ball i).image_of_subset
    (heightGraph_finitePL (T.sectorHeightPL i)) hsub
    (heightGraph_injective (T.sectorHeight i)).injOn
  simp only [image_pair] at hgraph
  rw [T.sectorGraph_eq_gap i] at hgraph
  exact hgraph.boundary_eq_of_same_carrier
    (T.gaps.gap_isFinitePLBallPair_cyclic (T.matching.symm i))

theorem OriginalPrimalCutDiskData.bridgeCopies_inter_sectorGraph
    (T : OriginalPrimalCutDiskData K P D hD hcofaces hP labels) (i : Fin 4) :
    complementaryBridgeCopies K P D hcofaces T.bands T.exteriorHeight ∩
        heightGraph (T.sectorHeight i) '' T.sectors.rim i =
      {heightGraph (T.sectorHeight i)
        (originalExteriorMarks K P D hcofaces T.bands labels (T.sectors.order i)),
      heightGraph (T.sectorHeight i)
        (originalExteriorMarks K P D hcofaces T.bands labels (T.sectors.order (i+1)))} := by
  rw [T.sectorGraph_eq_gap i,inter_comm,
    exteriorGap_inter_bridgeCopies K P D hD hcofaces T.bands T.exteriorHeight labels T.gaps]
  exact (T.sectorGraph_endpoints K P D hD hcofaces labels hP i).symm

end PoincareConjecture.M76.OriginalTriangleCopies
