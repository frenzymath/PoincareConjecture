import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalExteriorGaps









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
  (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
  (B : ∀ s : ResidualComplementaryEdge K P D,
    OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
  (labels : ResidualComplementaryEdge K P D ≃ Fin 2)

noncomputable def originalExteriorMarks (i : Fin 4) : E :=
  let j := exteriorFourIndex K P D labels i
  primalEdgeMark K (complementaryOriginalEdge K P hcofaces j.1.val) ((B j.1).ends j.2)

omit [Fintype K.barycentricSubdivision.faces] in
theorem residualOriginalEdge_injective :
    Function.Injective (fun s : ResidualComplementaryEdge K P D =>
      complementaryOriginalEdge K P hcofaces s.val) := by
  intro s t he
  apply Subtype.ext
  apply (complementaryTriangleEdgeEquiv K.vertexAbstractComplex.toPreAbstractSimplicialComplex P
    (originalTriangleCofaceCounts K hcofaces)).injective
  exact Subtype.ext he

private theorem band_end_mem (s : ResidualComplementaryEdge K P D) (i : Fin 2) :
    (B s).ends i ∈ (complementaryOriginalEdge K P hcofaces s.val).val := by
  fin_cases i <;> simp [(B s).edge_eq]

private theorem band_ends_injective (s : ResidualComplementaryEdge K P D) :
    Function.Injective (B s).ends := by
  intro i j he
  fin_cases i <;> fin_cases j
  · rfl
  · exact ((B s).ends_ne he).elim
  · exact ((B s).ends_ne he.symm).elim
  · rfl

theorem originalExteriorMarks_injective :
    Function.Injective (originalExteriorMarks K P D hcofaces B labels) := by
  have hflags : Function.Injective (fun i : ResidualHalfBandIndex K P D =>
      primalEdgeMark K (complementaryOriginalEdge K P hcofaces i.1.val) ((B i.1).ends i.2)) := by
    rintro ⟨s,i⟩ ⟨t,j⟩ he
    have hst : s = t := by
      by_contra hne
      exact primalEdgeMark_ne K _ _ _ _
        (band_end_mem K P D hcofaces B s i) (band_end_mem K P D hcofaces B t j)
        (Or.inl (fun h => hne (residualOriginalEdge_injective K P D hcofaces h))) he
    subst t
    have hij : i = j := by
      by_contra hne
      exact primalEdgeMark_ne K _ _ _ _
        (band_end_mem K P D hcofaces B s i) (band_end_mem K P D hcofaces B s j)
        (Or.inr (fun h => hne (band_ends_injective K P D hcofaces B s h))) he
    exact Prod.ext rfl hij
  exact hflags.comp (exteriorFourIndex K P D labels).injective

theorem originalExteriorMarks_apply_inverse (s : ResidualComplementaryEdge K P D) (j : Fin 2) :
    originalExteriorMarks K P D hcofaces B labels
        ((exteriorFourIndex K P D labels).symm (s,j)) =
      primalEdgeMark K (complementaryOriginalEdge K P hcofaces s.val) ((B s).ends j) := by
  unfold originalExteriorMarks
  dsimp only
  rw [(exteriorFourIndex K P D labels).apply_symm_apply (s,j)]

theorem originalExteriorMarks_range :
    range (originalExteriorMarks K P D hcofaces B labels) =
      residualQuarterMarks K P D hcofaces B := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    let j := exteriorFourIndex K P D labels i
    apply mem_iUnion.mpr
    refine ⟨j.1,?_⟩
    change primalEdgeMark K (complementaryOriginalEdge K P hcofaces j.1.val)
      ((B j.1).ends j.2) ∈ _
    generalize hj : j.2 = k
    fin_cases k <;> simp
  · intro hx
    obtain ⟨s,hs⟩ := mem_iUnion.mp hx
    rcases hs with hs | hs
    · refine ⟨(exteriorFourIndex K P D labels).symm (s,0),?_⟩
      exact (originalExteriorMarks_apply_inverse K P D hcofaces B labels s 0).trans hs.symm
    · refine ⟨(exteriorFourIndex K P D labels).symm (s,1),?_⟩
      have hs' : x = primalEdgeMark K (complementaryOriginalEdge K P hcofaces s.val)
        ((B s).ends 1) := hs
      exact (originalExteriorMarks_apply_inverse K P D hcofaces B labels s 1).trans hs'.symm

theorem originalExteriorMarks_mem_primalRim
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph) (i : Fin 4) :
    originalExteriorMarks K P D hcofaces B labels i ∈
      K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) := by
  let j := exteriorFourIndex K P D labels i
  apply primalEdgeMark_mem_rim K P hP
  · exact (complementaryTriangleEdgeEquiv K.vertexAbstractComplex.toPreAbstractSimplicialComplex P
      (originalTriangleCofaceCounts K hcofaces) j.1.val).property
  · exact band_end_mem K P D hcofaces B j.1 j.2

theorem exteriorCopiedMark_projection_originalExteriorMarks
    (h : ResidualHalfBandIndex K P D → E → ℝ)
    (i : ResidualHalfBandIndex K P D) (j : Fin 2) :
    (exteriorCopiedMark K P D hcofaces B h i j).1 =
      originalExteriorMarks K P D hcofaces B labels
        ((exteriorFourIndex K P D labels).symm (i.1,j)) := by
  exact (originalExteriorMarks_apply_inverse K P D hcofaces B labels i.1 j).symm



theorem nonempty_originalExteriorPrimalSectors
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph) (hPtree : P.IsTree) :
    Nonempty (OriginalPrimalSectorDecomposition
      (K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP))
      (K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP))
      (originalExteriorMarks K P D hcofaces B labels)) :=
  exists_original_primal_sector_decomposition
    (primalTreeNeighborhood_isFinitePLBallPair K hpure hcofaces hlinks P hP hPtree)
    _ (originalExteriorMarks_injective K P D hcofaces B labels)
    (originalExteriorMarks_mem_primalRim K P D hcofaces B labels hP)

end PoincareConjecture.M76.OriginalTriangleCopies
