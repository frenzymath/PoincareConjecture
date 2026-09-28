import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalSectorAttachmentFibers
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ExteriorBridgeGapContacts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutFibers








set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {d q : Set E} {marks : Fin 4 → E}
  (C : OriginalPrimalSectorDecomposition d q marks)
  (g : Fin 4 → E → F) (k : Fin 4 → (E × F) → ℝ)

theorem OriginalPrimalSectorDecomposition.attached_rim_eq
    {b R : Set (E × F)}
    (hz : ∀ i x, x ∈ C.sector i →
      (k i (heightGraph (g i) x) = 0 ↔ x ∈ C.rim i))
    (hdis : Pairwise (fun i j ↦ Disjoint (heightGraph (g i) '' C.rim i)
      (heightGraph (g j) '' C.rim j)))
    (hcover : b = R ∪ ⋃ i, heightGraph (g i) '' C.rim i)
    (hcontact : ∀ i, R ∩ heightGraph (g i) '' C.rim i =
      {heightGraph (g i) (marks (C.order i)),
        heightGraph (g i) (marks (C.order (i + 1)))}) :
    graphAttachmentRim g k b (fun i ↦ C.rim i ∪ (C.spoke i ∪ C.spoke (i + 1)))
      C.rim (fun i ↦ marks (C.order i)) (fun i ↦ marks (C.order (i + 1))) =
      zeroSheet '' R ∪ ⋃ i,
        graphAttachmentSheet g k i '' (C.spoke i ∪ C.spoke (i + 1)) := by
  classical
  have hzero (i : Fin 4) {x : E} (hx : x ∈ C.rim i) :
      graphAttachmentSheet g k i x = zeroSheet (ι := Fin 4) (heightGraph (g i) x) := by
    apply (separatedSheet_eq_zeroSheet_iff k i _ _).mpr
    exact ⟨rfl, (hz i x ((C.sector_ball i).1 (Or.inl hx))).mpr hx⟩
  apply Subset.antisymm
  · intro z hzrim
    have hsurvive := hzrim.2
    have hatt (i : Fin 4) {x : E} (hx : x ∈ C.rim i)
        (heq : z = zeroSheet (ι := Fin 4) (heightGraph (g i) x)) :
        z ∈ ⋃ j, graphAttachmentSheet g k j '' (C.spoke j ∪ C.spoke (j + 1)) := by
      have hends : x = marks (C.order i) ∨ x = marks (C.order (i + 1)) := by
        by_contra hn
        apply hsurvive
        refine mem_iUnion₂.mpr ⟨i, Finset.mem_univ _, ?_⟩
        rw [heq]
        refine ⟨⟨heightGraph (g i) x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
        rintro (he | he)
        · exact hn (Or.inl (congrArg (fun p : (E × F) × (Fin 4 → ℝ) ↦ p.1.1) he))
        · exact hn (Or.inr (congrArg (fun p : (E × F) × (Fin 4 → ℝ) ↦ p.1.1) he))
      refine mem_iUnion.mpr ⟨i, x, ?_, (hzero i hx).trans heq.symm⟩
      rcases hends with he | he
      · exact Or.inl (he ▸ (C.spoke_ball i).1 (Or.inr rfl))
      · exact Or.inr (he ▸ (C.spoke_ball (i + 1)).1 (Or.inr rfl))
    rcases hzrim.1 with hbase | hsheet
    · obtain ⟨y, hy, rfl⟩ := hbase
      rw [hcover] at hy
      rcases hy with hy | hy
      · exact Or.inl ⟨y, hy, rfl⟩
      · obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hy
        exact Or.inr (hatt i hx rfl)
    · obtain ⟨i, _, y, ⟨x, hx, rfl⟩, rfl⟩ := mem_iUnion₂.mp hsheet
      rcases hx with hx | hx
      · exact Or.inr (hatt i hx (hzero i hx))
      · exact Or.inr (mem_iUnion.mpr ⟨i, x, hx, rfl⟩)
  · rintro z (hbase | hsector)
    · obtain ⟨x, hxR, rfl⟩ := hbase
      refine ⟨Or.inl ⟨x, hcover.symm.subset (Or.inl hxR), rfl⟩, ?_⟩
      intro hremoved
      obtain ⟨i, _, hx, hn⟩ := mem_iUnion₂.mp hremoved
      obtain ⟨y, hy, heq⟩ := hx
      have hxy : x = y := (congrArg Prod.fst heq).symm
      have hc := (hcontact i).subset ⟨hxR, hxy ▸ hy⟩
      apply hn
      rcases hc with hc | hc
      · exact Or.inl (congrArg (zeroSheet (ι := Fin 4)) hc)
      · exact Or.inr (congrArg (zeroSheet (ι := Fin 4)) hc)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hsector
      exact C.attached_spoke_traces_subset_rim g k hz hdis b i hi

section OriginalSurface

open PreAbstractSimplicialComplex.ModTwoCochains

variable [DecidableEq E]
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



theorem OriginalPrimalCutDiskData.rim_eq_bridges_union_spokes
    (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels) :
    A.rim = zeroSheet '' complementaryBridgeCopies K P D hcofaces A.bands A.exteriorHeight ∪
      ⋃ i : Fin 4, A.sectorCopy i '' (A.sectors.spoke i ∪ A.sectors.spoke (i + 1)) := by
  apply A.sectors.attached_rim_eq A.sectorHeight A.freshHeight
    (fun i x hx ↦ (A.freshHeight_spec i x hx).2) A.sector_graphs_pairwise_disjoint
  · rw [complementaryCutRim_eq_bridgeCopies_union_gaps K P D hD hcofaces
      A.bands A.exteriorHeight labels A.gaps]
    congr 1
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨A.matching i, ?_⟩
      rw [A.sectorGraph_eq_gap, A.matching.symm_apply_apply]
      exact hi
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rw [A.sectorGraph_eq_gap] at hi
      exact mem_iUnion.mpr ⟨A.matching.symm i, hi⟩
  · exact A.bridgeCopies_inter_sectorGraph K P D hD hcofaces labels hP

end OriginalSurface

end PoincareConjecture.M76.OriginalTriangleCopies
