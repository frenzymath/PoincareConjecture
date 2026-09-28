import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ComplementaryAttachments
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.FiniteSeparatedAttachments
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalHalfBands









set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]

abbrev ResidualComplementaryEdge (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) :=
  {s : (complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet //
    s.val ∉ D.edgeSet}

theorem residualBand_iUnion_eq_residualCentroidUnion
    [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    (⋃ s : ResidualComplementaryEdge K P D,
      residualBand K (complementaryOriginalEdge K P hcofaces s.val)) =
      K.barycentricSubdivision.vertexDualUnion (residualCentroidSet K P D hcofaces) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    exact mem_iUnion₂.mpr ⟨complementaryCentroidEmbedding K P hcofaces (Sum.inr s.val),
      ⟨s.val, s.property, rfl⟩, hs⟩
  · intro hx
    obtain ⟨z, ⟨s, hs, rfl⟩, hx⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, hx⟩

theorem residualComplementaryBands_pairwise_disjoint
    [Fintype K.barycentricSubdivision.faces]
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    Pairwise (fun s t : ResidualComplementaryEdge K P D ↦
      Disjoint (residualBand K (complementaryOriginalEdge K P hcofaces s.val))
        (residualBand K (complementaryOriginalEdge K P hcofaces t.val))) := by
  intro s t hst
  exact distinctComplementaryCentroidBlocks_disjoint K P hcofaces s.val t.val
    (fun h ↦ hst (Subtype.ext h))

abbrev ResidualHalfBandIndex (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) :=
  ResidualComplementaryEdge K P D × Fin 2

section Construction

variable [Fintype K.barycentricSubdivision.faces]
  (P : SimpleGraph K.vertices)
  (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
  (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
  (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)

noncomputable def complementaryCutCarrier
    (B : ∀ s : ResidualComplementaryEdge K P D,
      OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
    (h : ResidualHalfBandIndex K P D → E → ℝ)
    [Fintype (ResidualComplementaryEdge K P D)] : Set (E × (ResidualHalfBandIndex K P D → ℝ)) :=
  separatedCarrier h
    (K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces))
    (fun i ↦ (B i.1).piece i.2) Finset.univ

noncomputable def complementaryCutRim
    (B : ∀ s : ResidualComplementaryEdge K P D,
      OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
    (h : ResidualHalfBandIndex K P D → E → ℝ)
    [Fintype (ResidualComplementaryEdge K P D)] : Set (E × (ResidualHalfBandIndex K P D → ℝ)) :=
  separatedRim h
    (K.barycentricSubdivision.vertexDualRim (selectedDualCentroidSet K P D hD hcofaces))
    (fun i ↦ (B i.1).rim i.2) (fun i ↦ (B i.1).attachment i.2)
    (fun i ↦ (B i.1).firstCorner i.2) (fun i ↦ (B i.1).secondCorner i.2) Finset.univ

theorem complementaryHalfBand_attachments_pairwise
    (B : ∀ s : ResidualComplementaryEdge K P D,
      OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val)) :
    Pairwise (fun i j : ResidualHalfBandIndex K P D ↦
      Disjoint ((B i.1).attachment i.2) ((B j.1).attachment j.2)) := by
  rintro ⟨s, i⟩ ⟨t, j⟩ hne
  by_cases hst : s = t
  · subst t
    apply (B s).attachment_pairwise
    exact fun hij ↦ hne (Prod.ext rfl hij)
  · exact (residualComplementaryBands_pairwise_disjoint K P D hcofaces hst).mono
      ((B s).attachment_subset_piece i |>.trans ((B s).piece_subset_band i))
      ((B t).attachment_subset_piece j |>.trans ((B t).piece_subset_band j))

theorem complementaryHalfBand_iUnion
    (B : ∀ s : ResidualComplementaryEdge K P D,
      OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val)) :
    (⋃ i : ResidualHalfBandIndex K P D, (B i.1).piece i.2) =
      K.barycentricSubdivision.vertexDualUnion (residualCentroidSet K P D hcofaces) := by
  rw [← residualBand_iUnion_eq_residualCentroidUnion K P D hcofaces]
  ext x
  constructor
  · intro hx
    obtain ⟨⟨s, i⟩, hx⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨s, (B s).piece_subset_band i hx⟩
  · intro hx
    obtain ⟨s, hx⟩ := mem_iUnion.mp hx
    rw [← (B s).piece_union] at hx
    rcases hx with hx | hx
    · exact mem_iUnion.mpr ⟨(s, 0), hx⟩
    · exact mem_iUnion.mpr ⟨(s, 1), hx⟩



theorem exists_original_complementary_cut_disk
    [Fintype (ResidualComplementaryEdge K P D)]
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (hDtree : D.IsTree) :
    ∃ (B : ∀ s : ResidualComplementaryEdge K P D,
        OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
      (h : ResidualHalfBandIndex K P D → E → ℝ),
      (∀ i, FinitePiecewiseAffineOn (h i) ((B i.1).piece i.2)) ∧
      (∀ i x, x ∈ (B i.1).piece i.2 →
        h i x ∈ Icc 0 1 ∧ (h i x = 0 ↔ x ∈ (B i.1).attachment i.2)) ∧
      IsFinitePLBallPair (ℝ × ℝ) (complementaryCutCarrier K P D hD hcofaces B h)
        (complementaryCutRim K P D hD hcofaces B h) ∧
      FinitePiecewiseAffineOn Prod.fst (complementaryCutCarrier K P D hD hcofaces B h) ∧
      Prod.fst '' complementaryCutCarrier K P D hD hcofaces B h =
        K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces) ∪
          K.barycentricSubdivision.vertexDualUnion (residualCentroidSet K P D hcofaces) := by
  classical
  let B : ∀ s : ResidualComplementaryEdge K P D,
      OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val) :=
    fun s ↦ Classical.choice (nonempty_originalResidualHalfBands K hpure hcofaces hlinks
      (complementaryOriginalEdge K P hcofaces s.val))
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, ht⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  have hbase := selectedDualCentroid_isFinitePLBallPair K hpure hcofaces hlinks P D hD hDtree
  have hdb : ∀ i : ResidualHalfBandIndex K P D, (B i.1).attachment i.2 ⊆
      K.barycentricSubdivision.vertexDualRim (selectedDualCentroidSet K P D hD hcofaces) := by
    intro i
    exact residualCofaceContact_subset_selectedDualRim K P D hD hcofaces i.1.val i.1.property
      ((B i.1).coface i.2) ((B i.1).edge_subset i.2)
  obtain ⟨h, hh, hz, hdisk, hproj, himage⟩ := exists_separated_disks hbase
    (fun i : ResidualHalfBandIndex K P D ↦ (B i.1).disk i.2)
    (fun i ↦ (B i.1).attachment_interval hbound hcofaces i.2) hdb
    (fun i ↦ (B i.1).attachment_subset_rim i.2)
    (fun i ↦ (B i.1).corners_ne hbound i.2)
    (complementaryHalfBand_attachments_pairwise K P D hcofaces B)
  refine ⟨B, h, hh, hz, hdisk, hproj, ?_⟩
  exact himage.trans (congrArg (_ ∪ ·) (complementaryHalfBand_iUnion K P D hcofaces B))

theorem complementaryCut_projection_fiber
    [Fintype (ResidualComplementaryEdge K P D)]
    (B : ∀ s : ResidualComplementaryEdge K P D,
      OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
    (h : ResidualHalfBandIndex K P D → E → ℝ) (x : E) :
    complementaryCutCarrier K P D hD hcofaces B h ∩ Prod.fst ⁻¹' {x} =
      (if x ∈ K.barycentricSubdivision.vertexDualUnion
        (selectedDualCentroidSet K P D hD hcofaces)
        then {zeroSheet (ι := ResidualHalfBandIndex K P D) x} else ∅) ∪
      ⋃ i : ResidualHalfBandIndex K P D,
        if x ∈ (B i.1).piece i.2 then {separatedSheet h i x} else ∅ := by
  simpa only [complementaryCutCarrier, Finset.mem_univ, iUnion_true] using
    separatedCarrier_projection_fiber h
      (K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces))
      (fun i : ResidualHalfBandIndex K P D ↦ (B i.1).piece i.2) Finset.univ x

theorem complementaryCut_projection_image
    [Fintype (ResidualComplementaryEdge K P D)]
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (B : ∀ s : ResidualComplementaryEdge K P D,
      OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
    (h : ResidualHalfBandIndex K P D → E → ℝ) :
    Prod.fst '' complementaryCutCarrier K P D hD hcofaces B h =
      K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)ᶜ := by
  unfold complementaryCutCarrier
  rw [projection_separatedCarrier]
  simp only [Finset.mem_univ, iUnion_true]
  rw [complementaryHalfBand_iUnion,
    treeCotree_exterior_eq_complementary_union K P hP D hD hbound hcofaces]



theorem complementaryCut_projection_eq_iff
    [Fintype (ResidualComplementaryEdge K P D)]
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (B : ∀ s : ResidualComplementaryEdge K P D,
      OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
    (h : ResidualHalfBandIndex K P D → E → ℝ)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 → (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    {p q : E × (ResidualHalfBandIndex K P D → ℝ)}
    (hp : p ∈ complementaryCutCarrier K P D hD hcofaces B h)
    (hq : q ∈ complementaryCutCarrier K P D hD hcofaces B h) :
    p.1 = q.1 ↔ p = q ∨ ∃ s : ResidualComplementaryEdge K P D, ∃ x,
      x ∈ residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
        ((B s).ends 0) ((B s).ends 1) ∧
      ((p = separatedSheet h (s, 0) x ∧ q = separatedSheet h (s, 1) x) ∨
        (p = separatedSheet h (s, 1) x ∧ q = separatedSheet h (s, 0) x)) := by
  constructor
  · intro hpq
    change p ∈ separatedCarrier h _ _ Finset.univ at hp
    change q ∈ separatedCarrier h _ _ Finset.univ at hq
    rcases hp with ⟨x, hx, rfl⟩ | hp
    · rcases hq with ⟨y, hy, rfl⟩ | hq
      · change x = y at hpq
        exact Or.inl (congrArg (zeroSheet (ι := ResidualHalfBandIndex K P D)) hpq)
      · obtain ⟨i, _, y, hy, rfl⟩ := mem_iUnion₂.mp hq
        change x = y at hpq
        subst y
        have ha := (OriginalResidualHalfBands.piece_inter_selectedDual K P D hD hbound
          hcofaces i.1.val i.1.property (B i.1) i.2).subset ⟨hy, hx⟩
        exact Or.inl ((separatedSheet_eq_zeroSheet_iff h i x x).mpr
          ⟨rfl, (hz i x hy).mpr ha⟩).symm
    · obtain ⟨i, _, x, hx, rfl⟩ := mem_iUnion₂.mp hp
      rcases hq with ⟨y, hy, rfl⟩ | hq
      · change x = y at hpq
        subst y
        have ha := (OriginalResidualHalfBands.piece_inter_selectedDual K P D hD hbound
          hcofaces i.1.val i.1.property (B i.1) i.2).subset ⟨hx, hy⟩
        exact Or.inl ((separatedSheet_eq_zeroSheet_iff h i x x).mpr
          ⟨rfl, (hz i x hx).mpr ha⟩)
      · obtain ⟨j, _, y, hy, rfl⟩ := mem_iUnion₂.mp hq
        change x = y at hpq
        subst y
        obtain ⟨s, i⟩ := i
        obtain ⟨t, j⟩ := j
        by_cases hst : s = t
        · subst t
          fin_cases i <;> fin_cases j
          · exact Or.inl rfl
          · exact Or.inr ⟨s, x, (B s).piece_inter.subset ⟨hx, hy⟩,
              Or.inl ⟨rfl, rfl⟩⟩
          · exact Or.inr ⟨s, x, (B s).piece_inter.subset ⟨hy, hx⟩,
              Or.inr ⟨rfl, rfl⟩⟩
          · exact Or.inl rfl
        · exact (Set.disjoint_left.mp
            (residualComplementaryBands_pairwise_disjoint K P D hcofaces hst)
            ((B s).piece_subset_band i hx) ((B t).piece_subset_band j hy)).elim
  · rintro (rfl | ⟨s, x, _, h | h⟩)
    · rfl
    · rw [h.1, h.2]; rfl
    · rw [h.1, h.2]; rfl

end Construction

end PoincareConjecture.M76.OriginalTriangleCopies
