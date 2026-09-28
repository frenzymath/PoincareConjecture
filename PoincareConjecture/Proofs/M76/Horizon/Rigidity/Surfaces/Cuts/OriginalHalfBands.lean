import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ResidualBandSideAlignment
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ComplementaryAttachments



set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  [Fintype K.barycentricSubdivision.faces]

structure OriginalResidualHalfBands
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) where
  ends : Fin 2 → K.vertices
  ends_ne : ends 0 ≠ ends 1
  edge_eq : e.val = {ends 0, ends 1}
  coface : Fin 2 → Triangle K
  coface_ne : coface 0 ≠ coface 1
  edge_subset : ∀ i, e.val.map (Function.Embedding.subtype _) ⊆ (coface i).val
  outer : Fin 2 → Set E
  piece : Fin 2 → Set E
  outer_interval : ∀ i, IsFinitePLBallPair ℝ (outer i)
    {primalEdgeMark K e (ends 0), primalEdgeMark K e (ends 1)}
  outer_union : outer 0 ∪ outer 1 = residualBandRim K e
  outer_inter : outer 0 ∩ outer 1 =
    {primalEdgeMark K e (ends 0), primalEdgeMark K e (ends 1)}
  disk : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (piece i)
    (outer i ∪ residualBridge K e (ends 0) (ends 1))
  piece_union : piece 0 ∪ piece 1 = residualBand K e
  piece_inter : piece 0 ∩ piece 1 = residualBridge K e (ends 0) (ends 1)
  piece_outer : ∀ i, piece i ∩ residualBandRim K e = outer i
  coface_outer : ∀ i, residualCofaceContact K e (coface i).val ⊆ outer i

theorem nonempty_originalResidualHalfBands
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    Nonempty (OriginalResidualHalfBands K e) := by
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, hst, hc⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq hc
  obtain ⟨a, b, t, u, hab, heq, htu, ht, hu, _⟩ :=
    exists_residualBand_rim_inventory K hbound hcofaces e
  obtain ⟨U, V, d₀, d₁, hU, hV, hUV, hUVint, hd₀, hd₁,
      hwhole, hcommon, hout₀, hout₁, hTU, hWV⟩ :=
    exists_residualBand_bridge_cut_aligned K hpure hcofaces hlinks e hab heq
      ht.1 hu.1 ht.2.1 hu.2.1 htu ht.2.2 hu.2.2
  refine ⟨{
    ends := ![a, b]
    ends_ne := hab
    edge_eq := heq
    coface := ![⟨t, ht.1, ht.2.1⟩, ⟨u, hu.1, hu.2.1⟩]
    coface_ne := fun h ↦ htu (congrArg Subtype.val h)
    edge_subset := ?_
    outer := ![U, V]
    piece := ![d₀, d₁]
    outer_interval := ?_
    outer_union := hUV
    outer_inter := hUVint
    disk := ?_
    piece_union := hwhole
    piece_inter := hcommon
    piece_outer := ?_
    coface_outer := ?_ }⟩
  · intro i; fin_cases i
    · exact ht.2.2
    · exact hu.2.2
  · intro i; fin_cases i
    · exact hU
    · exact hV
  · intro i; fin_cases i
    · exact hd₀
    · change IsFinitePLBallPair (ℝ × ℝ) d₁ (V ∪ residualBridge K e a b)
      simpa only [union_comm] using hd₁
  · intro i; fin_cases i
    · exact hout₀
    · exact hout₁
  · intro i; fin_cases i
    · exact hTU
    · exact hWV

variable {K} {e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex}

noncomputable def OriginalResidualHalfBands.attachment (B : OriginalResidualHalfBands K e)
    (i : Fin 2) : Set E := residualCofaceContact K e (B.coface i).val

noncomputable def OriginalResidualHalfBands.rim (B : OriginalResidualHalfBands K e)
    (i : Fin 2) : Set E := B.outer i ∪ residualBridge K e (B.ends 0) (B.ends 1)

noncomputable def OriginalResidualHalfBands.firstCorner (B : OriginalResidualHalfBands K e)
    (i : Fin 2) : E := residualBandCorner K e (B.ends 0) (B.coface i).val

noncomputable def OriginalResidualHalfBands.secondCorner (B : OriginalResidualHalfBands K e)
    (i : Fin 2) : E := residualBandCorner K e (B.ends 1) (B.coface i).val

theorem OriginalResidualHalfBands.attachment_interval (B : OriginalResidualHalfBands K e)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (i : Fin 2) : IsFinitePLBallPair ℝ (B.attachment i) {B.firstCorner i, B.secondCorner i} :=
  residualCofaceContact_exact_interval K hbound hcofaces e B.ends_ne B.edge_eq
    (B.coface i).property.1 (B.coface i).property.2 (B.edge_subset i)

theorem OriginalResidualHalfBands.attachment_subset_rim (B : OriginalResidualHalfBands K e)
    (i : Fin 2) : B.attachment i ⊆ B.rim i :=
  (B.coface_outer i).trans subset_union_left

theorem OriginalResidualHalfBands.attachment_subset_piece (B : OriginalResidualHalfBands K e)
    (i : Fin 2) : B.attachment i ⊆ B.piece i :=
  (B.attachment_subset_rim i).trans (B.disk i).1

theorem OriginalResidualHalfBands.piece_subset_band (B : OriginalResidualHalfBands K e)
    (i : Fin 2) : B.piece i ⊆ residualBand K e := by
  fin_cases i
  · exact subset_union_left.trans B.piece_union.subset
  · exact subset_union_right.trans B.piece_union.subset

theorem OriginalResidualHalfBands.attachment_disjoint (B : OriginalResidualHalfBands K e) :
    Disjoint (B.attachment 0) (B.attachment 1) :=
  residualCofaceContact_disjoint K e (B.coface 0).property.1 (B.coface 1).property.1
    (B.coface 0).property.2 (B.coface 1).property.2
    (fun h ↦ B.coface_ne (Subtype.ext h))

theorem OriginalResidualHalfBands.attachment_pairwise (B : OriginalResidualHalfBands K e) :
    Pairwise (fun i j ↦ Disjoint (B.attachment i) (B.attachment j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact B.attachment_disjoint
  · exact B.attachment_disjoint.symm
  · exact (hij rfl).elim

theorem OriginalResidualHalfBands.corners_ne (B : OriginalResidualHalfBands K e)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (i : Fin 2) :
    B.firstCorner i ≠ B.secondCorner i := by
  have hfirst := (primal_coface_contact_inter K hbound e (B.ends 0)
    (by simp [B.edge_eq]) (B.coface i).property.1 (B.coface i).property.2
    (B.edge_subset i)).symm.subset (mem_singleton _)
  have hsecond := (primal_coface_contact_inter K hbound e (B.ends 1)
    (by simp [B.edge_eq]) (B.coface i).property.1 (B.coface i).property.2
    (B.edge_subset i)).symm.subset (mem_singleton _)
  intro h
  change residualBandCorner K e (B.ends 0) (B.coface i).val =
    residualBandCorner K e (B.ends 1) (B.coface i).val at h
  exact Set.disjoint_left.mp (primalEdgeContact_disjoint K e e (B.ends 0) (B.ends 1)
    (Or.inr B.ends_ne)) hfirst.1 (h.symm ▸ hsecond.1)

theorem OriginalResidualHalfBands.attachment_avoids_marks (B : OriginalResidualHalfBands K e)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (i : Fin 2) :
    Disjoint (B.attachment i)
      {primalEdgeMark K e (B.ends 0), primalEdgeMark K e (B.ends 1)} := by
  apply Set.disjoint_left.mpr
  rintro x hx (rfl | hx')
  · exact primalEdgeMark_not_mem_cofaceContact K hbound e (B.ends 0)
      (by simp [B.edge_eq]) (B.coface i).property.1 (B.coface i).property.2
      (B.edge_subset i) hx
  · have hx'' : x = primalEdgeMark K e (B.ends 1) := hx'
    rw [hx''] at hx
    exact primalEdgeMark_not_mem_cofaceContact K hbound e (B.ends 1)
      (by simp [B.edge_eq]) (B.coface i).property.1 (B.coface i).property.2
      (B.edge_subset i) hx

theorem OriginalResidualHalfBands.piece_disjoint_other_attachment
    (B : OriginalResidualHalfBands K e) (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    {i j : Fin 2} (hij : i ≠ j) : Disjoint (B.piece i) (B.attachment j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have houterj := B.coface_outer j hxj
  have hrim : x ∈ residualBandRim K e :=
    residualCofaceContact_subset_bandRim K e (B.coface j).property.1
      (B.coface j).property.2 hxj
  have houteri := (B.piece_outer i).subset ⟨hxi, hrim⟩
  have hmarks : x ∈ ({primalEdgeMark K e (B.ends 0),
      primalEdgeMark K e (B.ends 1)} : Set E) := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact B.outer_inter.subset ⟨houteri, houterj⟩
    · exact B.outer_inter.subset ⟨houterj, houteri⟩
    · exact (hij rfl).elim
  exact Set.disjoint_left.mp (B.attachment_avoids_marks hbound j) hxj hmarks

theorem OriginalResidualHalfBands.piece_inter_attachment_union
    (B : OriginalResidualHalfBands K e) (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (i : Fin 2) : B.piece i ∩ (B.attachment 0 ∪ B.attachment 1) = B.attachment i := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxa | hxb⟩
    · by_cases hi : i = 0
      · simpa only [hi] using hxa
      · exact (Set.disjoint_left.mp (B.piece_disjoint_other_attachment hbound hi) hx hxa).elim
    · by_cases hi : i = 1
      · simpa only [hi] using hxb
      · exact (Set.disjoint_left.mp (B.piece_disjoint_other_attachment hbound hi) hx hxb).elim
  · intro x hx
    refine ⟨B.attachment_subset_piece i hx, ?_⟩
    fin_cases i
    · exact Or.inl hx
    · exact Or.inr hx

theorem OriginalResidualHalfBands.bridge_disjoint_attachment
    (B : OriginalResidualHalfBands K e) (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (i : Fin 2) :
    Disjoint (residualBridge K e (B.ends 0) (B.ends 1)) (B.attachment i) := by
  apply Set.disjoint_left.mpr
  intro x hx ha
  have hrim := residualCofaceContact_subset_bandRim K e (B.coface i).property.1
    (B.coface i).property.2 ha
  have hmark := (residualBridge_inter_bandRim K e B.edge_eq).subset ⟨hx, hrim⟩
  exact Set.disjoint_left.mp (B.attachment_avoids_marks hbound i) ha hmark

variable (K) [Fintype K.vertices]

theorem OriginalResidualHalfBands.attachment_subset_selectedDualRim
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (s : (complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet)
    (B : OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s)) (i : Fin 2) :
    B.attachment i ⊆
      K.barycentricSubdivision.vertexDualRim (selectedDualCentroidSet K P D hD hcofaces) :=
  residualCofaceContact_subset_selectedDualRim K P D hD hcofaces s hs
    (B.coface i) (B.edge_subset i)

theorem OriginalResidualHalfBands.piece_inter_selectedDual
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (s : (complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hs : s.val ∉ D.edgeSet)
    (B : OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s)) (i : Fin 2) :
    B.piece i ∩
        K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces) =
      B.attachment i := by
  have hband := residualBand_inter_selectedDual_two_contacts K P D hD hcofaces s hs
    (B.coface 0) (B.coface 1) B.coface_ne (B.edge_subset 0) (B.edge_subset 1)
  calc
    _ = B.piece i ∩ (residualBand K (complementaryOriginalEdge K P hcofaces s) ∩
        K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces)) := by
      ext x
      exact ⟨fun hx ↦ ⟨hx.1, B.piece_subset_band i hx.1, hx.2⟩,
        fun hx ↦ ⟨hx.1, hx.2.2⟩⟩
    _ = B.attachment i := by
      rw [hband]
      exact B.piece_inter_attachment_union hbound i

end PoincareConjecture.M76.OriginalTriangleCopies
