import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ComplementaryCutDisk








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

noncomputable def residualBridgeUnion : Set E :=
  ⋃ s : ResidualComplementaryEdge K P D,
    residualBridge K (complementaryOriginalEdge K P hcofaces s.val) ((B s).ends 0) ((B s).ends 1)

noncomputable def residualQuarterMarks : Set E :=
  ⋃ s : ResidualComplementaryEdge K P D,
    {primalEdgeMark K (complementaryOriginalEdge K P hcofaces s.val) ((B s).ends 0),
      primalEdgeMark K (complementaryOriginalEdge K P hcofaces s.val) ((B s).ends 1)}

theorem bridge_not_mem_selectedDual
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (s : ResidualComplementaryEdge K P D) {x : E}
    (hx : x ∈ residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
      ((B s).ends 0) ((B s).ends 1)) :
    x ∉ K.barycentricSubdivision.vertexDualUnion (selectedDualCentroidSet K P D hD hcofaces) := by
  intro hxD
  have hx0 := ((B s).piece_inter.symm.subset hx).1
  have hxa := (OriginalResidualHalfBands.piece_inter_selectedDual K P D hD hbound
    hcofaces s.val s.property (B s) 0).subset ⟨hx0, hxD⟩
  exact Set.disjoint_left.mp ((B s).bridge_disjoint_attachment hbound 0) hx hxa

theorem complementary_bridge_copies_ne
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 → (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    (s : ResidualComplementaryEdge K P D) {x : E}
    (hx : x ∈ residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
      ((B s).ends 0) ((B s).ends 1)) :
    separatedSheet h (s, 0) x ≠ separatedSheet h (s, 1) x := by
  intro heq
  have hz0 := ((separatedSheet_distinct_eq_iff h
    (show (s, (0 : Fin 2)) ≠ (s, 1) by simp) x x).mp heq).2.1
  have hx0 := ((B s).piece_inter.symm.subset hx).1
  exact Set.disjoint_left.mp ((B s).bridge_disjoint_attachment hbound 0) hx
    ((hz (s, 0) x hx0).mp hz0)

theorem complementaryCut_bridge_fiber
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (s : ResidualComplementaryEdge K P D) {x : E}
    (hx : x ∈ residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
      ((B s).ends 0) ((B s).ends 1)) :
    complementaryCutCarrier K P D hD hcofaces B h ∩ Prod.fst ⁻¹' {x} =
      {separatedSheet h (s, 0) x, separatedSheet h (s, 1) x} := by
  have hx01 := (B s).piece_inter.symm.subset hx
  have hxb := residualBridge_subset_band K _ (B s).edge_eq hx
  ext p
  constructor
  · rintro ⟨hp, hpx⟩
    change p ∈ separatedCarrier h _ _ Finset.univ at hp
    rcases hp with ⟨y, hy, rfl⟩ | hp
    · have hyx : y = x := hpx
      subst y
      exact (bridge_not_mem_selectedDual K P D hD hcofaces B hbound s hx hy).elim
    · obtain ⟨⟨t, i⟩, _, y, hy, rfl⟩ := mem_iUnion₂.mp hp
      have hyx : y = x := hpx
      subst y
      have hst : s = t := by
        by_contra hne
        exact Set.disjoint_left.mp (residualComplementaryBands_pairwise_disjoint K P D hcofaces hne)
          hxb ((B t).piece_subset_band i hy)
      subst t
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
  · rintro (rfl | hp)
    · exact ⟨Or.inr (mem_iUnion₂.mpr ⟨(s, 0), Finset.mem_univ _, x, hx01.1, rfl⟩), rfl⟩
    · have hp' : p = separatedSheet h (s, 1) x := hp
      subst p
      exact ⟨Or.inr (mem_iUnion₂.mpr ⟨(s, 1), Finset.mem_univ _, x, hx01.2, rfl⟩), rfl⟩

theorem complementaryCut_bridge_fiber_ncard
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 → (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    (s : ResidualComplementaryEdge K P D) {x : E}
    (hx : x ∈ residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
      ((B s).ends 0) ((B s).ends 1)) :
    (complementaryCutCarrier K P D hD hcofaces B h ∩ Prod.fst ⁻¹' {x}).ncard = 2 := by
  rw [complementaryCut_bridge_fiber K P D hD hcofaces B h hbound s hx]
  exact Set.ncard_pair (complementary_bridge_copies_ne K P D hcofaces B h hbound hz s hx)

theorem complementaryCut_fiber_singleton_off_bridges
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 → (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    {x : E} (hx : x ∈ Prod.fst '' complementaryCutCarrier K P D hD hcofaces B h)
    (hnot : x ∉ residualBridgeUnion K P D hcofaces B) :
    ∃ p : E × (ResidualHalfBandIndex K P D → ℝ),
      complementaryCutCarrier K P D hD hcofaces B h ∩ Prod.fst ⁻¹' {x} = {p} := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p, ?_⟩
  ext q
  constructor
  · rintro ⟨hq, hqx⟩
    have hqp : q.1 = p.1 := (show q.1 = x from hqx).trans hpx.symm
    rcases (complementaryCut_projection_eq_iff K P D hD hcofaces hbound B h hz hq hp).mp hqp with
      h | ⟨s, y, hy, h | h⟩
    · exact h
    · apply False.elim
      apply hnot
      have hyx : y = x := by simpa only [h.1, separatedSheet] using (show q.1 = x from hqx)
      exact mem_iUnion.mpr ⟨s, hyx ▸ hy⟩
    · apply False.elim
      apply hnot
      have hyx : y = x := by simpa only [h.1, separatedSheet] using (show q.1 = x from hqx)
      exact mem_iUnion.mpr ⟨s, hyx ▸ hy⟩
  · intro hq
    have hq' : q = p := hq
    subst q
    exact ⟨hp, hpx⟩

theorem complementary_bridge_copy_subset_rim
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 → (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    (s : ResidualComplementaryEdge K P D) (j : Fin 2) :
    separatedSheet h (s, j) '' residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
        ((B s).ends 0) ((B s).ends 1) ⊆ complementaryCutRim K P D hD hcofaces B h := by
  apply retained_sheet_trace_subset_separatedRim h (fun i ↦ ((B i.1).disk i.2).1) hz
    (complementaryHalfBand_attachments_pairwise K P D hcofaces B)
    Finset.univ (Finset.mem_univ (s, j)) (show _ ⊆ (B s).rim j from subset_union_right)
  intro x hx
  exact (Set.disjoint_left.mp ((B s).bridge_disjoint_attachment hbound j) hx.1 hx.2).elim

theorem residualBridge_inter_primalRim
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (s : ResidualComplementaryEdge K P D) :
    residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
        ((B s).ends 0) ((B s).ends 1) ∩
        K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) =
      {primalEdgeMark K (complementaryOriginalEdge K P hcofaces s.val) ((B s).ends 0),
        primalEdgeMark K (complementaryOriginalEdge K P hcofaces s.val) ((B s).ends 1)} := by
  let e := complementaryOriginalEdge K P hcofaces s.val
  have he : ¬ edgeInGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P e :=
    (complementaryTriangleEdgeEquiv K.vertexAbstractComplex.toPreAbstractSimplicialComplex P
      (originalTriangleCofaceCounts K hcofaces) s.val).property
  have hN := residualBridge_inter_primal K P hP e he (B s).ends_ne (B s).edge_eq
  apply Subset.antisymm
  · rintro x ⟨hx, hr⟩
    exact hN.subset ⟨hr.1, hx⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact ⟨left_mem_segment ℝ _ _,
        primalEdgeMark_mem_rim K P hP e he ((B s).ends 0) (by
          change (B s).ends 0 ∈ (complementaryOriginalEdge K P hcofaces s.val).val
          simp [(B s).edge_eq])⟩
    · have hx' : x = primalEdgeMark K e ((B s).ends 1) := hx
      subst x
      exact ⟨right_mem_segment ℝ _ _,
        primalEdgeMark_mem_rim K P hP e he ((B s).ends 1) (by
          change (B s).ends 1 ∈ (complementaryOriginalEdge K P hcofaces s.val).val
          simp [(B s).edge_eq])⟩

theorem residualBridgeUnion_inter_primalRim
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph) :
    residualBridgeUnion K P D hcofaces B ∩
      K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) =
        residualQuarterMarks K P D hcofaces B := by
  ext x
  constructor
  · rintro ⟨hx, hr⟩
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨s,
      (residualBridge_inter_primalRim K P D hcofaces B hP s).subset ⟨hs, hr⟩⟩
  · intro hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp hx
    have hh := (residualBridge_inter_primalRim K P D hcofaces B hP s).symm.subset hs
    exact ⟨mem_iUnion.mpr ⟨s, hh.1⟩, hh.2⟩

theorem complementaryCut_quarterMark_fiber_ncard
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 → (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    {x : E} (hx : x ∈ residualQuarterMarks K P D hcofaces B) :
    (complementaryCutCarrier K P D hD hcofaces B h ∩ Prod.fst ⁻¹' {x}).ncard = 2 := by
  obtain ⟨s, hs⟩ := mem_iUnion.mp hx
  apply complementaryCut_bridge_fiber_ncard K P D hD hcofaces B h hbound hz s
  rcases hs with rfl | hs
  · exact left_mem_segment ℝ _ _
  · have hs' : x = primalEdgeMark K (complementaryOriginalEdge K P hcofaces s.val)
      ((B s).ends 1) := hs
    rw [hs']
    exact right_mem_segment ℝ _ _

theorem complementaryCut_primalRim_fiber_ncard
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 → (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    {x : E} (hx : x ∈ K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP)) :
    (complementaryCutCarrier K P D hD hcofaces B h ∩ Prod.fst ⁻¹' {x}).ncard =
      if x ∈ residualQuarterMarks K P D hcofaces B then 2 else 1 := by
  by_cases hm : x ∈ residualQuarterMarks K P D hcofaces B
  · rw [if_pos hm]
    exact complementaryCut_quarterMark_fiber_ncard K P D hD hcofaces B h hbound hz hm
  · rw [if_neg hm]
    have hnot : x ∉ residualBridgeUnion K P D hcofaces B := by
      intro hb
      exact hm ((residualBridgeUnion_inter_primalRim K P D hcofaces B hP).subset ⟨hb, hx⟩)
    have himage : x ∈ Prod.fst '' complementaryCutCarrier K P D hD hcofaces B h := by
      rw [complementaryCut_projection_image K P D hD hcofaces hP hbound B h]
      exact hx.2
    obtain ⟨p, hp⟩ := complementaryCut_fiber_singleton_off_bridges K P D hD hcofaces
      B h hbound hz himage hnot
    rw [hp, Set.ncard_singleton]

end PoincareConjecture.M76.OriginalTriangleCopies
