import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalCutRim

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

noncomputable def cutGraph : Set E :=
  (⋃ i : Fin 4, A.sectors.spoke i) ∪ residualBridgeUnion K P D hcofaces A.bands

theorem sourceMap_rim_image : A.sourceMap '' A.rim = A.cutGraph := by
  rw [A.rim_eq_bridges_union_spokes]
  ext x
  constructor
  · rintro ⟨p, hp | hp, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := hp
      obtain ⟨s, j, z, hz, rfl⟩ := mem_iUnion₂.mp hy
      exact Or.inr (mem_iUnion.mpr ⟨s, hz⟩)
    · obtain ⟨i, z, hz | hz, rfl⟩ := mem_iUnion.mp hp
      · exact Or.inl (mem_iUnion.mpr ⟨i, hz⟩)
      · exact Or.inl (mem_iUnion.mpr ⟨i + 1, hz⟩)
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨A.sectorCopy i x, Or.inr (mem_iUnion.mpr ⟨i, x, Or.inl hi, rfl⟩), rfl⟩
    · obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      exact ⟨zeroSheet (separatedSheet A.exteriorHeight (s, 0) x),
        Or.inl ⟨separatedSheet A.exteriorHeight (s, 0) x,
          mem_iUnion₂.mpr ⟨s, 0, x, hs, rfl⟩, rfl⟩, rfl⟩

theorem quarterMarks_subset_spokes :
    residualQuarterMarks K P D hcofaces A.bands ⊆ ⋃ i : Fin 4, A.sectors.spoke i := by
  intro x hx
  rw [← originalExteriorMarks_range K P D hcofaces A.bands labels] at hx
  obtain ⟨j, rfl⟩ := hx
  refine mem_iUnion.mpr ⟨A.sectors.order.symm j, ?_⟩
  have hj := (A.sectors.spoke_ball (A.sectors.order.symm j)).1 (Or.inr rfl)
  simpa only [A.sectors.order.apply_symm_apply] using hj

theorem bridge_primal_subset_spokes
    (s : ResidualComplementaryEdge K P D) {x : E}
    (hx : x ∈ residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
      ((A.bands s).ends 0) ((A.bands s).ends 1))
    (hxP : x ∈ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)) :
    x ∈ ⋃ i : Fin 4, A.sectors.spoke i := by
  apply A.quarterMarks_subset_spokes
  refine mem_iUnion.mpr ⟨s, ?_⟩
  exact (residualBridge_inter_primal K P hP _
    (complementaryTriangleEdgeEquiv K.vertexAbstractComplex.toPreAbstractSimplicialComplex P
      (originalTriangleCofaceCounts K hcofaces) s.val).property
    (A.bands s).ends_ne (A.bands s).edge_eq).subset ⟨hxP, hx⟩

variable (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
include hbound

theorem mem_rim_of_sourceMap_mem_spoke
    {p : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)}
    (hp : p ∈ A.carrier) (i : Fin 4) (hi : (A.sourceMap) p ∈ A.sectors.spoke i) :
    p ∈ A.rim := by
  by_cases hc : (A.sourceMap) p = A.sectors.center
  · have hf : p ∈ A.carrier ∩ A.sourceMap ⁻¹' {A.sectors.center} := ⟨hp, hc⟩
    rw [A.sourceMap_center_fiber hbound] at hf
    obtain ⟨j, rfl⟩ := hf
    exact A.center_copies_mem_rim j
  · have hf : p ∈ A.carrier ∩ A.sourceMap ⁻¹' {(A.sourceMap) p} := ⟨hp, rfl⟩
    rw [A.sourceMap_spoke_fiber hbound i hi hc] at hf
    rcases hf with hf | hf
    · exact hf ▸ A.sector_spoke_traces_subset_rim i
        (mem_image_of_mem _ (Or.inl hi))
    · have hidx : i + 3 + 1 = i := by fin_cases i <;> decide
      exact hf ▸ A.sector_spoke_traces_subset_rim (i + 3)
        (mem_image_of_mem _ (Or.inr (hidx.symm ▸ hi)))

theorem mem_rim_of_sourceMap_mem_cutGraph
    {p : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)}
    (hp : p ∈ A.carrier) (hcut : (A.sourceMap) p ∈ A.cutGraph) : p ∈ A.rim := by
  rcases hcut with hsp | hbridge
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hsp
    exact A.mem_rim_of_sourceMap_mem_spoke hbound hp i hi
  · obtain ⟨s, hs⟩ := mem_iUnion.mp hbridge
    by_cases hxP : (A.sourceMap) p ∈
        K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (A.bridge_primal_subset_spokes s hs hxP)
      exact A.mem_rim_of_sourceMap_mem_spoke hbound hp i hi
    · have hf : p ∈ A.carrier ∩ A.sourceMap ⁻¹' {(A.sourceMap) p} := ⟨hp, rfl⟩
      rw [A.sourceMap_bridge_fiber hbound s hs hxP] at hf
      rw [A.rim_eq_bridges_union_spokes]
      rcases hf with hf | hf
      · exact Or.inl ⟨separatedSheet A.exteriorHeight (s, 0) ((A.sourceMap) p),
          mem_iUnion₂.mpr ⟨s, 0, (A.sourceMap) p, hs, rfl⟩, hf.symm⟩
      · exact Or.inl ⟨separatedSheet A.exteriorHeight (s, 1) ((A.sourceMap) p),
          mem_iUnion₂.mpr ⟨s, 1, (A.sourceMap) p, hs, rfl⟩, hf.symm⟩

theorem carrier_inter_preimage_cutGraph :
    A.carrier ∩ A.sourceMap ⁻¹' A.cutGraph = A.rim := by
  apply Subset.antisymm
  · exact fun _ hp ↦ A.mem_rim_of_sourceMap_mem_cutGraph hbound hp.1 hp.2
  · intro p hp
    refine ⟨A.disk.1 hp, ?_⟩
    exact A.sourceMap_rim_image.subset (mem_image_of_mem A.sourceMap hp)

theorem sourceMap_fiber_eq_or_rim
    {p q : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)}
    (hp : p ∈ A.carrier) (hq : q ∈ A.carrier) (heq : (A.sourceMap) p = (A.sourceMap) q) :
    p = q ∨ p ∈ A.rim ∧ q ∈ A.rim := by
  by_cases hcut : (A.sourceMap) p ∈ A.cutGraph
  · exact Or.inr ⟨A.mem_rim_of_sourceMap_mem_cutGraph hbound hp hcut,
      A.mem_rim_of_sourceMap_mem_cutGraph hbound hq (heq ▸ hcut)⟩
  · have hxK : (A.sourceMap) p ∈ K.space :=
      A.sourceMap_image.subset (mem_image_of_mem A.sourceMap hp)
    obtain ⟨z, hz⟩ := A.sourceMap_singleton_off_spokes_and_bridges hbound hxK
      (fun h ↦ hcut (Or.inl h)) (fun h ↦ hcut (Or.inr h))
    have hpz : p = z := hz.subset ⟨hp, rfl⟩
    have hqz : q = z := hz.subset ⟨hq, heq.symm⟩
    exact Or.inl (hpz.trans hqz.symm)

theorem sourceMap_injOn_interior : InjOn A.sourceMap (A.carrier \ A.rim) := by
  intro p hp q hq heq
  rcases A.sourceMap_fiber_eq_or_rim hbound hp.1 hq.1 heq with h | h
  · exact h
  · exact (hp.2 h.1).elim

theorem sourceMap_whole_fiber_of_interior
    {p : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)}
    (hp : p ∈ A.carrier \ A.rim) :
    A.carrier ∩ A.sourceMap ⁻¹' {(A.sourceMap) p} = {p} := by
  apply Subset.antisymm
  · rintro q ⟨hq, hqp⟩
    rcases A.sourceMap_fiber_eq_or_rim hbound hq hp.1 hqp with heq | hrim
    · exact heq
    · exact (hp.2 hrim.2).elim
  · rintro q rfl
    exact ⟨hp.1, rfl⟩

theorem sourceMap_whole_fiber_on_rim {x : E} (hx : x ∈ A.cutGraph) :
    A.carrier ∩ A.sourceMap ⁻¹' {x} = A.rim ∩ A.sourceMap ⁻¹' {x} := by
  apply Subset.antisymm
  · rintro p ⟨hp, hpx⟩
    have hpx' : (A.sourceMap) p = x := hpx
    exact ⟨A.mem_rim_of_sourceMap_mem_cutGraph hbound hp (hpx'.symm ▸ hx), hpx⟩
  · exact inter_subset_inter_left _ A.disk.1

theorem sourceMap_interior_image :
    A.sourceMap '' (A.carrier \ A.rim) = K.space \ A.cutGraph := by
  apply Subset.antisymm
  · rintro x ⟨p, ⟨hp, hpr⟩, rfl⟩
    exact ⟨A.sourceMap_image.subset (mem_image_of_mem _ hp),
      fun hc ↦ hpr (A.mem_rim_of_sourceMap_mem_cutGraph hbound hp hc)⟩
  · rintro x ⟨hx, hxc⟩
    obtain ⟨p, hp, hpx⟩ := A.sourceMap_image.symm.subset hx
    refine ⟨p, ⟨hp, ?_⟩, hpx⟩
    intro hpr
    exact hxc (hpx ▸ A.sourceMap_rim_image.subset (mem_image_of_mem A.sourceMap hpr))

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData
