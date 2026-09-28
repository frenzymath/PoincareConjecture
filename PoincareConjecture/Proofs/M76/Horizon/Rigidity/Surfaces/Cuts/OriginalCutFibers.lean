import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalPrimalCutDisk
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalRimLiftCoverage








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
  (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
  [Fintype (ResidualComplementaryEdge K P D)]
  (labels : ResidualComplementaryEdge K P D ≃ Fin 2)

variable {K P D hD hcofaces hP labels}

namespace OriginalPrimalCutDiskData

variable (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)

noncomputable def sectorCopy (i : Fin 4) (x : E) :
    (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ) :=
  graphAttachmentSheet A.sectorHeight A.freshHeight i x

theorem sector_graphs_pairwise_disjoint :
    Pairwise (fun i j ↦ Disjoint (heightGraph (A.sectorHeight i) '' A.sectors.rim i)
      (heightGraph (A.sectorHeight j) '' A.sectors.rim j)) := by
  intro i j hij
  rw [A.sectorGraph_eq_gap, A.sectorGraph_eq_gap]
  exact A.gaps.gaps_pairwise_disjoint (fun h ↦ hij (A.matching.symm.injective h))

variable (hbound : ∀ s ∈ K.faces, s.card ≤ 3)

include hbound

theorem exterior_projection_inter_primal_subset :
    Prod.fst '' complementaryCutCarrier K P D hD hcofaces A.bands A.exteriorHeight ∩
        K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) ⊆
      K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) := by
  rw [complementaryCut_projection_image K P D hD hcofaces hP hbound]
  exact fun _ hx ↦ ⟨hx.2, hx.1⟩

theorem exterior_primalRim_eq_sector_graphs :
    complementaryCutCarrier K P D hD hcofaces A.bands A.exteriorHeight ∩
        Prod.fst ⁻¹' K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) =
      ⋃ i, heightGraph (A.sectorHeight i) '' A.sectors.rim i := by
  rw [complementaryCut_over_primalRim_eq_gaps K P D hD hcofaces A.bands A.exteriorHeight
    hP hbound labels A.gaps (fun i x hx ↦ (A.exteriorHeight_spec i x hx).2)]
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    refine mem_iUnion.mpr ⟨A.matching i, ?_⟩
    rw [A.sectorGraph_eq_gap, A.matching.symm_apply_apply]
    exact hi
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    rw [A.sectorGraph_eq_gap] at hi
    exact mem_iUnion.mpr ⟨A.matching.symm i, hi⟩

theorem sourceMap_primal_fiber {x : E}
    (hx : x ∈ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)) :
    A.carrier ∩ A.sourceMap ⁻¹' {x} =
      ⋃ i : Fin 4, if x ∈ A.sectors.sector i then {A.sectorCopy i x} else ∅ := by
  exact A.sectors.attached_primal_fiber A.sectorHeight A.freshHeight _
    (fun i x hx ↦ (A.freshHeight_spec i x hx).2)
    (A.exterior_projection_inter_primal_subset hbound)
    (A.exterior_primalRim_eq_sector_graphs hbound) hx

theorem sourceMap_center_fiber :
    A.carrier ∩ A.sourceMap ⁻¹' {A.sectors.center} =
      range (fun i : Fin 4 ↦ A.sectorCopy i A.sectors.center) := by
  exact A.sectors.attached_center_fiber A.sectorHeight A.freshHeight _
    (fun i x hx ↦ (A.freshHeight_spec i x hx).2)
    (A.exterior_projection_inter_primal_subset hbound)
    (A.exterior_primalRim_eq_sector_graphs hbound)

theorem sourceMap_center_fiber_ncard :
    (A.carrier ∩ A.sourceMap ⁻¹' {A.sectors.center}).ncard = 4 := by
  exact A.sectors.attached_center_fiber_ncard A.sectorHeight A.freshHeight _
    (fun i x hx ↦ (A.freshHeight_spec i x hx).2)
    (A.exterior_projection_inter_primal_subset hbound)
    (A.exterior_primalRim_eq_sector_graphs hbound) A.sector_graphs_pairwise_disjoint

theorem sourceMap_spoke_fiber (i : Fin 4) {x : E}
    (hx : x ∈ A.sectors.spoke i) (hxc : x ≠ A.sectors.center) :
    A.carrier ∩ A.sourceMap ⁻¹' {x} =
      {A.sectorCopy i x, A.sectorCopy (i + 3) x} := by
  exact A.sectors.attached_spoke_fiber A.sectorHeight A.freshHeight _
    (fun i x hx ↦ (A.freshHeight_spec i x hx).2)
    (A.exterior_projection_inter_primal_subset hbound)
    (A.exterior_primalRim_eq_sector_graphs hbound) i hx hxc

theorem sourceMap_spoke_fiber_ncard (i : Fin 4) {x : E}
    (hx : x ∈ A.sectors.spoke i) (hxc : x ≠ A.sectors.center) :
    (A.carrier ∩ A.sourceMap ⁻¹' {x}).ncard = 2 := by
  exact A.sectors.attached_spoke_fiber_ncard A.sectorHeight A.freshHeight _
    (fun i x hx ↦ (A.freshHeight_spec i x hx).2)
    (A.exterior_projection_inter_primal_subset hbound)
    (A.exterior_primalRim_eq_sector_graphs hbound) A.sector_graphs_pairwise_disjoint i hx hxc

theorem sourceMap_primal_singleton_off_spokes {x : E}
    (hx : x ∈ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP))
    (hsp : x ∉ ⋃ i, A.sectors.spoke i) :
    ∃ i : Fin 4, A.carrier ∩ A.sourceMap ⁻¹' {x} = {A.sectorCopy i x} := by
  exact A.sectors.attached_singleton_fiber_off_spokes A.sectorHeight A.freshHeight _
    (fun i x hx ↦ (A.freshHeight_spec i x hx).2)
    (A.exterior_projection_inter_primal_subset hbound)
    (A.exterior_primalRim_eq_sector_graphs hbound) hx hsp

omit hbound in
theorem sourceMap_fiber_outside_primal {x : E}
    (hx : x ∉ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)) :
    A.carrier ∩ A.sourceMap ⁻¹' {x} =
      zeroSheet '' (complementaryCutCarrier K P D hD hcofaces A.bands A.exteriorHeight ∩
        Prod.fst ⁻¹' {x}) := by
  exact A.sectors.attached_fiber_outside_primal A.sectorHeight A.freshHeight _ hx

theorem sourceMap_bridge_fiber (s : ResidualComplementaryEdge K P D) {x : E}
    (hx : x ∈ residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
      ((A.bands s).ends 0) ((A.bands s).ends 1))
    (hxP : x ∉ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)) :
    A.carrier ∩ A.sourceMap ⁻¹' {x} =
      {zeroSheet (separatedSheet A.exteriorHeight (s, 0) x),
        zeroSheet (separatedSheet A.exteriorHeight (s, 1) x)} := by
  rw [A.sourceMap_fiber_outside_primal hxP,
    complementaryCut_bridge_fiber K P D hD hcofaces A.bands A.exteriorHeight hbound s hx,
    image_pair]

theorem sourceMap_bridge_fiber_ncard (s : ResidualComplementaryEdge K P D) {x : E}
    (hx : x ∈ residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
      ((A.bands s).ends 0) ((A.bands s).ends 1))
    (hxP : x ∉ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)) :
    (A.carrier ∩ A.sourceMap ⁻¹' {x}).ncard = 2 := by
  rw [A.sourceMap_bridge_fiber hbound s hx hxP]
  apply Set.ncard_pair
  intro heq
  exact complementary_bridge_copies_ne K P D hcofaces A.bands A.exteriorHeight hbound
    (fun i x hx ↦ (A.exteriorHeight_spec i x hx).2) s hx (zeroSheet_injective heq)

theorem sourceMap_singleton_off_spokes_and_bridges {x : E} (hxK : x ∈ K.space)
    (hsp : x ∉ ⋃ i, A.sectors.spoke i)
    (hbridge : x ∉ residualBridgeUnion K P D hcofaces A.bands) :
    ∃ p, A.carrier ∩ A.sourceMap ⁻¹' {x} = {p} := by
  by_cases hxP : x ∈ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)
  · obtain ⟨i, hi⟩ := A.sourceMap_primal_singleton_off_spokes hbound hxP hsp
    exact ⟨A.sectorCopy i x, hi⟩
  · have hcover :
        K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) ∪
          K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)ᶜ = K.space := by
      rw [← K.barycentricSubdivision.vertexDualUnion_union, union_compl_self,
        K.barycentricSubdivision.vertexDualUnion_univ]
      exact K.barycentricSubdivision_isSubdivision.space_eq
    have hxext : x ∈ Prod.fst ''
        complementaryCutCarrier K P D hD hcofaces A.bands A.exteriorHeight := by
      rw [complementaryCut_projection_image K P D hD hcofaces hP hbound]
      exact (hcover.symm.subset hxK).resolve_left hxP
    obtain ⟨p, hp⟩ := complementaryCut_fiber_singleton_off_bridges K P D hD hcofaces
      A.bands A.exteriorHeight hbound (fun i x hx ↦ (A.exteriorHeight_spec i x hx).2)
      hxext hbridge
    refine ⟨zeroSheet p, ?_⟩
    rw [A.sourceMap_fiber_outside_primal hxP, hp, image_singleton]

omit hbound in
theorem sector_spoke_traces_subset_rim (i : Fin 4) :
    A.sectorCopy i '' (A.sectors.spoke i ∪ A.sectors.spoke (i + 1)) ⊆ A.rim := by
  exact A.sectors.attached_spoke_traces_subset_rim A.sectorHeight A.freshHeight
    (fun i x hx ↦ (A.freshHeight_spec i x hx).2) A.sector_graphs_pairwise_disjoint _ i

omit hbound in
theorem center_copies_mem_rim (i : Fin 4) : A.sectorCopy i A.sectors.center ∈ A.rim :=
  A.sector_spoke_traces_subset_rim i
    (mem_image_of_mem _ (Or.inl (A.sectors.center_mem_spoke i)))

end OriginalPrimalCutDiskData
end PoincareConjecture.M76.OriginalTriangleCopies
