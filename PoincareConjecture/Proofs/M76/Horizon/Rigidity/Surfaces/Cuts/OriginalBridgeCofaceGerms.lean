import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalHalfBandCofaces
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutFibers
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalCutArcPairing
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalRefinementOwnerGerms

set_option autoImplicit false

open Set Geometry Classical Topology
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
  (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)

local notation "CutSpace" => (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)
local notation "Primal" => K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP)
local notation "sm" => A.sourceMap K P D hD hcofaces hP labels

include hpure

theorem sourceMap_mem_coface_of_sheet_coordinate
    (i : ResidualHalfBandIndex K P D) {p : CutSpace} (hp : p ∈ A.carrier)
    (hnp : sm p ∉ Primal) (hi : p.1.2 i ≠ 0) :
    sm p ∈ convexHull ℝ (((A.bands i.1).coface i.2).val : Set E) := by
  obtain ⟨q, ⟨hq, _⟩, rfl⟩ :=
    (A.sourceMap_fiber_outside_primal hnp).subset ⟨hp, rfl⟩
  change q ∈ separatedCarrier A.exteriorHeight _ _ Finset.univ at hq
  rcases hq with ⟨x, hx, rfl⟩ | hq
  · exact (hi rfl).elim
  · obtain ⟨j, _, x, hx, rfl⟩ := mem_iUnion₂.mp hq
    have hji : j = i := by
      by_contra hne
      apply hi
      simp [separatedSheet, Pi.single_eq_of_ne (Ne.symm hne)]
    subst j
    exact (A.bands i.1).piece_subset_original_coface K hpure hcofaces i.2 hx

include A in
omit hpure in
theorem primalCarrier_isClosed : IsClosed Primal := by
  rw [← A.sectors.sector_cover]
  exact (((A.sectors.sector_ball 0).isCompact.union
    (A.sectors.sector_ball 1).isCompact).union ((A.sectors.sector_ball 2).isCompact.union
    (A.sectors.sector_ball 3).isCompact)).isClosed

theorem exists_original_coface_neighborhood_of_bridge
    (s : ResidualComplementaryEdge K P D) (j : Fin 2) {x : E}
    (hx : x ∈ residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
      ((A.bands s).ends 0) ((A.bands s).ends 1))
    (hnp : x ∉ Primal) :
    ∃ U : Set CutSpace, IsOpen U ∧
      zeroSheet (ι := Fin 4) (separatedSheet A.exteriorHeight (s, j) x) ∈ U ∧
      MapsTo sm (A.carrier ∩ U)
        (convexHull ℝ (((A.bands s).coface j).val : Set E)) := by
  have hbound : ∀ t ∈ K.faces, t.card ≤ 3 := by
    intro t ht
    obtain ⟨u, _, htu, huc⟩ := hpure t ht
    exact (Finset.card_le_card htu).trans_eq huc
  have hxj : x ∈ (A.bands s).piece j := by
    have hx01 := (A.bands s).piece_inter.symm.subset hx
    fin_cases j
    · exact hx01.1
    · exact hx01.2
  have hh : A.exteriorHeight (s, j) x ≠ 0 := by
    intro he
    exact disjoint_left.mp ((A.bands s).bridge_disjoint_attachment hbound j) hx
      ((A.exteriorHeight_spec (s, j) x hxj).2.mp he)
  let U : Set CutSpace := {p | p.1.2 (s, j) ≠ 0} ∩ sm ⁻¹' Primalᶜ
  have hcont : Continuous (fun p : CutSpace ↦ p.1.2 (s, j)) := by fun_prop
  have hsource : Continuous sm := continuous_fst.comp continuous_fst
  refine ⟨U, (isOpen_ne_fun hcont continuous_const).inter
    (A.primalCarrier_isClosed.isOpen_compl.preimage hsource), ?_, ?_⟩
  · exact ⟨by simpa [separatedSheet] using hh, hnp⟩
  · intro p hp
    exact A.sourceMap_mem_coface_of_sheet_coordinate hpure (s, j) hp.1 hp.2.2 hp.2.1

omit hpure in
theorem bridge_nonendpoint_source_not_mem_primal
    (i : Fin 4) {p : CutSpace} (hp : p ∈ A.boundaryBridge i)
    (hp0 : p ≠ A.bridgeBegin i) (hp1 : p ≠ A.bridgeEnd i) : sm p ∉ Primal := by
  intro hnp
  have hx : sm p ∈ A.sourceBridge i :=
    (A.sourceMap_boundaryBridge i).subset (mem_image_of_mem _ hp)
  have he := (residualBridge_inter_primal K P hP _
    (complementaryTriangleEdgeEquiv K.vertexAbstractComplex.toPreAbstractSimplicialComplex P
      (originalTriangleCofaceCounts K hcofaces) (A.bridgeLabelling i).1.val).property
    (A.bands (A.bridgeLabelling i).1).ends_ne
    (A.bands (A.bridgeLabelling i).1).edge_eq).subset ⟨hnp, hx⟩
  change sm p ∈ {primalEdgeMark K
    (complementaryOriginalEdge K P hcofaces (A.bridgeLabelling i).1.val)
      ((A.bands (A.bridgeLabelling i).1).ends 0), primalEdgeMark K
    (complementaryOriginalEdge K P hcofaces (A.bridgeLabelling i).1.val)
      ((A.bands (A.bridgeLabelling i).1).ends 1)} at he
  rw [← A.source_bridge_endpoints i] at he
  rcases he with he | he
  · exact hp0 (A.sourceMap_injOn_boundaryBridge i hp
      ((A.boundaryBridge_interval i).1 (Or.inl rfl)) he)
  · exact hp1 (A.sourceMap_injOn_boundaryBridge i hp
      ((A.boundaryBridge_interval i).1 (Or.inr rfl)) he)

theorem exists_original_coface_neighborhood_of_boundaryBridge
    (i : Fin 4) {p : CutSpace} (hp : p ∈ A.boundaryBridge i)
    (hp0 : p ≠ A.bridgeBegin i) (hp1 : p ≠ A.bridgeEnd i) :
    ∃ U : Set CutSpace, IsOpen U ∧ p ∈ U ∧
      MapsTo sm (A.carrier ∩ U)
        (convexHull ℝ (((A.bands (A.bridgeLabelling i).1).coface
          (A.bridgeLabelling i).2).val : Set E)) := by
  have hnp := A.bridge_nonendpoint_source_not_mem_primal i hp hp0 hp1
  change p ∈ zeroSheet '' (separatedSheet A.exteriorHeight
    (A.bridgeLabelling i) '' A.sourceBridge i) at hp
  obtain ⟨q, ⟨x, hx, rfl⟩, rfl⟩ := hp
  exact A.exists_original_coface_neighborhood_of_bridge hpure
    (A.bridgeLabelling i).1 (A.bridgeLabelling i).2 hx hnp

theorem refined_owner_at_boundaryBridge
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (f : (ℝ × ℝ) → CutSpace)
    (hf : L.AffineOnFaces f) (hmap : MapsTo f L.space A.carrier)
    {t : Finset (ℝ × ℝ)} (ht : t ∈ L.faces) (htc : t.card = 3)
    (hi : InjOn (sm ∘ f) (convexHull ℝ (t : Set (ℝ × ℝ))))
    {T : Finset E} (hTf : T ∈ K.faces) (hTc : T.card = 3)
    (hT : MapsTo (sm ∘ f) (convexHull ℝ (t : Set (ℝ × ℝ)))
      (convexHull ℝ (T : Set E)))
    {z : ℝ × ℝ} (hz : z ∈ convexHull ℝ (t : Set (ℝ × ℝ)))
    (i : Fin 4) (hzi : f z ∈ A.boundaryBridge i)
    (hz0 : f z ≠ A.bridgeBegin i) (hz1 : f z ≠ A.bridgeEnd i) :
    T = ((A.bands (A.bridgeLabelling i).1).coface (A.bridgeLabelling i).2).val := by
  obtain ⟨U, hU, hzU, hcoface⟩ :=
    A.exists_original_coface_neighborhood_of_boundaryBridge hpure i hzi hz0 hz1
  obtain ⟨af, haf⟩ := hf t ht
  let projection : CutSpace →ᴬ[ℝ] E :=
    ((ContinuousLinearMap.fst ℝ E (ResidualHalfBandIndex K P D → ℝ)).comp
      (ContinuousLinearMap.fst ℝ (E × (ResidualHalfBandIndex K P D → ℝ))
        (Fin 4 → ℝ))).toContinuousAffineMap
  have hF : L.AffineOnFaces (sm ∘ f) := hf.postcomp projection
  apply original_owner_eq_of_affineOnFaces_germ K L hTf
    ((A.bands (A.bridgeLabelling i).1).coface (A.bridgeLabelling i).2).property.1
    hTc ((A.bands (A.bridgeLabelling i).1).coface (A.bridgeLabelling i).2).property.2
    ht htc (sm ∘ f) hF hi hT hz (hU.preimage af.continuous)
  · change af z ∈ U
    rwa [← haf hz]
  · intro x hx
    apply hcoface
    refine ⟨hmap (L.convexHull_subset_space ht hx.1), ?_⟩
    rw [haf hx.1]
    exact hx.2

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData
