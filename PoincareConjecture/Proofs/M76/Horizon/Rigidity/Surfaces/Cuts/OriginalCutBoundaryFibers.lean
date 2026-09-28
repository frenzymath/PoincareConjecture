import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutInteriorEmbedding
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalCutBoundaryArcs
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalCutArcPairing








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

include hbound

theorem sourceMap_fiber_subset_pair {x : E} (hx : x ∈ K.space)
    (hxc : x ≠ A.sectors.center) :
    ∃ p q, A.carrier ∩ A.sourceMap ⁻¹' {x} ⊆ {p, q} := by
  by_cases hsp : x ∈ ⋃ i : Fin 4, A.sectors.spoke i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hsp
    exact ⟨_, _, (A.sourceMap_spoke_fiber hbound i hi hxc).subset⟩
  · by_cases hb : x ∈ residualBridgeUnion K P D hcofaces A.bands
    · obtain ⟨s, hs⟩ := mem_iUnion.mp hb
      have hn : x ∉ K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP) :=
        fun h ↦ hsp (A.bridge_primal_subset_spokes s hs h)
      exact ⟨_, _, (A.sourceMap_bridge_fiber hbound s hs hn).subset⟩
    · obtain ⟨p, hp⟩ := A.sourceMap_singleton_off_spokes_and_bridges hbound hx hsp hb
      exact ⟨p, p, hp.subset.trans (by simp)⟩

theorem sourceMap_three_points
    {p q r : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)}
    (hp : p ∈ A.carrier) (hq : q ∈ A.carrier) (hr : r ∈ A.carrier)
    (hc : (A.sourceMap) p ≠ A.sectors.center)
    (hqv : (A.sourceMap) q = (A.sourceMap) p)
    (hrv : (A.sourceMap) r = (A.sourceMap) p) :
    p = q ∨ p = r ∨ q = r := by
  obtain ⟨u, v, huv⟩ := A.sourceMap_fiber_subset_pair hbound
    (A.sourceMap_image.subset (mem_image_of_mem _ hp)) hc
  have hp' := huv ⟨hp, rfl⟩
  have hq' := huv ⟨hq, hqv⟩
  have hr' := huv ⟨hr, hrv⟩
  simp only [mem_insert_iff, mem_singleton_iff] at hp' hq' hr'
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;>
    rcases hr' with rfl | rfl <;> simp

omit hbound in
theorem longBoundaryArc_subset_carrier (i : Fin 4) : A.longBoundaryArc i ⊆ A.carrier := by
  intro p hp
  exact A.disk.1 (A.longBoundaryArcs_cover.subset (mem_iUnion.mpr ⟨i, hp⟩))

theorem sourceMap_eq_center_of_mem_distinct_arcs {i j : Fin 4} (hij : i ≠ j)
    {p : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)}
    (hi : p ∈ A.longBoundaryArc i) (hj : p ∈ A.longBoundaryArc j) :
    (A.sourceMap) p = A.sectors.center := by
  have hcases : j = i + 1 ∨ j = i + 2 ∨ j = i + 3 := by
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  rcases hcases with rfl | rfl | hprev
  · have he : p = A.gapCenter i := (A.longBoundaryArc_inter_next hbound i).subset ⟨hi, hj⟩
    rw [he]
    rfl
  · exact (Set.disjoint_left.mp (A.longBoundaryArc_disjoint_opposite hbound i) hi hj).elim
  · have hji : j + 1 = i := by
      rw [hprev, add_assoc, show (3 : Fin 4) + 1 = 0 from rfl, add_zero]
    have he : p = A.gapCenter j :=
      (A.longBoundaryArc_inter_next hbound j).subset ⟨hj, hji.symm ▸ hi⟩
    rw [he]
    rfl

theorem whole_fiber_of_longBoundaryArc_pairing (i : Fin 4)
    (H : A.longBoundaryArc i ≃ₜ A.longBoundaryArc (A.arcPairing i))
    (hH : ∀ x, (A.sourceMap) (H x) = (A.sourceMap) x)
    (p : A.longBoundaryArc i) (hc : (A.sourceMap) p ≠ A.sectors.center) :
    A.carrier ∩ A.sourceMap ⁻¹' {(A.sourceMap) p} = {p.val, (H p).val} := by
  have hp := A.longBoundaryArc_subset_carrier i p.property
  have hq := A.longBoundaryArc_subset_carrier (A.arcPairing i) (H p).property
  have hne : p.val ≠ (H p).val := by
    intro he
    exact hc (A.sourceMap_eq_center_of_mem_distinct_arcs hbound
      (A.arcPairing_ne i).symm p.property (he.symm ▸ (H p).property))
  apply Subset.antisymm
  · rintro r ⟨hr, hrv⟩
    rcases A.sourceMap_three_points hbound hp hq hr hc (hH p) hrv with h | h | h
    · exact (hne h).elim
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro r (rfl | rfl)
    · exact ⟨hp, rfl⟩
    · exact ⟨hq, hH p⟩



theorem exists_longBoundaryArc_pairing_with_exact_fibers (i : Fin 4) :
    ∃ H : A.longBoundaryArc i ≃ₜ A.longBoundaryArc (A.arcPairing i), H.IsFinitePL ∧
      (∀ p, (A.sourceMap) (H p) = (A.sourceMap) p) ∧
      ∀ p : A.longBoundaryArc i, (A.sourceMap) p ≠ A.sectors.center →
        A.carrier ∩ A.sourceMap ⁻¹' {(A.sourceMap) p} = {p.val, (H p).val} := by
  obtain ⟨H, hH, hv⟩ := A.exists_longBoundaryArc_pairing_homeomorph hbound i
  exact ⟨H, hH, hv, A.whole_fiber_of_longBoundaryArc_pairing hbound i H hv⟩

omit hbound in
theorem sourceMap_bridge_endpoints_ne (i : Fin 4) :
    (A.sourceMap) (A.bridgeBegin i) ≠ (A.sourceMap) (A.bridgeEnd i) := by
  intro he
  have hball := A.boundaryBridge_interval i
  have hp := hball.1 (Or.inl rfl)
  have hq := hball.1 (Or.inr rfl)
  have hpq := A.sourceMap_injOn_boundaryBridge i hp hq he
  have hn := hball.ncard_boundary_eq_two
  rw [hpq] at hn
  simp at hn

theorem exists_reversing_longBoundaryArc_pairing (i : Fin 4)
    (hrev : (A.sourceMap) (A.bridgeBegin (A.arcPairing i)) =
      (A.sourceMap) (A.bridgeEnd i)) :
    ∃ H : A.longBoundaryArc i ≃ₜ A.longBoundaryArc (A.arcPairing i), H.IsFinitePL ∧
      (∀ p, (A.sourceMap) (H p) = (A.sourceMap) p) ∧
      H (A.arcStart i) = A.arcFinish (A.arcPairing i) ∧
      H (A.arcFinish i) = A.arcStart (A.arcPairing i) ∧
      ∀ p : A.longBoundaryArc i, (A.sourceMap) p ≠ A.sectors.center →
        A.carrier ∩ A.sourceMap ⁻¹' {(A.sourceMap) p} = {p.val, (H p).val} := by
  obtain ⟨H, hH, hv, hend⟩ :=
    A.exists_longBoundaryArc_pairing_homeomorph_with_endpoints hbound i
  rcases hend with ⟨he, _, _⟩ | ⟨_, hs, ht⟩
  · exact (A.sourceMap_bridge_endpoints_ne i (he.symm.trans hrev)).elim
  · exact ⟨H, hH, hv, hs, ht, A.whole_fiber_of_longBoundaryArc_pairing hbound i H hv⟩

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData
