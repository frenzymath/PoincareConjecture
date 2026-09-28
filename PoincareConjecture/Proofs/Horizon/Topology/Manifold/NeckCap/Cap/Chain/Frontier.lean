import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.Truncation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.EndFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Maximal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Exhaustion.Frontier












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}


theorem frontier_union_chain_subset_frontier_chain (C : CapCertificate g)
    (T : BalancedNeckChain g C.epsilon)
    (hend : C.end_neck.carrier ⊆ (T.unionOpen : Set M)) :
    frontier (C.carrier ∪ (T.unionOpen : Set M)) ⊆ frontier (T.unionOpen : Set M) := by
  intro x hx
  have hout := ((C.carrier_open.union T.unionOpen.isOpen).frontier_eq ▸ hx).2
  rw [T.unionOpen.isOpen.frontier_eq]
  refine ⟨?_, fun h => hout (Or.inr h)⟩
  rcases frontier_union_subset C.carrier (T.unionOpen : Set M) hx with hC | hT
  · exact closure_mono hend (frontier_subset_closure
      (C.frontier_carrier_subset_frontier_end hC.1))
  · exact frontier_subset_closure hT.2

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem index_eq_zero_of_no_predecessor {ε : ℝ} (T : BalancedNeckChain g ε)
    (hzero : 0 ∈ T.shape.active) (hnonnegative : ∀ i ∈ T.shape.active, 0 ≤ i)
    {i : ℤ} (hi : i ∈ T.shape.active) (hprev : i - 1 ∉ T.shape.active) : i = 0 := by
  have hnonneg := hnonnegative i hi
  cases hshape : T.shape with
  | finite a b =>
    simp only [hshape, ChainShape.active, mem_Icc] at hzero hi hprev
    omega
  | forward a =>
    simp only [hshape, ChainShape.active, mem_Ici] at hzero hi hprev
    omega
  | backward b =>
    simp only [hshape, ChainShape.active, mem_Iic] at hi hprev
    omega
  | biInfinite =>
    simp only [hshape, ChainShape.active, mem_univ, not_true_eq_false] at hprev




theorem exists_chain_frontier_positive_end_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ T : BalancedNeckChain g C.epsilon,
          0 ∈ T.shape.active → (∀ i ∈ T.shape.active, 0 ≤ i) →
          T.neck 0 = C.end_neck →
          T.HasQuarterCapture →
          ∀ x ∈ frontier (C.carrier ∪ (T.unionOpen : Set M)),
            ∃ b ∈ T.shape.active, b + 1 ∉ T.shape.active ∧
              x ∈ closure ((T.neck b).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) := by
  obtain ⟨ε₀, hε₀, hsmall, htrunc⟩ := exists_compact_truncated_core_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε T hzero hnonnegative hfirst hcapture x hx
  have hend : C.end_neck.carrier ⊆ (T.unionOpen : Set M) := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨0, hzero⟩, hfirst.symm ▸ hy⟩
  have hfront := C.frontier_union_chain_subset_frontier_chain T hend hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp
    (T.frontier_subset_iUnion_closure_of_quarter_capture hcapture hfront)
  rcases T.frontier_endpoint_of_mem_closure i.property hfront hxi with
    ⟨hprev, hnegative⟩ | ⟨hnext, hpositive⟩
  · have hi : i.val = 0 := index_eq_zero_of_no_predecessor T hzero hnonnegative
      i.property hprev
    rw [hi, hfirst] at hnegative
    have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
    have hcapture := (htrunc C hε (-C.epsilon⁻¹ / 2) (by linarith)).2
    have hout := ((C.carrier_open.union T.unionOpen.isOpen).frontier_eq ▸ hx).2
    exact (hout (Or.inl (hcapture (Or.inr hnegative)))).elim
  · exact ⟨i.val, i.property, hnext, hpositive⟩



theorem exists_outgoing_chain_frontier_positive_end_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T →
          ∀ x ∈ frontier (C.carrier ∪ (T.unionOpen : Set M)),
            ∃ b ∈ T.shape.active, b + 1 ∉ T.shape.active ∧
              x ∈ closure ((T.neck b).region (C.epsilon⁻¹ / 2) C.epsilon⁻¹) := by
  obtain ⟨ε₀, hε₀, hsmall, hfront⟩ := exists_chain_frontier_positive_end_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε H T hT
  exact hfront C hε T hT.zero_active hT.nonnegative hT.first_neck hT.quarter_capture

end PoincareConjecture.CapCertificate
