import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Exhaustion.Frontier
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Distance.NewScale










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.NeckOnlyCover

local notation "slab(" N ")" => EpsilonNeck.coordinate_map N ''
  (Set.prod univ (Icc (-(3 / 4 : ℝ) * (EpsilonNeck.epsilon N)⁻¹)
    ((3 / 4 : ℝ) * (EpsilonNeck.epsilon N)⁻¹)))




theorem exists_neck_at_outer_end_of_quarter_capture :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} (H : NeckOnlyCover g),
        H.epsilon ≤ ε₀ → ∀ C : BalancedNeckChain g H.epsilon,
        (∀ i ∈ C.shape.active, (C.neck i).center ∈ H.X) →
        (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
          (C.neck i).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹ ⊆ slab(C.neck (i + 1)) ∨
          (C.neck (i + 1)).region (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2) ⊆ slab(C.neck i)) →
        ¬ H.X ⊆ C.unionOpen →
        ∃ N ∈ H.necks, N.center ∈ H.X ∧
          N.center ∈ frontier (C.unionOpen : Set M) ∧
          (∀ j ∈ C.shape.active, N.center ≠ (C.neck j).center) ∧
          ∃ i ∈ C.shape.active,
            ((i - 1 ∉ C.shape.active ∧ N.center ∈ closure
              ((C.neck i).region (-H.epsilon⁻¹) (-H.epsilon⁻¹ / 2))) ∨
             (i + 1 ∉ C.shape.active ∧ N.center ∈ closure
              ((C.neck i).region (H.epsilon⁻¹ / 2) H.epsilon⁻¹))) ∧
            (ENNReal.ofReal ((0.99 : ℝ) * (C.neck i).scale * H.epsilon⁻¹) ≤
                g.edist (C.neck i).center N.center ∧
              g.edist (C.neck i).center N.center ≤
                ENNReal.ofReal ((1.01 : ℝ) * (C.neck i).scale * H.epsilon⁻¹)) ∧
            (ENNReal.ofReal ((0.99 : ℝ) * N.scale * H.epsilon⁻¹) ≤
                g.edist N.center (C.neck i).center ∧
              g.edist N.center (C.neck i).center ≤
                ENNReal.ofReal ((1.01 : ℝ) * N.scale * H.epsilon⁻¹)) := by
  obtain ⟨ε₀, hε₀, hsmall, hnewdist⟩ :=
    EpsilonNeck.exists_balanced_frontier_distance_in_new_scale.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g H hε C hcenters hcapture hmiss
  obtain ⟨N, hN, hx, hfront, hfresh, _⟩ := H.exists_neck_at_chain_frontier C hcenters hmiss
  obtain ⟨i, hclosure⟩ := mem_iUnion.mp
    (C.frontier_subset_iUnion_closure_of_quarter_capture hcapture hfront)
  have hout : N.center ∉ (C.neck i.1).carrier := by
    intro h
    exact (C.unionOpen.isOpen.frontier_eq ▸ hfront).2 (mem_iUnion.mpr ⟨i, h⟩)
  have hfronti : N.center ∈ frontier (C.neck i.1).carrier := by
    rw [(C.neck i.1).carrier_open.frontier_eq]
    exact ⟨hclosure, hout⟩
  have he := C.epsilon_eq i.1 i.2
  have hNe := H.neck_epsilon N hN
  have hNsmall : (C.neck i.1).epsilon ≤ ε₀ := by rwa [he]
  refine ⟨N, hN, hx, hfront, hfresh, i.1, i.2,
    C.frontier_endpoint_of_mem_closure i.2 hfront hclosure, ?_, ?_⟩
  · simpa only [he] using (C.neck i.1).balanced_edist_of_mem_frontier
      (hNsmall.trans (hsmall.trans (by norm_num))) hfronti
  · simpa only [hNe] using hnewdist (C.neck i.1) N hNsmall (hNe.trans he.symm) hfronti

end PoincareConjecture.NeckOnlyCover
