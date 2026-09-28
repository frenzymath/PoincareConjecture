import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.DistanceLower
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.DistanceUpper
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Frontier

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem EpsilonNeck.balanced_edist_of_mem_frontier (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) {x : M} (hx : x ∈ frontier N.carrier) :
    ENNReal.ofReal ((0.99 : ℝ) * N.scale * N.epsilon⁻¹) ≤ g.edist N.center x ∧
      g.edist N.center x ≤ ENNReal.ofReal ((1.01 : ℝ) * N.scale * N.epsilon⁻¹) :=
  ⟨N.balanced_edist_lower_of_not_mem_carrier hε (N.carrier_open.frontier_eq ▸ hx).2,
    N.edist_center_le_balanced_upper_of_mem_closure hε (frontier_subset_closure hx)⟩

theorem NeckOnlyCover.exists_neck_at_balanced_frontier (H : NeckOnlyCover g)
    (hε : H.epsilon ≤ 1 / 1000) (C : BalancedNeckChain g H.epsilon)
    (hfinite : C.shape.active.Finite)
    (hcenters : ∀ i ∈ C.shape.active, (C.neck i).center ∈ H.X)
    (hmiss : ¬ H.X ⊆ ⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) :
    ∃ N ∈ H.necks, N.center ∈ H.X ∧
      N.center ∈ frontier (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) ∧
      (∀ i ∈ C.shape.active, N.center ≠ (C.neck i).center) ∧
      ∃ i ∈ C.shape.active, N.center ∈ frontier (C.neck i).carrier ∧
        ENNReal.ofReal ((0.99 : ℝ) * (C.neck i).scale * H.epsilon⁻¹) ≤
          g.edist (C.neck i).center N.center ∧
        g.edist (C.neck i).center N.center ≤
          ENNReal.ofReal ((1.01 : ℝ) * (C.neck i).scale * H.epsilon⁻¹) := by
  obtain ⟨N, hN, hx, hxf, hdistinct, -⟩ :=
    H.exists_neck_at_chain_frontier C hcenters hmiss
  obtain ⟨i, hi, hxi⟩ := C.exists_mem_frontier_of_finite hfinite hxf
  refine ⟨N, hN, hx, hxf, hdistinct, i, hi, hxi, ?_⟩
  have hiε : (C.neck i).epsilon ≤ 1 / 1000 := by
    rw [C.epsilon_eq i hi]
    exact hε
  simpa only [C.epsilon_eq i hi] using (C.neck i).balanced_edist_of_mem_frontier hiε hxi

end PoincareConjecture
