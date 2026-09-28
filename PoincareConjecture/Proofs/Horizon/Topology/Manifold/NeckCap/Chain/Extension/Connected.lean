import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Separation










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

theorem ChainShape.ordConnected_active (shape : ChainShape) :
    OrdConnected shape.active := by
  cases shape <;> simp only [ChainShape.active] <;> infer_instance

namespace BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε)


theorem isConnected_subchain_union {J : Set ℤ} (hJ : J.Nonempty)
    (hord : OrdConnected J) (hactive : J ⊆ C.shape.active) :
    IsConnected (⋃ i ∈ J, (C.neck i).carrier) := by
  apply IsConnected.biUnion_of_chain hJ hord
    (fun i _ => (C.neck i).isConnected_carrier)
  intro i hi hnext
  exact C.adjacent_overlap i (hactive hi) (hactive hnext)


theorem isConnected_union :
    IsConnected (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) := by
  simpa only [iUnion_subtype] using C.isConnected_subchain_union
    C.active_nonempty C.shape.ordConnected_active (Subset.rfl)


theorem union_subset_connectedComponent {i : ℤ} (hi : i ∈ C.shape.active) :
    (⋃ j : {j // j ∈ C.shape.active}, (C.neck j.1).carrier) ⊆
      connectedComponent (C.neck i).center := by
  apply C.isConnected_union.subset_connectedComponent
  exact mem_iUnion.mpr ⟨⟨i, hi⟩,
    (C.neck i).central_sphere_subset (C.neck i).center_on_central_sphere⟩

end BalancedNeckChain

end PoincareConjecture
