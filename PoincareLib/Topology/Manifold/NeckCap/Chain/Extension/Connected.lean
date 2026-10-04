import PoincareLib.Topology.Manifold.NeckCap.Chain
import PoincareLib.Topology.Manifold.NeckCap.Separation

/-!
# Connected subchains of necks

Every nonempty interval of active indices has connected carrier union. This
also applies to infinite chains and places their entire union in the ambient
component of any selected center.

Reference: Morgan--Tian, Definition A.12 and Lemma A.15, pp. 504--506.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT

theorem ChainShape.ordConnected_active (shape : ChainShape) :
    OrdConnected shape.active := by
  cases shape <;> simp only [ChainShape.active] <;> infer_instance

namespace BalancedNeckChain

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {ε : ℝ} (C : BalancedNeckChain g ε)

/-- Adjacent overlap connects any interval of selected necks. -/
theorem isConnected_subchain_union {J : Set ℤ} (hJ : J.Nonempty)
    (hord : OrdConnected J) (hactive : J ⊆ C.shape.active) :
    IsConnected (⋃ i ∈ J, (C.neck i).carrier) := by
  apply IsConnected.biUnion_of_chain hJ hord
    (fun i _ => (C.neck i).isConnected_carrier)
  intro i hi hnext
  exact C.adjacent_overlap i (hactive hi) (hactive hnext)

/-- The carrier union of a balanced chain is connected for every shape. -/
theorem isConnected_union :
    IsConnected (⋃ i : {i // i ∈ C.shape.active}, (C.neck i.1).carrier) := by
  simpa only [iUnion_subtype] using C.isConnected_subchain_union
    C.active_nonempty C.shape.ordConnected_active (Subset.rfl)

/-- All points of a chain lie in the component of each active center. -/
theorem union_subset_connectedComponent {i : ℤ} (hi : i ∈ C.shape.active) :
    (⋃ j : {j // j ∈ C.shape.active}, (C.neck j.1).carrier) ⊆
      connectedComponent (C.neck i).center := by
  apply C.isConnected_union.subset_connectedComponent
  exact mem_iUnion.mpr ⟨⟨i, hi⟩,
    (C.neck i).central_sphere_subset (C.neck i).center_on_central_sphere⟩

end BalancedNeckChain

end PoincareMT
