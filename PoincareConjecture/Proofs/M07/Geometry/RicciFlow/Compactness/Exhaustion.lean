import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Carrier
import PoincareConjecture.Proofs.M07.Topology.Exhaustion

set_option autoImplicit false

namespace PoincareConjecture.FlowCarrier

theorem exists_connected_open_exhaustion {n : ℕ} (C : FlowCarrier n) (base : C.carrier) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    ∃ U : ℕ → Set C.carrier,
      (∀ j, IsOpen (U j)) ∧
      (∀ j, IsConnected (U j)) ∧
      (∀ j, IsCompact (closure (U j))) ∧
      (∀ j, U j ⊆ U (j + 1)) ∧
      (⋃ j, U j = Set.univ) ∧
      (∀ j, base ∈ U j) := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : T2Space C.carrier := C.t2Space
  let : SecondCountableTopology C.carrier := C.secondCountable
  let : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  let : LocallyConnectedSpace C.carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) C.carrier
  let : LocallyCompactSpace C.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) C.carrier
  exact Poincare.exists_connected_open_exhaustion base

end PoincareConjecture.FlowCarrier
