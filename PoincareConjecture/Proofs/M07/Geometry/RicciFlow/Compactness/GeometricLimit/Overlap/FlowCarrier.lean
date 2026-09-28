import PoincareConjecture.Proofs.M07.Geometry.Manifold.Gluing.Smooth
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Carrier
import PoincareConjecture.Proofs.M07.Topology.Gluing.Separation

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Poincare.Gluing.OverlapSystem

variable {n : ℕ} {ι : Type u} [Countable ι]
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i))
    (hsmooth : SmoothOverlap U hU O)
    (hclosed : ∀ i j, IsClosed {q : Piece U i × Piece U j |
      O.Rel ⟨i, q.1⟩ ⟨j, q.2⟩})
    [ConnectedSpace (Quotient O.setoid)]

@[implicit_reducible]
noncomputable def flowCarrier : PoincareConjecture.FlowCarrier.{u} n := by
  let := quotientChartedSpace U hU O
  let := quotient_isManifold U hU O hsmooth
  let : T2Space (Quotient O.setoid) := O.quotient_t2Space hclosed
  let : LocallyCompactSpace (Quotient O.setoid) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) _
  let : SecondCountableTopology (Quotient O.setoid) :=
    O.quotient_secondCountableTopology
  let : MeasurableSpace (Quotient O.setoid) := borel (Quotient O.setoid)
  let : BorelSpace (Quotient O.setoid) := ⟨rfl⟩
  exact
    { carrier := Quotient O.setoid
      topologicalSpace := inferInstance
      measurableSpace := inferInstance
      borelSpace := inferInstance
      chartedSpace := quotientChartedSpace U hU O
      isManifold := inferInstance
      t2Space := inferInstance
      t3Space := inferInstance
      secondCountable := inferInstance
      connected := isConnected_univ }

@[simp] theorem flowCarrier_carrier :
    (flowCarrier U hU O hsmooth hclosed).carrier = Quotient O.setoid := rfl

@[simp] theorem flowCarrier_topologicalSpace :
    (flowCarrier U hU O hsmooth hclosed).topologicalSpace =
      (inferInstance : TopologicalSpace (Quotient O.setoid)) := rfl

@[simp] theorem flowCarrier_chartedSpace :
    (flowCarrier U hU O hsmooth hclosed).chartedSpace =
      quotientChartedSpace U hU O := rfl

@[simp] theorem flowCarrier_measurableSpace :
    (flowCarrier U hU O hsmooth hclosed).measurableSpace =
      borel (Quotient O.setoid) := rfl

theorem flowCarrier_include_isOpenEmbedding (i : ι) :
    let C := flowCarrier U hU O hsmooth hclosed
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    IsOpenEmbedding (O.include i : Piece U i → C.carrier) :=
  O.include_isOpenEmbedding i

theorem flowCarrier_include_isLocalDiffeomorph (i : ι) :
    let C := flowCarrier U hU O hsmooth hclosed
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Quotient O.setoid) := C.chartedSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (O.include i : Piece U i → C.carrier) :=
  include_isLocalDiffeomorph U hU O hsmooth i

theorem flowCarrier_include_contMDiff (i : ι) :
    let C := flowCarrier U hU O hsmooth hclosed
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Quotient O.setoid) := C.chartedSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U i) :=
      (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    ContMDiff (𝓡 n) (𝓡 n) ∞ (O.include i : Piece U i → C.carrier) := by
  let := quotientChartedSpace U hU O
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  exact (include_isLocalDiffeomorph U hU O hsmooth i).contMDiff

end Poincare.Gluing.OverlapSystem
