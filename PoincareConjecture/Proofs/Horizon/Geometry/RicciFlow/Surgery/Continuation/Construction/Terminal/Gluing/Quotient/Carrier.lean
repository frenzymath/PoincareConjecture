import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Quotient.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Gluing.Separation

noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {P : ι → Type v}
  [∀ i, TopologicalSpace (P i)]
  [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (P i)]
  [∀ i, IsManifold (𝓡 3) ∞ (P i)]
  [∀ i, SecondCountableTopology (P i)]
  (O : Poincare.Gluing.OverlapSystem P)
  (hs : ∀ i j, ContMDiffOn (𝓡 3) (𝓡 3) ∞
    (O.transition i j) (O.transition i j).source)
  (hc : ∀ i j, IsClosed {q : P i × P j | O.Rel ⟨i, q.1⟩ ⟨j, q.2⟩})

@[implicit_reducible]
def carrier : GeneralizedSliceCarrier.{max u v} := by
  let := chartedSpace O
  let := isManifold O hs
  let : T2Space (Quotient O.setoid) := O.quotient_t2Space hc
  let : LocallyCompactSpace (Quotient O.setoid) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) _
  let : SecondCountableTopology (Quotient O.setoid) := O.quotient_secondCountableTopology
  let : MeasurableSpace (Quotient O.setoid) := borel (Quotient O.setoid)
  let : BorelSpace (Quotient O.setoid) := ⟨rfl⟩
  exact
    { carrier := Quotient O.setoid
      topologicalSpace := inferInstance
      measurableSpace := inferInstance
      borelSpace := inferInstance
      chartedSpace := chartedSpace O
      isManifold := inferInstance
      t2Space := inferInstance
      t3Space := inferInstance
      secondCountable := inferInstance }

theorem carrier_include_isLocalDiffeomorph (i : ι) :
    let C := carrier O hs hc
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Quotient O.setoid) := C.chartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (O.include i : P i → C.carrier) :=
  include_isLocalDiffeomorph O hs i

theorem carrier_include_isOpenEmbedding (i : ι) :
    let C := carrier O hs hc
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    IsOpenEmbedding (O.include i : P i → C.carrier) :=
  O.include_isOpenEmbedding i

end PoincareConjecture.Surgery.Terminal.Gluing
