import Mathlib.Geometry.Manifold.Riemannian.Basic
import PoincareLib.Geometry.Manifold.ZeroDimensional

/-!
# Smooth carriers for pointed flows

The carrier and tangent-space declarations are unchanged from the reviewed
snapshot in `contracts/definitions/ricci-flow/PointedRicciFlowCompactness.lean`,
from Mapher06/Poincare-MorganTian at
`b2c3c64781fee22edfd683a224d4f8d280e2e9ce`.
They are separated from the metric and flow definitions so purely topological
constructions do not depend on curvature theory.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- A possibly varying smooth carrier for a generalized Ricci flow. -/
structure FlowCarrier (n : ℕ) where
  carrier : Type u
  topologicalSpace : TopologicalSpace carrier
  measurableSpace : MeasurableSpace carrier
  borelSpace : @BorelSpace carrier topologicalSpace measurableSpace
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin n)) carrier
  isManifold : IsManifold (𝓡 n) ∞ carrier
  t2Space : T2Space carrier
  t3Space : T3Space carrier
  secondCountable : SecondCountableTopology carrier
  connected : IsConnected (Set.univ : Set carrier)

abbrev FlowCarrier.tangent {n : ℕ} (C : FlowCarrier n) (x : C.carrier) :=
  @TangentSpace ℝ _ (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanSpace ℝ (Fin n)) _ (𝓡 n) C.carrier
    C.topologicalSpace C.chartedSpace x

/-- Connected zero-dimensional flow carriers have at most one point. -/
theorem FlowCarrier.subsingleton_zero (C : FlowCarrier 0) : Subsingleton C.carrier := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 0)) C.carrier := C.chartedSpace
  let : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
  exact Poincare.subsingleton_of_preconnected_euclidean_zero C.carrier

end PoincareMT
