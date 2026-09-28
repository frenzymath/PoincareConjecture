import PoincareConjecture.Proofs.M14.Sec6_2_MinimizerEuler
import PoincareConjecture.Proofs.M14.Sec6_2_Jacobi
import PoincareConjecture.Proofs.M14.Sec6_4_IndexKernel

set_option autoImplicit false

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem pathCalculusConclusion
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    M14PathCalculusConclusion G where
  minimizer_euler := minimizerEulerStatement hCoordinates hM12
  square_root_euler := squareRootEulerStatement hCoordinates hM12
  square_root_regularization := squareRootRegularizationStatement hCoordinates hM12
  first_variation := firstVariationStatement hCoordinates hM12
  second_variation := secondVariationStatement hCoordinates hM04 hM12
  fixed_endpoint_index := fixedEndpointIndexStatement hCoordinates hM04 hM12
  fixed_endpoint_index_kernel := fixedEndpointIndexKernelStatement hCoordinates hM04 hM12
  jacobi := jacobiStatement hM04 hM12
  initial_jacobi := initialJacobiStatement hM04 hM12

end PoincareConjecture.M14
