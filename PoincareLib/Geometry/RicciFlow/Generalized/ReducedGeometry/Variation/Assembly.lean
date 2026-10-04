import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Minimizers.MinimizerEuler
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Jacobi.Jacobi
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.IndexForm.IndexKernel

/-!
# The complete generalized path calculus

Morgan-Tian Sections 6.1-6.4, in particular Lemma 6.4, Definition 6.7,
Lemmas 6.8, 6.10, 6.12, Proposition 6.13 and Proposition 6.33,
pp. 107-122. This assembles the exact frozen calculus clauses from
the actual closed-domain horizontal constructions. No completeness
or open square-root extension of the supplied curve is assumed.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

/-- All nine frozen generalized path-calculus conclusions follow
from the preceding actual constructions, Sections 6.1-6.4,
pp. 107-122. The second variation applies to every Euler path;
the index and its kernel retain their stated minimality hypotheses. -/
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

end PoincareMT.M14
