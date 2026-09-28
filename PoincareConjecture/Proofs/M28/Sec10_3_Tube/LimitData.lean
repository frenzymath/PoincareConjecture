import PoincareConjecture.Definitions.M28BoundedDistance










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]




structure LocalNonnegativeBackwardModel (g : RiemannianMetric 3 M)
    (U : Set M) (x : M) where

  carrier : FlowCarrier.{0} 3

  duration : ℝ

  duration_pos : 0 < duration

  flow : letI := carrier.topologicalSpace
    letI := carrier.chartedSpace
    letI := carrier.isManifold
    RicciFlow 3 carrier.carrier (Icc (-duration) 0)

  embedding : carrier.carrier → M

  embedding_open : letI := carrier.topologicalSpace
    Topology.IsOpenEmbedding embedding

  embedding_smooth : letI := carrier.topologicalSpace
    letI := carrier.chartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ embedding

  image_subset : range embedding ⊆ U

  captures : x ∈ range embedding

  metric_at_zero : letI := carrier.topologicalSpace
    letI := carrier.chartedSpace
    letI := carrier.isManifold
    ∀ p v w, g.inner (embedding p)
      (mfderiv (𝓡 3) (𝓡 3) embedding p v)
      (mfderiv (𝓡 3) (𝓡 3) embedding p w) = (flow.metric 0).inner p v w

  nonnegative : letI := carrier.topologicalSpace
    letI := carrier.chartedSpace
    letI := carrier.isManifold
    ∀ t ∈ Icc (-duration) 0, ∀ p,
      LeviCivitaData.NonnegativeCurvatureOperator (flow.connection t) p

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]





structure QuantitativeBackwardNeck (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (epsilon K : ℝ) (U : Set M) (x : M) where

  neck : EpsilonNeck g

  epsilon_eq : neck.epsilon = epsilon

  center_eq : neck.center = x

  connection_eq : neck.connection = D

  carrier_subset : neck.carrier ⊆ U

  model : LocalNonnegativeBackwardModel g U x

  duration_eq : model.duration = neck.scale ^ 2 / 2

  captures_neck : neck.carrier ⊆ range model.embedding

  curvature_bound : letI := model.carrier.topologicalSpace
    letI := model.carrier.chartedSpace
    letI := model.carrier.isManifold
    ∀ t ∈ Icc (-model.duration) 0, ∀ p, model.embedding p ∈ neck.carrier →
      (model.flow.connection t).curvatureTensorNorm p ≤ K * neck.scale⁻¹ ^ 2




structure SingularNeckTube (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (epsilon : ℝ) where

  carrier : Set M

  carrier_open : IsOpen carrier

  cylinder : OpenCylinderModel carrier

  diameter_bound : ℝ

  diameter_bound_pos : 0 < diameter_bound

  diameter_le : intrinsicDiameter g carrier ≤ ENNReal.ofReal diameter_bound

  scalar_lower : ∀ x ∈ carrier, 3 ≤ D.scalarCurvature x

  initial_scalar_bound : ∃ B : ℝ, ∀ x ∈ cylinder.tail false (1 / 2),
    D.scalarCurvature x ≤ B

  scalar_at_end : ∀ B : ℝ, ∃ a ∈ Ioo (0 : ℝ) 1,
    ∀ x ∈ cylinder.tail true a, B < D.scalarCurvature x

  backward_curvature_bound : ℝ

  backward_curvature_bound_pos : 0 < backward_curvature_bound

  terminal_necks : ∀ x ∈ cylinder.tail true (1 / 2),
    Nonempty (QuantitativeBackwardNeck g D epsilon backward_curvature_bound carrier x)

  backward_models : ∀ x ∈ carrier, Nonempty (LocalNonnegativeBackwardModel g carrier x)




structure SingularNeckTubeWitness (epsilon : ℝ) where

  carrier : FlowCarrier.{0} 3

  metric : carrier.metric

  connection : letI := carrier.topologicalSpace
    letI := carrier.chartedSpace
    letI := carrier.isManifold
    LeviCivitaData metric

  tube : letI := carrier.topologicalSpace
    letI := carrier.measurableSpace
    letI := carrier.borelSpace
    letI := carrier.chartedSpace
    letI := carrier.isManifold
    letI := carrier.t2Space
    letI := carrier.t3Space
    SingularNeckTube metric connection epsilon

end PoincareConjecture.M28
