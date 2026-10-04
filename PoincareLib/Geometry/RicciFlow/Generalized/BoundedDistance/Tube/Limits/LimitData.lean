import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Dense

/-!
# The actual limiting-tube consumer data

These are the geometric outputs still to construct in Claims 10.3-10.11
of Morgan--Tian, pp. 248-255. They are inputs to the cone contradiction
of sections 10.4-10.6, pp. 255-265. No existence or impossibility result
is asserted here. See task derivations 07 and 12.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- An actual local nonnegative backward flow whose top metric maps to
the displayed limiting metric. Lifetimes are local, as in Claim 10.11,
p. 255, and task derivation 12. -/
structure LocalNonnegativeBackwardModel (g : RiemannianMetric 3 M)
    (U : Set M) (x : M) where
  /-- The actual smooth local flow carrier. -/
  carrier : FlowCarrier.{0} 3
  /-- A strictly positive backward duration. -/
  duration : ℝ
  /-- The time interval is nontrivial. -/
  duration_pos : 0 < duration
  /-- The included top slice is part of an actual Ricci flow. -/
  flow : letI := carrier.topologicalSpace
    letI := carrier.chartedSpace
    letI := carrier.isManifold
    RicciFlow 3 carrier.carrier (Icc (-duration) 0)
  /-- The fixed spatial map into the limiting tube. -/
  embedding : carrier.carrier → M
  /-- The map gives an open neighborhood in the actual topology. -/
  embedding_open : letI := carrier.topologicalSpace
    Topology.IsOpenEmbedding embedding
  /-- The map is a smooth local diffeomorphism. -/
  embedding_smooth : letI := carrier.topologicalSpace
    letI := carrier.chartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ embedding
  /-- The neighborhood stays within the tube. -/
  image_subset : range embedding ⊆ U
  /-- The chosen tube point is captured. -/
  captures : x ∈ range embedding
  /-- Equality is of the actual top metric and its tensor pullback. -/
  metric_at_zero : letI := carrier.topologicalSpace
    letI := carrier.chartedSpace
    letI := carrier.isManifold
    ∀ p v w, g.inner (embedding p)
      (mfderiv (𝓡 3) (𝓡 3) embedding p v)
      (mfderiv (𝓡 3) (𝓡 3) embedding p w) = (flow.metric 0).inner p v w
  /-- Pinching has passed to the entire local backward model. -/
  nonnegative : letI := carrier.topologicalSpace
    letI := carrier.chartedSpace
    letI := carrier.isManifold
    ∀ t ∈ Icc (-duration) 0, ∀ p,
      LeviCivitaData.NonnegativeCurvatureOperator (flow.connection t) p

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

/-- A terminal neck retains a curvature-scale backward window and a
uniform curvature bound on its entire fixed spatial carrier. These are
the quantitative inputs used after rescaling in section 10.5, pp. 263-264;
arbitrary positive pointwise lifetimes do not supply them. -/
structure QuantitativeBackwardNeck (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (epsilon K : ℝ) (U : Set M) (x : M) where
  /-- The actual top-slice neck. -/
  neck : EpsilonNeck g
  /-- Its accuracy is the displayed limiting accuracy. -/
  epsilon_eq : neck.epsilon = epsilon
  /-- Its center is the tested tube point. -/
  center_eq : neck.center = x
  /-- Its connection is the one used for the limiting scalar. -/
  connection_eq : neck.connection = D
  /-- The full top-slice neck stays in the tube. -/
  carrier_subset : neck.carrier ⊆ U
  /-- The actual nonnegative backward flow. -/
  model : LocalNonnegativeBackwardModel g U x
  /-- Half of the normalized neck time survives at every center. -/
  duration_eq : model.duration = neck.scale ^ 2 / 2
  /-- The whole fixed spatial neck is captured by the backward model. -/
  captures_neck : neck.carrier ⊆ range model.embedding
  /-- The bound is uniform on the entire fixed neck and backward window. -/
  curvature_bound : letI := model.carrier.topologicalSpace
    letI := model.carrier.chartedSpace
    letI := model.carrier.isManifold
    ∀ t ∈ Icc (-model.duration) 0, ∀ p, model.embedding p ∈ neck.carrier →
      (model.flow.connection t).curvatureTensorNorm p ≤ K * neck.scale⁻¹ ^ 2

/-- The geometric limiting tube consumed by sections 10.4-10.6. Its
existence from counterexamples and its impossibility remain separate
proof obligations (Claims 10.3-10.11; task derivations 07 and 12). -/
structure SingularNeckTube (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (epsilon : ℝ) where
  /-- The actual open tube region. -/
  carrier : Set M
  /-- Openness is in the smooth limiting carrier. -/
  carrier_open : IsOpen carrier
  /-- The cylinder parametrization labels the regular and singular ends. -/
  cylinder : OpenCylinderModel carrier
  /-- A finite intrinsic diameter bound. -/
  diameter_bound : ℝ
  /-- The displayed bound is positive. -/
  diameter_bound_pos : 0 < diameter_bound
  /-- Paths are confined to the actual tube in this diameter assertion. -/
  diameter_le : intrinsicDiameter g carrier ≤ ENNReal.ofReal diameter_bound
  /-- The normalized positive scalar lower bound. -/
  scalar_lower : ∀ x ∈ carrier, 3 ≤ D.scalarCurvature x
  /-- The initial end stays in a bounded-curvature part. -/
  initial_scalar_bound : ∃ B : ℝ, ∀ x ∈ cylinder.tail false (1 / 2),
    D.scalarCurvature x ≤ B
  /-- Scalar tends uniformly to infinity at the other end. -/
  scalar_at_end : ∀ B : ℝ, ∃ a ∈ Ioo (0 : ℝ) 1,
    ∀ x ∈ cylinder.tail true a, B < D.scalarCurvature x
  /-- A uniform finite curvature coefficient chosen before the neck center. -/
  backward_curvature_bound : ℝ
  /-- The common coefficient is positive. -/
  backward_curvature_bound_pos : 0 < backward_curvature_bound
  /-- Reverse persistence retains actual quantitative backward neck models. -/
  terminal_necks : ∀ x ∈ cylinder.tail true (1 / 2),
    Nonempty (QuantitativeBackwardNeck g D epsilon backward_curvature_bound carrier x)
  /-- Included-time local backward models, with no common tube-wide lifetime. -/
  backward_models : ∀ x ∈ carrier, Nonempty (LocalNonnegativeBackwardModel g carrier x)

/-- A limiting-tube witness on the actual countable carrier produced by
partial compactness. It does not assert such a witness exists (Claims
10.3-10.11; task derivation 12). -/
structure SingularNeckTubeWitness (epsilon : ℝ) where
  /-- The actual spatial limit carrier. -/
  carrier : FlowCarrier.{0} 3
  /-- Its positive smooth metric. -/
  metric : carrier.metric
  /-- The compatible connection used by all tube certificates. -/
  connection : letI := carrier.topologicalSpace
    letI := carrier.chartedSpace
    letI := carrier.isManifold
    LeviCivitaData metric
  /-- All geometric tube data in the displayed topology and metric. -/
  tube : letI := carrier.topologicalSpace
    letI := carrier.measurableSpace
    letI := carrier.borelSpace
    letI := carrier.chartedSpace
    letI := carrier.isManifold
    letI := carrier.t2Space
    letI := carrier.t3Space
    SingularNeckTube metric connection epsilon

end PoincareMT.M28
