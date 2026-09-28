import PoincareConjecture.Definitions.M27ProductModels

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology BigOperators

universe u v

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

def M27PositiveSectionalCurvature (K : AncientKappaSolution 3 M) (t : ℝ) : Prop :=
  ∀ x : M, ∀ a b : TangentSpace (𝓡 3) x,
    (K.flow.metric t).inner x a a = 1 →
    (K.flow.metric t).inner x b b = 1 →
    (K.flow.metric t).inner x a b = 0 →
      0 < (K.flow.connection t).sectionalCurvature x a b

structure M27CanonicalCap (K : AncientKappaSolution 3 M)
    (t : ℝ) (x : M) (epsilon C : ℝ) where
  time_mem : t ≤ 0
  cap : CapCertificate (K.flow.metric t)
  epsilon_eq : cap.epsilon = epsilon
  constant_le : cap.cap_constant ≤ C
  connection_eq : cap.connection = K.flow.connection t
  contains : x ∈ cap.core

structure M27CanonicalComponent (K : AncientKappaSolution 3 M) (t C : ℝ) where
  time_mem : t ≤ 0
  constant_pos : 0 < C
  compact : IsCompact (Set.univ : Set M)
  topology :
    Nonempty (ClosedComponentCertificate .threeSphere (Set.univ : Set M)) ∨
      Nonempty (ClosedComponentCertificate .realProjectiveThree (Set.univ : Set M))
  positive : M27PositiveSectionalCurvature K t
  scalar_sup_pos : 0 < scalarCurvatureSup (K.flow.metric t) (K.flow.connection t)
  uniform_sectional_lower : ∃ B : ℝ, C⁻¹ < B ∧
    ∀ x : M, ∀ a b : TangentSpace (𝓡 3) x,
      (K.flow.metric t).inner x a a = 1 →
      (K.flow.metric t).inner x b b = 1 →
      (K.flow.metric t).inner x a b = 0 →
        B * scalarCurvatureSup (K.flow.metric t) (K.flow.connection t) ≤
          (K.flow.connection t).sectionalCurvature x a b
  diameter_lower :
    C⁻¹ * sSup (Set.range (fun x : M =>
      (K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ))) <
      metricDiameter (K.flow.metric t) Set.univ
  diameter_upper :
    metricDiameter (K.flow.metric t) Set.univ <
      C * sInf (Set.range (fun x : M =>
        (K.flow.connection t).scalarCurvature x ^ (-1 / 2 : ℝ)))

noncomputable def m27RescaledPullbackMetric
    {Z : Type v} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Z] [IsManifold (𝓡 3) ∞ Z]
    (g : RiemannianMetric 3 M) (scale : ℝ)
    (f : Diffeomorph (𝓡 3) (𝓡 3) Z M ∞) : CovariantTensorEvaluation 3 Z 2 :=
  fun z a => scale * g.inner (f z)
    (mfderiv (𝓡 3) (𝓡 3) f z (a 0)) (mfderiv (𝓡 3) (𝓡 3) f z (a 1))

structure M27EpsilonRoundComponent (K : AncientKappaSolution 3 M)
    (t epsilon : ℝ) where
  time_mem : t ≤ 0
  epsilon_pos : 0 < epsilon
  compact : IsCompact (Set.univ : Set M)
  reference : Type u
  reference_topology : TopologicalSpace reference
  reference_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) reference
  reference_manifold : IsManifold (𝓡 3) ∞ reference
  reference_compact : IsCompact (Set.univ : Set reference)
  reference_connected : ConnectedSpace reference
  reference_metric : RiemannianMetric 3 reference
  reference_connection : LeviCivitaData reference_metric
  reference_sectional_one : ∀ z : reference, ∀ a b : TangentSpace (𝓡 3) z,
    reference_metric.inner z a a = 1 → reference_metric.inner z b b = 1 →
      reference_metric.inner z a b = 0 →
        reference_connection.sectionalCurvature z a b = 1
  scale : ℝ
  scale_pos : 0 < scale
  identification : Diffeomorph (𝓡 3) (𝓡 3) reference M ∞
  comparison : ∃ B : ℝ, B < epsilon ^ 2 ∧ ∀ z : reference,
    reference_metric.tensorNorm
        (fun y a => m27RescaledPullbackMetric (K.flow.metric t) scale identification y a -
          reference_metric.inner y (a 0) (a 1)) z ^ 2 +
      (∑ j ∈ Finset.range (Nat.floor epsilon⁻¹),
        reference_metric.tensorNorm
          (reference_connection.iteratedCovariantTensorDerivative
            (m27RescaledPullbackMetric (K.flow.metric t) scale identification) (j + 1)) z ^ 2)
      ≤ B

inductive M27StrongCanonicalNeighborhood (K : AncientKappaSolution 3 M)
    (t : ℝ) (x : M) (epsilon C : ℝ) : Prop where
  | neck (N : StrongEvolvingNeck K t epsilon) (center_eq : N.center = x)
  | cap (N : M27CanonicalCap K t x epsilon C)
  | component (N : M27CanonicalComponent K t C)
  | round (N : M27EpsilonRoundComponent K t epsilon)

end PoincareConjecture
