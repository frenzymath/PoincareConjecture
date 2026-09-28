import PoincareConjecture.Definitions.M27KappaAlternatives
import PoincareConjecture.Statements.M26CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Separation.Neck

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

noncomputable def soulScalar (K : AncientKappaSolution 3 M) (p : M) : ℝ :=
  (K.flow.connection 0).scalarCurvature p

section PointSoul

variable [NoncompactSpace M]

structure SoulCenteredCoreEstimate (K : AncientKappaSolution 3 M)
    (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
    (epsilon D D₁ : ℝ) : Prop where
  epsilon_pos : 0 < epsilon
  soul_scalar_pos : 0 < soulScalar K S.center
  radius_constant : 1 < D
  curvature_constant : 1 < D₁
  strong_outside : ∀ x : M,
    x ∉ (K.flow.metric 0).ball S.center
        (D * soulScalar K S.center ^ (-1 / 2 : ℝ)) →
      ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x
  sectional_bounds : ∀ x ∈ (K.flow.metric 0).ball S.center
        (D * soulScalar K S.center ^ (-1 / 2 : ℝ)),
      ∀ a b : TangentSpace (𝓡 3) x,
        (K.flow.metric 0).inner x a a = 1 →
        (K.flow.metric 0).inner x b b = 1 →
        (K.flow.metric 0).inner x a b = 0 →
        D₁⁻¹ * soulScalar K S.center <
            (K.flow.connection 0).sectionalCurvature x a b ∧
          (K.flow.connection 0).sectionalCurvature x a b <
            D₁ * soulScalar K S.center
  volume_bounds :
    ENNReal.ofReal
        (D₁ ^ (-3 / 2 : ℝ) * soulScalar K S.center ^ (-3 / 2 : ℝ)) <
        calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball S.center
            (D * soulScalar K S.center ^ (-1 / 2 : ℝ))) ∧
      calibratedMetricVolume (K.flow.metric 0)
          ((K.flow.metric 0).ball S.center
            (D * soulScalar K S.center ^ (-1 / 2 : ℝ))) <
        ENNReal.ofReal
          (D₁ ^ (3 / 2 : ℝ) * soulScalar K S.center ^ (-3 / 2 : ℝ))

end PointSoul

def UniformSoulCenteredCoreConclusionOfServices : Prop :=
  ∃ epsilonStar : ℝ, 0 < epsilonStar ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonStar →
      ∃ D D₁ : ℝ, 1 < D ∧ 1 < D₁ ∧
        ∀ {M : Type u} [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
          [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
          [T2Space M] [T3Space M] [SecondCountableTopology M]
          [ConnectedSpace M],
          ∀ K : AncientKappaSolution 3 M,
            (hnoncompact : ¬ IsCompact (Set.univ : Set M)) →
            M27PositiveSectionalCurvature K 0 →
            letI : NoncompactSpace M :=
              not_compactSpace_iff.mp (fun hcompact : CompactSpace M =>
                hnoncompact (isCompact_univ_iff.mpr hcompact))
            ∀ S : RiemannianMetric.PointSoulData (K.flow.metric 0),
              SoulCenteredCoreEstimate K S epsilon D D₁

def UniformSoulCenteredCoreConclusion (_P : M26CanonicalNeighborhoodPredecessors.{u}) : Prop :=
  UniformSoulCenteredCoreConclusionOfServices.{u}

end PoincareConjecture
