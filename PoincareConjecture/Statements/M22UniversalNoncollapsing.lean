import PoincareConjecture.Definitions.M22UniversalNoncollapsing
import PoincareConjecture.Statements.Ch04.Harnack
import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Statements.M12GeneralizedEquation
import PoincareConjecture.Statements.M13Rescaling
import PoincareConjecture.Statements.M14GeneralizedLGeometry
import PoincareConjecture.Statements.M15Noncollapsing
import PoincareConjecture.Statements.M17BlowupSetup
import PoincareConjecture.Statements.M20ThreeDimensionalClassification
import PoincareConjecture.Statements.M21AsymptoticVolume

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure M22UniversalNoncollapsingPredecessors (_n : ℕ) : Prop where
  tensor_calculus :
    ∀ (d : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
      (g : RiemannianMetric d M) (D : LeviCivitaData g), D.CurvatureTensorCalculus
  curvature_norm_zero :
    ∀ (d : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
      (g : RiemannianMetric d M) (D : LeviCivitaData g) (x : M),
      D.curvatureDerivativeNorm 0 x = D.curvatureTensorNorm x
  scalar_regular :
    ∀ (d : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
      (J : Set ℝ) (F : RicciFlow d M J),
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 d)) (𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ)
  scalar_evolution :
    ∀ (d : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
      (J : Set ℝ) (F : RicciFlow d M J) (t : ℝ), t ∈ J → ∀ x : M,
      HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x)
        ((F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x) J t
  curvature_evolution :
    ∀ (d : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
      (J : Set ℝ) (F : RicciFlow d M J) (t : ℝ), t ∈ J →
      ∀ (x : M) (v₁ v₂ v₃ v₄ : TangentSpace (𝓡 d) x),
      HasDerivWithinAt (fun s ↦ (F.connection s).curvatureTensor x v₁ v₂ v₃ v₄)
        ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
          ![v₁, v₂, v₃, v₄] + (F.connection t).curvatureReaction x v₁ v₂ v₃ v₄) J t
  ricci_evolution :
    ∀ (d : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
      (J : Set ℝ) (F : RicciFlow d M J) (t : ℝ), t ∈ J →
      ∀ (x : M) (v w : TangentSpace (𝓡 d) x),
      HasDerivWithinAt (fun s ↦ (F.connection s).ricci x v w)
        ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![v, w] +
          (F.connection t).ricciReaction x v w) J t
  local_derivative_estimates :
    ∀ (d k : ℕ) (K α r : ℝ), 0 < K → 0 < α → 0 < r →
      ∃ C : ℝ, 0 < C ∧
        ∀ (M : Type u) [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
          [T2Space M] [SecondCountableTopology M],
        ∀ T : ℝ, 0 < T → T ≤ α / K →
        ∀ (F : RicciFlow d M (Set.Icc 0 T)) (p : M),
          IsCompact (closure ((F.metric 0).ball p r)) →
          (∀ t ∈ Set.Icc 0 T, ∀ x ∈ (F.metric 0).ball p r,
            (F.connection t).curvatureTensorNorm x ≤ K) →
          ∀ t ∈ Set.Ioc 0 T, ∀ x ∈ (F.metric 0).ball p (r / 2),
            (F.connection t).curvatureDerivativeNorm k x ≤ C / t ^ ((k : ℝ) / 2)
  metric_edist_transport :
    ∀ (d : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
      [T3Space M] (g : RiemannianMetric d M) (x y : M),
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 d) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin d))
          (TangentSpace (𝓡 d) : M → Type _) :=
        ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 d) M
      edist x y = g.edist x y
  ancient_differential :
    ∀ (d : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
      ∀ F : RicciFlow d M (Set.Iic 0),
      (∀ t ≤ 0, MetricComplete (F.metric t)) →
      (∀ t ≤ 0, ∀ x : M,
        LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x) →
      (∀ t ≤ 0, ∃ K : ℝ, 0 ≤ K ∧
        ∀ x : M, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x) →
      (∀ t ≤ 0, ∃ x : M, (F.connection t).curvatureTensorNorm x ≠ 0) →
      ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 d) x,
        ∃ dR : ℝ,
          HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x) dR
            (Set.Iic 0) t ∧
          dR + 2 * (mvfderiv (𝓡 d)
            (fun y ↦ (F.connection t).scalarCurvature y) x) v +
            2 * (F.connection t).ricci x v v ≥ 0
  pointed_compactness :
    ∀ {d : ℕ} {T' T : ℝ}, T' < 0 → 0 < T →
      ∀ H : PointedRicciFlowCompactnessHypotheses d T' T,
        Nonempty (PointedRicciFlowCompactnessConclusion H)
  ordinary_windows : M14OrdinaryProviders.{u} 3
  ordinary_product :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] [Nonempty M]
      (I : SpacetimeInterval) (F : RicciFlow 3 M I.domain),
      ∃ R : OrdinaryProductRicciGeometry F.metric I,
        IntrinsicGeneralizedRicciEquation R.leafwiseConnection
  ordinary_rescaling :
    ∀ (d : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
      [T2Space M] [SecondCountableTopology M]
      (I : SpacetimeInterval) (F : RicciFlow d M I.domain)
      (Q : ℝ) (hQ : 0 < Q) (a : ℝ),
      Nonempty (OrdinaryParabolicRescaling F Q hQ a)
  metric_homothety :
    ∀ (d : ℕ) (M N : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold (𝓡 d) ∞ M]
      [TopologicalSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin d)) N] [IsManifold (𝓡 d) ∞ N]
      [T3Space M] [MeasurableSpace M] [BorelSpace M]
      [T3Space N] [MeasurableSpace N] [BorelSpace N]
      (g : RiemannianMetric d M) (h : RiemannianMetric d N)
      (f : Diffeomorph (𝓡 d) (𝓡 d) M N ∞) (Q : ℝ), 0 < Q →
      MetricHomothety g h f Q → MetricHomothetyCalculus g h f Q
  exponential :
    ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
      (I : SpacetimeInterval) (G : GeneralizedLGeometryTransport 3 X time I),
      Nonempty (M14ExponentialConclusion G)
  ordinary_capture :
    ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
      (I : SpacetimeInterval) (G : GeneralizedLGeometryTransport 3 X time I)
      (O : M14OrdinaryProviders.{u} 3),
      M14OrdinaryCaptureStatement G O
  noncollapse_generalized : M15GeneralizedUniformTheorem.{u} 3
  blowup_setup : AncientBlowupSetupTheory.{u} 3
  two_dimensional_compact :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (_K : AncientKappaSolution 2 M), CompactSpace M
  classified_limit :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M) (S : AncientRescalingSequence K),
      ∃ L : AncientAsymptoticSolitonLimitData S,
        ThreeDimensionalAsymptoticClassificationCertificate S L
  volume_ratio : ∀ d : ℕ, AsymptoticVolumeRatioTheory.{u} d

structure UniversalNoncollapsingConclusion (n : ℕ) where
  data : UniversalNoncollapsingData
  three_dimensional_alternative :
    ∀ {M₃ : Type u} [TopologicalSpace M₃]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₃]
      [IsManifold (𝓡 3) ∞ M₃] [MeasurableSpace M₃] [BorelSpace M₃]
      [T2Space M₃] [T3Space M₃] [SecondCountableTopology M₃]
      [ConnectedSpace M₃]
      (K : AncientKappaSolution 3 M₃),
      IsRoundAncientKappaSolution K ∨
        AncientKappaNoncollapsed K.flow data.universal_kappa
  nonround_is_universally_noncollapsed :
    ∀ {M₃ : Type u} [TopologicalSpace M₃]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₃]
      [IsManifold (𝓡 3) ∞ M₃] [MeasurableSpace M₃] [BorelSpace M₃]
      [T2Space M₃] [T3Space M₃] [SecondCountableTopology M₃]
      [ConnectedSpace M₃]
      (K : AncientKappaSolution 3 M₃),
      ¬ IsRoundAncientKappaSolution K →
        AncientKappaNoncollapsed K.flow data.universal_kappa
  asymptotic_volume_ratio_zero :
    ∀ {M' : Type u} [TopologicalSpace M']
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M']
      [IsManifold (𝓡 n) ∞ M'] [MeasurableSpace M'] [BorelSpace M']
      [T2Space M'] [T3Space M'] [SecondCountableTopology M']
      [ConnectedSpace M']
      (K : AncientKappaSolution n M'),
      AncientAsymptoticVolumeRatioZero K

end PoincareConjecture
