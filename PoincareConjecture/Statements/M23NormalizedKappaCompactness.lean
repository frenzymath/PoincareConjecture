import PoincareConjecture.Definitions.M23NormalizedKappaCompactness
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Statements.Ch05.Compactness
import PoincareConjecture.Statements.M13Rescaling
import PoincareConjecture.Definitions.M16StructuralKappa
import PoincareConjecture.Statements.M19TwoDimensionalClassification
import PoincareConjecture.Statements.M21AsymptoticVolume
import PoincareConjecture.Statements.M22UniversalNoncollapsing










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture





structure M23NormalizedKappaCompactnessPredecessors : Prop where
  tensor_calculus :
    ∀ (n : ℕ) (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus
  curvature_norm_zero :
    ∀ (n : ℕ) (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (g : RiemannianMetric n M) (D : LeviCivitaData g) (x : M),
      D.curvatureDerivativeNorm 0 x = D.curvatureTensorNorm x
  scalar_regular :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J),
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ)
  scalar_evolution :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (t : ℝ), t ∈ J → ∀ x : M,
      HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x)
        ((F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x) J t
  curvature_evolution :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (t : ℝ), t ∈ J →
      ∀ (x : M) (v₁ v₂ v₃ v₄ : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s ↦ (F.connection s).curvatureTensor x v₁ v₂ v₃ v₄)
        ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
          ![v₁, v₂, v₃, v₄] + (F.connection t).curvatureReaction x v₁ v₂ v₃ v₄) J t
  ricci_evolution :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (t : ℝ), t ∈ J →
      ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s ↦ (F.connection s).ricci x v w)
        ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![v, w] +
          (F.connection t).ricciReaction x v w) J t
  local_derivative_estimates :
    ∀ (k : ℕ) (K α r : ℝ), 0 < K → 0 < α → 0 < r →
      ∃ C : ℝ, 0 < C ∧
        ∀ (M : Type) [TopologicalSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
          [T2Space M] [SecondCountableTopology M],
        ∀ (T : ℝ), 0 < T → T ≤ α / K →
        ∀ (F : RicciFlow 3 M (Set.Icc 0 T)) (p : M),
          IsCompact (closure ((F.metric 0).ball p r)) →
          (∀ t ∈ Set.Icc 0 T, ∀ x ∈ (F.metric 0).ball p r,
            (F.connection t).curvatureTensorNorm x ≤ K) →
          ∀ t ∈ Set.Ioc 0 T, ∀ x ∈ (F.metric 0).ball p (r / 2),
            (F.connection t).curvatureDerivativeNorm k x ≤ C / t ^ ((k : ℝ) / 2)
  scalar_zero_rigidity :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] [ConnectedSpace M],
      ∀ (T : ℝ), 0 < T → ∀ F : RicciFlow 3 M (Set.Icc 0 T),
      (∀ t ∈ Set.Icc 0 T, (F.connection t).NonnegativeSectionalCurvature) →
      ∀ p : M, (F.connection T).scalarCurvature p = 0 →
        ∀ t ∈ Set.Icc 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x = 0
  pointed_compactness :
    ∀ {T' T : ℝ}, T' < 0 → 0 < T →
      ∀ H : PointedRicciFlowCompactnessHypotheses 3 T' T,
        Nonempty (PointedRicciFlowCompactnessConclusion H)
  ordinary_rescaling :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M]
      (I : SpacetimeInterval) (F : RicciFlow 3 M I.domain)
      (Q : ℝ) (hQ : 0 < Q) (a : ℝ),
      Nonempty (OrdinaryParabolicRescaling F Q hQ a)
  scalar_pos :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M),
      ∀ t : ℝ, t ≤ 0 → ∀ x : M, 0 < (K.flow.connection t).scalarCurvature x
  scalar_monotone :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M),
      ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x : M,
        (K.flow.connection s).scalarCurvature x ≤ (K.flow.connection t).scalarCurvature x
  past_norm_le_scalar :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M),
      ∀ t b : ℝ, t ≤ b → b ≤ 0 → ∀ x : M,
        (K.flow.connection t).curvatureTensorNorm x ≤
          (K.flow.connection b).scalarCurvature x
  ball_monotone :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M),
      ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x : M, ∀ r : ℝ,
        (K.flow.metric s).ball x r ⊆ (K.flow.metric t).ball x r
  two_dimensional_classification :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 2 M),
      Nonempty (TwoDimensionalAncientRoundCertificate K)
  ratio_antitone :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M) (t : ℝ), t ≤ 0 →
      ∀ p : M, AntitoneMetricBallVolumeRatio (K.flow.metric t) p
  zero_avr :
    ∀ (M : Type) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M), AncientAsymptoticVolumeRatioZero K





def M23LocalCurvatureEstimate
    {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧
    ∀ k : ℕ,
      let B := S.term k
      let Crr := B.carrier
      letI : TopologicalSpace Crr.carrier := Crr.topologicalSpace
      letI : MeasurableSpace Crr.carrier := Crr.measurableSpace
      letI : BorelSpace Crr.carrier := Crr.borelSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Crr.carrier := Crr.chartedSpace
      letI : IsManifold (𝓡 3) ∞ Crr.carrier := Crr.isManifold
      letI : T2Space Crr.carrier := Crr.t2Space
      letI : T3Space Crr.carrier := Crr.t3Space
      letI : SecondCountableTopology Crr.carrier := Crr.secondCountable
      letI : ConnectedSpace Crr.carrier := B.connectedSpace
      ∀ x : Crr.carrier,
        x ∈ Crr.metricBall (B.flow.flow.metric 0) B.base r →
          (B.flow.flow.connection 0).scalarCurvature x ≤ C




def M23AllTimeCurvatureControl
    {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧
    ∀ k : ℕ,
      let B := S.term k
      let Crr := B.carrier
      letI : TopologicalSpace Crr.carrier := Crr.topologicalSpace
      letI : MeasurableSpace Crr.carrier := Crr.measurableSpace
      letI : BorelSpace Crr.carrier := Crr.borelSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) Crr.carrier := Crr.chartedSpace
      letI : IsManifold (𝓡 3) ∞ Crr.carrier := Crr.isManifold
      letI : T2Space Crr.carrier := Crr.t2Space
      letI : T3Space Crr.carrier := Crr.t3Space
      letI : SecondCountableTopology Crr.carrier := Crr.secondCountable
      letI : ConnectedSpace Crr.carrier := B.connectedSpace
      ∀ t : ℝ, t ≤ 0 → ∀ x : Crr.carrier,
        x ∈ Crr.metricBall (B.flow.flow.metric 0) B.base r →
          |(B.flow.flow.connection t).curvatureTensorNorm x| ≤ C




def M23LimitBoundedCurvature {kappa : ℝ}
    (B : BasedKappaSolution kappa) : Prop :=
  let C := B.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : T2Space C.carrier := C.t2Space
  letI : T3Space C.carrier := C.t3Space
  letI : SecondCountableTopology C.carrier := C.secondCountable
  letI : ConnectedSpace C.carrier := B.connectedSpace
  ∀ t : ℝ, t ≤ 0 → ∃ K : ℝ, 0 ≤ K ∧ ∀ x : C.carrier,
    |(B.flow.flow.connection t).curvatureTensorNorm x| ≤ K





def M23TerminalNoncollapsing {kappa : ℝ}
    (B : BasedKappaSolution kappa) : Prop :=
  let C := B.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : T2Space C.carrier := C.t2Space
  letI : T3Space C.carrier := C.t3Space
  letI : SecondCountableTopology C.carrier := C.secondCountable
  letI : ConnectedSpace C.carrier := B.connectedSpace
  ∀ r₀ : ℝ, 0 < r₀ → ∀ p : C.carrier, ∀ r : ℝ, 0 < r → r ≤ r₀ →
    (∀ s ∈ Set.Ioc (-r ^ 2) 0, ∀ q ∈ (B.flow.flow.metric 0).ball p r,
      |(B.flow.flow.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
    ENNReal.ofReal (B.flow.kappa * r ^ 3) ≤
      calibratedMetricVolume (B.flow.flow.metric 0)
        ((B.flow.flow.metric 0).ball p r)

def M23TerminalCompleteAtZero {kappa : ℝ}
    (B : BasedKappaSolution kappa) : Prop :=
  let C := B.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : T2Space C.carrier := C.t2Space
  letI : T3Space C.carrier := C.t3Space
  letI : SecondCountableTopology C.carrier := C.secondCountable
  letI : ConnectedSpace C.carrier := B.connectedSpace
  FlowCarrier.metricComplete C (B.flow.flow.metric 0)

def M23TerminalBoundedAtZero {kappa : ℝ}
    (B : BasedKappaSolution kappa) : Prop :=
  let C := B.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : T2Space C.carrier := C.t2Space
  letI : T3Space C.carrier := C.t3Space
  letI : SecondCountableTopology C.carrier := C.secondCountable
  letI : ConnectedSpace C.carrier := B.connectedSpace
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x : C.carrier,
    |(B.flow.flow.connection 0).curvatureTensorNorm x| ≤ K

def M23TerminalNormalization {kappa : ℝ}
    (B : BasedKappaSolution kappa) : Prop :=
  let C := B.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : T2Space C.carrier := C.t2Space
  letI : T3Space C.carrier := C.t3Space
  letI : SecondCountableTopology C.carrier := C.secondCountable
  letI : ConnectedSpace C.carrier := B.connectedSpace
  (B.flow.flow.connection 0).scalarCurvature B.base = 1




noncomputable def M23TerminalMetricJet (r : ℕ)
    (f : ℝ × EuclideanSpace ℝ (Fin 3) → ℝ)
    (p : ℝ × EuclideanSpace ℝ (Fin 3)) :=
  iteratedFDerivWithin ℝ r f (Set.Iic (0 : ℝ) ×ˢ Set.univ) p





def M23TerminalMetricConvergence {kappa : ℝ}
    {S : NormalizedKappaSolutionSequence kappa}
    (G : M23InteriorConvergence S)
    (e : ∀ j, NormalizedKappaSpacetimeEmbedding
      (source := S.term (G.subsequence j)) (target := G.limit)
      (Set.Iic 0 ×ˢ G.exhaustion j)) : Prop :=
  let C := G.limit.carrier
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  letI : T2Space C.carrier := C.t2Space
  letI : T3Space C.carrier := C.t3Space
  letI : SecondCountableTopology C.carrier := C.secondCountable
  letI : ConnectedSpace C.carrier := G.limit.connectedSpace
  ∀ q : C.carrier, ∀ j r : ℕ,
    ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin 3)), IsCompact K →
    K ⊆ {p | p.1 ≤ 0 ∧ p.2 ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p.2 ∈ G.exhaustion j} →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
      ∀ a b : Fin 3, ∀ p ∈ K,
        ‖M23TerminalMetricJet r
            (normalizedKappaPullbackCoefficient
              (source := S.term (G.subsequence k)) (target := G.limit)
              (e k) q a b) p -
          M23TerminalMetricJet r
            (FlowCarrier.coordinateCoefficient C q
              (fun t x v w ↦ (G.limit.flow.flow.metric t).inner x v w) a b) p‖ < ε

structure M23TerminalExtension {kappa : ℝ}
    {S : NormalizedKappaSolutionSequence kappa}
    (G : M23InteriorConvergence S) : Prop where
  endpoint_in_domain : ∀ j,
    ((0 : ℝ), G.limit.base) ∈ Set.Iic 0 ×ˢ G.exhaustion j
  terminal_embedding :
    ∃ e : ∀ j, NormalizedKappaSpacetimeEmbedding
      (source := S.term (G.subsequence j)) (target := G.limit)
      (Set.Iic 0 ×ˢ G.exhaustion j),
      (∀ j,
        (∀ t ∈ G.time_window j, ∀ x ∈ G.exhaustion j,
          (e j).toFun (t, x) = (G.embedding j).toFun (t, x)) ∧
        (e j).toFun (0, G.limit.base) =
          (0, (S.term (G.subsequence j)).base)) ∧
      (∀ j (s t : ℝ) (x : G.limit.carrier.carrier),
        s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion j →
          ((e j).toFun (s, x)).2 = ((e j).toFun (t, x)).2) ∧
      M23TerminalMetricConvergence G e
  complete_at_zero : M23TerminalCompleteAtZero G.limit
  bounded_at_zero : M23TerminalBoundedAtZero G.limit
  noncollapsed_at_zero : M23TerminalNoncollapsing G.limit
  normalized_at_zero : M23TerminalNormalization G.limit

structure RedesignNormalizedKappaCompactnessConclusion
    (N : NormalizedKappaCompactnessData) where
  convergence : M23InteriorConvergence N.sequence
  local_curvature_estimate : M23LocalCurvatureEstimate N.sequence
  all_time_curvature_control : M23AllTimeCurvatureControl N.sequence
  limit_bounded_curvature : M23LimitBoundedCurvature convergence.limit
  terminal_extension : M23TerminalExtension convergence

end PoincareConjecture
