import PoincareConjecture.Statements.M16StructuralKappa
import PoincareConjecture.Statements.M22UniversalNoncollapsing
import PoincareConjecture.Statements.M23NormalizedKappaCompactness
import PoincareConjecture.Statements.M24ModelCertificates
import PoincareConjecture.Statements.M26CanonicalNeighborhoods









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure M27KappaAlternativePredecessors : Prop where
  tensor_calculus :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus
  scalar_regular :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J),
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ)
  scalar_evolution :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (t : ℝ), t ∈ J → ∀ x : M,
      HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x)
        ((F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x) J t
  curvature_evolution :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (t : ℝ), t ∈ J →
      ∀ (x : M) (v₁ v₂ v₃ v₄ : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s ↦ (F.connection s).curvatureTensor x v₁ v₂ v₃ v₄)
        ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x
          ![v₁, v₂, v₃, v₄] + (F.connection t).curvatureReaction x v₁ v₂ v₃ v₄) J t
  past_norm_le_scalar :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M),
      ∀ t b : ℝ, t ≤ b → b ≤ 0 → ∀ x : M,
        (K.flow.connection t).curvatureTensorNorm x ≤
          (K.flow.connection b).scalarCurvature x
  normalization :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 3 M) (p : M) (b : ℝ), b ≤ 0 →
        Nonempty (AncientKappaNormalization K p b)
  two_dimensional_classification :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      [SecondCountableTopology M] [ConnectedSpace M]
      (K : AncientKappaSolution 2 M),
      Nonempty (TwoDimensionalAncientRoundCertificate K)
  universal_noncollapsing :
    ∃ kappa₀ : ℝ, 0 < kappa₀ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        (K : AncientKappaSolution 3 M),
        ¬ IsRoundAncientKappaSolution K → AncientKappaNoncollapsed K.flow kappa₀
  normalized_compactness :
    ∀ N : NormalizedKappaCompactnessData,
      Nonempty (RedesignNormalizedKappaCompactnessConclusion N)
  model_refinement :
    ∀ {M₃ : Type u} [TopologicalSpace M₃]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₃]
      [IsManifold (𝓡 3) ∞ M₃] [MeasurableSpace M₃] [BorelSpace M₃]
      [T2Space M₃] [T3Space M₃] [SecondCountableTopology M₃]
      [ConnectedSpace M₃]
      {S : GradientShrinkingSolitonData 3 M₃}
      (G : ShrinkingSolitonFlow S),
      ∀ input : M24ModelInput G, RepairedModelCertificateTheory input
  separating_neck_tube :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M],
        ∀ g : RiemannianMetric 3 M, ∀ H : NeckOnlyCover g,
          H.epsilon ≤ epsilon₀ →
            (∀ N ∈ H.necks, N.IsSeparating) →
              Nonempty (CorrectedA19Conclusion g H)
  global_neck_cap :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (H : ConnectedNeckCapCover g),
        H.epsilon ≤ epsilon₀ → H.isWhole →
          Nonempty (GlobalNeckCapConclusion g H.epsilon H.cap_constant)
  noncompact_alternatives :
    ∃ epsilon₂ : ℝ, 0 < epsilon₂ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₂ →
        ∃ C₀ : ℝ, 0 < C₀ ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              ¬ IsCompact (Set.univ : Set M) →
              NoEmbeddedTrivialNormalProjectivePlane K →
              Nonempty (KappaNine88Conclusion K epsilon C₀)
  compact_alternatives :
    ∃ epsilon₃ : ℝ, 0 < epsilon₃ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₃ →
        ∃ C₁ : ℝ, 0 < C₁ ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              IsCompact (Set.univ : Set M) →
              Nonempty (RepairedCanonicalNeighborhoodCertificate K epsilon C₁)

end PoincareConjecture
