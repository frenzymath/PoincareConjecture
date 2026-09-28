import PoincareConjecture.Definitions.Ch04.Harnack
import PoincareConjecture.Statements.Ch04.CurvatureTheory









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

structure HarnackAncientTheory : Prop where
  metric_edist_transport :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T3Space M] (g : RiemannianMetric n M) (x y : M),
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
      edist x y = g.edist x y
  finite_differential :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [T3Space M] [SecondCountableTopology M],
      ∀ T₀ T₁ : ℝ, T₀ < T₁ →
      ∀ F : RicciFlow n M (Set.Ioo T₀ T₁),
      (∀ t ∈ Set.Ioo T₀ T₁, MetricComplete (F.metric t)) →
      (∀ t ∈ Set.Ioo T₀ T₁, ∀ x : M,
        LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x) →
      (∀ t ∈ Set.Ioo T₀ T₁, ∃ K : ℝ, 0 ≤ K ∧
        ∀ x : M, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x) →
      ∀ t ∈ Set.Ioo T₀ T₁, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
        ∃ dR : ℝ,
          HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x) dR
            (Set.Ioo T₀ T₁) t ∧
          dR + (F.connection t).scalarCurvature x / (t - T₀) +
              2 * (mvfderiv (𝓡 n)
                (fun y ↦ (F.connection t).scalarCurvature y) x) v +
              2 * (F.connection t).ricci x v v ≥ 0
  finite_integrated :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [T3Space M] [SecondCountableTopology M],
      ∀ T₀ T₁ t₁ t₂ : ℝ, T₀ < t₁ → t₁ < t₂ → t₂ < T₁ →
      ∀ F : RicciFlow n M (Set.Ioo T₀ T₁),
      (∀ t ∈ Set.Ioo T₀ T₁, MetricComplete (F.metric t)) →
      (∀ t ∈ Set.Ioo T₀ T₁, ∀ x : M,
        LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x) →
      (∀ t ∈ Set.Ioo T₀ T₁, ∃ K : ℝ, 0 ≤ K ∧
        ∀ x : M, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x) →
      ∀ γ : ℝ → M, ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Set.Icc t₁ t₂) →
      ∀ x₁ x₂ : M, γ t₁ = x₁ → γ t₂ = x₂ →
      (F.connection t₂).scalarCurvature x₂ * (t₂ - T₀) ≥
        (F.connection t₁).scalarCurvature x₁ * (t₁ - T₀) *
          Real.exp (-spacetimeEnergy F γ t₁ t₂ / 2)
  ancient_differential :
      ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
      ∀ F : RicciFlow n M (Set.Iic 0),
      (∀ t ≤ 0, MetricComplete (F.metric t)) →
      (∀ t ≤ 0, ∀ x : M,
        LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x) →
      (∀ t ≤ 0, ∃ K : ℝ, 0 ≤ K ∧
        ∀ x : M, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x) →
      (∀ t ≤ 0, ∃ x : M, (F.connection t).curvatureTensorNorm x ≠ 0) →
      ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
        ∃ dR : ℝ,
          HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x) dR
            (Set.Iic 0) t ∧
          dR + 2 * (mvfderiv (𝓡 n)
            (fun y ↦ (F.connection t).scalarCurvature y) x) v +
            2 * (F.connection t).ricci x v v ≥ 0
  ancient_integrated :
    ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
      ∀ F : RicciFlow n M (Set.Iic 0),
      (∀ t ≤ 0, MetricComplete (F.metric t)) →
      (∀ t ≤ 0, ∀ x : M,
        LeviCivitaData.NonnegativeCurvatureOperator (F.connection t) x) →
      (∀ t ≤ 0, ∃ K : ℝ, 0 ≤ K ∧
        ∀ x : M, LeviCivitaData.CurvatureOperatorBound (F.connection t) K x) →
      (∀ t ≤ 0, ∃ x : M, (F.connection t).curvatureTensorNorm x ≠ 0) →
      ∀ t₁ t₂ : ℝ, t₁ < t₂ → t₂ ≤ 0 → ∀ γ : ℝ → M,
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Set.Icc t₁ t₂) →
      ∀ x₁ x₂ : M, γ t₁ = x₁ → γ t₂ = x₂ →
      (F.connection t₂).scalarCurvature x₂ ≥
        (F.connection t₁).scalarCurvature x₁ *
          Real.exp (-spacetimeEnergy F γ t₁ t₂ / 2)

end PoincareConjecture
