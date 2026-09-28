import PoincareConjecture.Definitions.Ch09.AsymptoticSoliton
import PoincareConjecture.Definitions.M13OrdinaryRescaling
















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]


structure AncientKappaNormalization (K : AncientKappaSolution n M)
    (p : M) (b : ℝ) where
  scale : ℝ
  scale_eq : scale = (K.flow.connection b).scalarCurvature p
  scale_pos : 0 < scale
  target : AncientKappaSolution n M
  target_kappa : target.kappa = K.kappa
  metric_eq : ∀ s : ℝ, ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
    (target.flow.metric s).inner x v w =
      scale * (K.flow.metric (b + s / scale)).inner x v w
  scalar_eq : ∀ s : ℝ, s ≤ 0 → ∀ x : M,
    (target.flow.connection s).scalarCurvature x =
      (K.flow.connection (b + s / scale)).scalarCurvature x / scale
  curvature_norm_eq : ∀ s : ℝ, s ≤ 0 → ∀ x : M,
    (target.flow.connection s).curvatureTensorNorm x =
      (K.flow.connection (b + s / scale)).curvatureTensorNorm x / scale
  normalized_scalar :
    (target.flow.connection 0).scalarCurvature p = 1


structure AncientKappaStructuralData (K : AncientKappaSolution n M) where
  scalar_pos : ∀ t : ℝ, t ≤ 0 → ∀ x : M,
    0 < (K.flow.connection t).scalarCurvature x
  norm_le_scalar : ∀ t : ℝ, t ≤ 0 → ∀ x : M,
    (K.flow.connection t).curvatureTensorNorm x ≤
      (K.flow.connection t).scalarCurvature x
  scalar_le_dim_norm : ∀ t : ℝ, t ≤ 0 → ∀ x : M,
    (K.flow.connection t).scalarCurvature x ≤
      (n : ℝ) * (K.flow.connection t).curvatureTensorNorm x
  ricci_nonnegative : ∀ t : ℝ, t ≤ 0 → ∀ x : M,
    ∀ v : TangentSpace (𝓡 n) x,
    0 ≤ (K.flow.connection t).ricci x v v
  ricci_upper_bound : ∀ t : ℝ, t ≤ 0 → ∀ x : M,
    ∀ v : TangentSpace (𝓡 n) x,
    (K.flow.connection t).ricci x v v ≤
      (K.flow.connection t).scalarCurvature x *
        (K.flow.metric t).inner x v v
  scalar_derivative_nonnegative : ∀ t : ℝ, t ≤ 0 → ∀ x : M,
    ∃ dR : ℝ,
      HasDerivWithinAt
        (fun s ↦ (K.flow.connection s).scalarCurvature x) dR
        (Set.Iic 0) t ∧ 0 ≤ dR
  scalar_monotone : ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x : M,
    (K.flow.connection s).scalarCurvature x ≤
      (K.flow.connection t).scalarCurvature x
  metric_monotone : ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x : M,
    ∀ v : TangentSpace (𝓡 n) x,
    (K.flow.metric t).inner x v v ≤ (K.flow.metric s).inner x v v
  edist_monotone : ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x y : M,
    (K.flow.metric t).edist x y ≤ (K.flow.metric s).edist x y
  ball_monotone : ∀ s t : ℝ, s ≤ t → t ≤ 0 → ∀ x : M, ∀ r : ℝ,
    RiemannianMetric.ball (K.flow.metric s) x r ⊆
      RiemannianMetric.ball (K.flow.metric t) x r
  past_norm_le_scalar : ∀ t b : ℝ, t ≤ b → b ≤ 0 → ∀ x : M,
    (K.flow.connection t).curvatureTensorNorm x ≤
      (K.flow.connection b).scalarCurvature x
  fixed_set_bound : ∀ (b : ℝ), b ≤ 0 → ∀ (A : Set M) (C : ℝ),
    (∀ x ∈ A, (K.flow.connection b).scalarCurvature x ≤ C) →
    ∀ t, t ≤ b → ∀ x ∈ A,
      (K.flow.connection t).curvatureTensorNorm x ≤ C
  whole_past_bound : ∀ b : ℝ, b ≤ 0 → ∃ C : ℝ, 0 < C ∧
    ∀ t, t ≤ b → ∀ x : M,
      |(K.flow.connection t).curvatureTensorNorm x| ≤ C
  normalization : ∀ (p : M) (b : ℝ), b ≤ 0 →
    AncientKappaNormalization K p b

end PoincareConjecture
