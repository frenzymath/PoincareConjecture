import PoincareConjecture.Definitions.M62Curve
import PoincareConjecture.Statements.Ch19.CurveEvolution
import PoincareConjecture.Statements.M62Geometry









set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}


noncomputable def m62SpatialEvolutionRhs (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (t x : ℝ) : ℝ :=
  let H := m62CurvatureVector F c t x
  let S := spatialUnitTangent F c t x
  let P := m62SpatialNormalDerivative F c t x
  let D := F.connection t
  let k2 := m62CurvatureSquared F c t x
  m62ArcSecondDerivative F c t (m62CurvatureSquared F c t) x -
    2 * (F.metric t).inner (c x t) P P + 2 * k2 ^ 2 -
    2 * D.ricci (c x t) H H + 4 * k2 * D.ricci (c x t) S S +
    2 * D.curvatureTensor (c x t) H S H S +
    2 * D.covariantTensorDerivative D.ricciEvaluation (c x t) ![H, S, S] -
    4 * D.covariantTensorDerivative D.ricciEvaluation (c x t) ![S, S, H]


structure M62SpatialEvolution (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) : Prop where
  speed_positive : ∀ t ∈ Set.Icc a b, ∀ x, 0 < curveSpeed F c t x
  speed_squared : ∀ t ∈ Set.Ioo a b, ∀ x,
    HasDerivAt (fun s ↦ (curveSpeed F c s x) ^ 2)
      (-2 * (m62TangentRicci F c t x + m62CurvatureSquared F c t x) *
        (curveSpeed F c t x) ^ 2) t
  speed_derivative : ∀ t ∈ Set.Ioo a b, ∀ x,
    HasDerivAt (fun s ↦ curveSpeed F c s x)
      (-(m62TangentRicci F c t x + m62CurvatureSquared F c t x) *
        curveSpeed F c t x) t
  commutator : ∀ f : ℝ × ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.univ ×ˢ Set.Ioo a b) → ∀ t ∈ Set.Ioo a b, ∀ x,
      deriv (fun s ↦ m62ArcDerivative F c s (fun y ↦ f (y, s)) x) t -
        m62ArcDerivative F c t (fun y ↦ deriv (fun s ↦ f (y, s)) t) x =
          (m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
            m62ArcDerivative F c t (fun y ↦ f (y, t)) x
  curvature_squared_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ ↦ m62CurvatureSquared F c z.2 z.1)
    (Set.univ ×ˢ Set.Ioo a b)
  exact_curvature : ∀ t ∈ Set.Ioo a b, ∀ x,
    HasDerivAt (fun s ↦ m62CurvatureSquared F c s x)
      (m62SpatialEvolutionRhs F c t x) t


structure M62CurveEstimates (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (K0 K1 K2 : ℝ) : Prop where
  spatial_squared_bound : ∀ t ∈ Set.Ioo a b, ∀ x,
    let P := m62SpatialNormalDerivative F c t x
    let k2 := m62CurvatureSquared F c t x
    deriv (fun s ↦ m62CurvatureSquared F c s x) t ≤
      m62ArcSecondDerivative F c t (m62CurvatureSquared F c t) x -
        2 * (F.metric t).inner (c x t) P P + 2 * k2 ^ 2 +
        m62C0 K0 K1 K2 * (k2 + m62Curvature F c t x)
  regularized_positive : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Icc a b, ∀ x,
    0 < m62RegularizedCurvature F c ε t x
  regularized_smooth : ∀ ε : ℝ, 0 < ε → ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ ↦ m62RegularizedCurvature F c ε z.2 z.1)
    (Set.univ ×ˢ Set.Ioo a b)
  regularized_gradient : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Ioo a b, ∀ x,
    let P := m62SpatialNormalDerivative F c t x
    (m62ArcDerivative F c t (m62RegularizedCurvature F c ε t) x) ^ 2 ≤
      (F.metric t).inner (c x t) P P
  regularized_bound : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Ioo a b, ∀ x,
    deriv (fun s ↦ m62RegularizedCurvature F c ε s x) t ≤
      m62ArcSecondDerivative F c t (m62RegularizedCurvature F c ε t) x +
        (m62Curvature F c t x) ^ 3 +
        m62C1 K0 K1 K2 * (m62RegularizedCurvature F c ε t x + 1)
  length_integrable : ∀ t ∈ Set.Icc a b,
    IntervalIntegrable (curveSpeed F c t) MeasureTheory.volume 0 curvePeriod
  total_curvature_integrable : ∀ t ∈ Set.Icc a b, IntervalIntegrable
    (fun x ↦ m62Curvature F c t x * curveSpeed F c t x)
    MeasureTheory.volume 0 curvePeriod
  regularized_integrable : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Icc a b,
    IntervalIntegrable (fun x ↦ m62RegularizedCurvature F c ε t x * curveSpeed F c t x)
      MeasureTheory.volume 0 curvePeriod
  length_continuous : ContinuousOn (m62Length F c) (Set.Icc a b)
  total_curvature_continuous : ContinuousOn (m62TotalCurvature F c) (Set.Icc a b)
  regularized_continuous : ∀ ε : ℝ, 0 < ε →
    ContinuousOn (m62RegularizedTotalCurvature F c ε) (Set.Icc a b)
  length_derivative : ∀ t ∈ Set.Ioo a b,
    HasDerivAt (m62Length F c)
      (-(∫ x in (0 : ℝ)..curvePeriod,
        (m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
          curveSpeed F c t x)) t
  length_bound : ∀ t ∈ Set.Ioo a b,
    deriv (m62Length F c) t ≤ ∫ x in (0 : ℝ)..curvePeriod,
      (K2 - m62CurvatureSquared F c t x) * curveSpeed F c t x
  length_scalar_bound : ∀ t ∈ Set.Ioo a b,
    deriv (m62Length F c) t ≤ K2 * m62Length F c t
  regularized_differentiable : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Ioo a b,
    DifferentiableAt ℝ (m62RegularizedTotalCurvature F c ε) t
  regularized_total_bound : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Ioo a b,
    deriv (m62RegularizedTotalCurvature F c ε) t ≤
      (m62C1 K0 K1 K2 + K2) * m62RegularizedTotalCurvature F c ε t +
        m62C1 K0 K1 K2 * m62Length F c t
  regularization_error : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Icc a b,
    0 ≤ m62RegularizedTotalCurvature F c ε t - m62TotalCurvature F c t ∧
      m62RegularizedTotalCurvature F c ε t - m62TotalCurvature F c t ≤
        ε * m62Length F c t
  total_curvature_integral : ∀ s t : ℝ,
    s ∈ Set.Icc a b → t ∈ Set.Icc a b → s ≤ t →
      m62TotalCurvature F c t - m62TotalCurvature F c s ≤
        ∫ r in s..t, (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F c r +
          m62C1 K0 K1 K2 * m62Length F c r
  total_curvature_forward : ∀ t ∈ Set.Ico a b, ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → t + h ∈ Set.Icc a b →
      (m62TotalCurvature F c (t + h) - m62TotalCurvature F c t) / h ≤
        (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F c t +
          m62C1 K0 K1 K2 * m62Length F c t + ε


noncomputable def m62LiftedCurvature {F : RicciFlow n M (Set.Icc a b)}
    (G : M62.SpacetimeData F) (c : ℝ → ℝ → M) (t : M62.OpenTime a b) (x : ℝ) :
    TangentSpace (𝓡 (n + 1)) (G.liftCurve c (x, t)) :=
  G.charts.horizontal (G.liftCurve c (x, t)) (m62CurvatureVector F c t x)

noncomputable def m62LiftedUnitTangent {F : RicciFlow n M (Set.Icc a b)}
    (G : M62.SpacetimeData F) (c : ℝ → ℝ → M) (t : M62.OpenTime a b) (x : ℝ) :
    TangentSpace (𝓡 (n + 1)) (G.liftCurve c (x, t)) :=
  G.charts.horizontal (G.liftCurve c (x, t)) (spatialUnitTangent F c t x)


noncomputable def m62SpacetimeNormalDerivative {F : RicciFlow n M (Set.Icc a b)}
    (G : M62.SpacetimeData F) (c : ℝ → ℝ → M) (t : M62.OpenTime a b) (x : ℝ) :
    TangentSpace (𝓡 (n + 1)) (G.liftCurve c (x, t)) :=
  let A := (curveSpeed F c t x)⁻¹ •
    G.covariantAlong (fun y ↦ G.liftCurve c (y, t)) (m62LiftedCurvature G c t) x
  let S := m62LiftedUnitTangent G c t x
  A - G.metric.inner (G.liftCurve c (x, t)) A S • S


noncomputable def m62SpacetimeEvolutionRhs {F : RicciFlow n M (Set.Icc a b)}
    (G : M62.SpacetimeData F) (c : ℝ → ℝ → M) (t : M62.OpenTime a b) (x : ℝ) : ℝ :=
  let H := m62CurvatureVector F c t x
  let S := spatialUnitTangent F c t x
  let P := m62SpacetimeNormalDerivative G c t x
  let D := F.connection t
  let k2 := m62CurvatureSquared F c t x
  m62ArcSecondDerivative F c t (m62CurvatureSquared F c t) x -
    2 * G.metric.inner (G.liftCurve c (x, t)) P P + 2 * k2 ^ 2 -
    2 * D.ricci (c x t) H H + 4 * k2 * D.ricci (c x t) S S +
    2 * G.connection.curvatureTensor (G.liftCurve c (x, t))
      (G.liftedTimeVelocity c (x, t)) (m62LiftedUnitTangent G c t x)
      (m62LiftedCurvature G c t x) (m62LiftedUnitTangent G c t x) +
    2 * D.ricci (c x t) S S * D.ricci (c x t) H H -
    2 * D.covariantTensorDerivative D.ricciEvaluation (c x t) ![S, S, H]


structure M62CurveLaws {F : RicciFlow n M (Set.Icc a b)}
    (G : M62.SpacetimeData F) (c : ℝ → ℝ → M) : Prop where
  spatial : M62SpatialEvolution F c
  lifted_time : ∀ (t : M62.OpenTime a b) (x : ℝ),
    G.liftedTimeVelocity c (x, t) =
      m62LiftedCurvature G c t x + G.charts.timeVector (G.liftCurve c (x, t))
  normal_norm : ∀ (t : M62.OpenTime a b) (x : ℝ),
    let P := m62SpacetimeNormalDerivative G c t x
    let Pg := m62SpatialNormalDerivative F c t x
    G.metric.inner (G.liftCurve c (x, t)) P P =
      (F.metric t).inner (c x t) Pg Pg +
        ((F.connection t).ricci (c x t) (spatialUnitTangent F c t x)
          (m62CurvatureVector F c t x)) ^ 2
  exact_curvature : ∀ (t : M62.OpenTime a b) (x : ℝ),
    HasDerivAt (fun s ↦ m62CurvatureSquared F c s x)
      (m62SpacetimeEvolutionRhs G c t x) t
  regularized_gradient : ∀ ε : ℝ, 0 < ε → ∀ (t : M62.OpenTime a b) (x : ℝ),
    let P := m62SpacetimeNormalDerivative G c t x
    (m62ArcDerivative F c t (m62RegularizedCurvature F c ε t) x) ^ 2 ≤
      G.metric.inner (G.liftCurve c (x, t)) P P


def M62SpacetimeEstimate {F : RicciFlow n M (Set.Icc a b)}
    (G : M62.SpacetimeData F) (c : ℝ → ℝ → M) (K0 K1 K2 : ℝ) : Prop :=
  ∀ (t : M62.OpenTime a b) (x : ℝ),
    let P := m62SpacetimeNormalDerivative G c t x
    let k2 := m62CurvatureSquared F c t x
    deriv (fun s ↦ m62CurvatureSquared F c s x) t ≤
      m62ArcSecondDerivative F c t (m62CurvatureSquared F c t) x -
        2 * G.metric.inner (G.liftCurve c (x, t)) P P + 2 * k2 ^ 2 +
        m62C0 K0 K1 K2 * (k2 + m62Curvature F c t x)


structure M62CurveTheory (F : RicciFlow n M (Set.Icc a b)) where
  spacetime : M62.SpacetimeData F
  spacetime_identities : M62.SpacetimeIdentities spacetime
  curves : ∀ c : ℝ → ℝ → M, M62ShrinkingCurve F c → M62CurveLaws spacetime c
  estimates : ∀ K0 K1 K2 : ℝ, 0 ≤ K0 → 0 ≤ K1 → 0 ≤ K2 →
    CurveEvolutionAmbientBounds F K0 K1 K2 →
      ∀ c : ℝ → ℝ → M, M62ShrinkingCurve F c →
        M62CurveEstimates F c K0 K1 K2 ∧ M62SpacetimeEstimate spacetime c K0 K1 K2


noncomputable def m62Slope {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (t x : ℝ) : ℝ :=
  (P.flow.metric t).inner (c x t) (spatialUnitTangent P.flow c t x)
    (P.charts.circleUnit (c x t))


structure M62SlopeLaws {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (K2 : ℝ) : Prop where
  abs_le_one : ∀ t ∈ Set.Icc a b, ∀ x, |m62Slope P c t x| ≤ 1
  evolution : ∀ t ∈ Set.Ioo a b, ∀ x,
    HasDerivAt (fun s ↦ m62Slope P c s x)
      (m62ArcSecondDerivative P.flow c t (m62Slope P c t) x +
        (m62CurvatureSquared P.flow c t x + m62TangentRicci P.flow c t x) *
          m62Slope P c t x) t
  lower_bound : ∀ t ∈ Set.Ioo a b, ∀ x, 0 ≤ m62Slope P c t x →
    m62ArcSecondDerivative P.flow c t (m62Slope P c t) x - K2 * m62Slope P c t x ≤
      deriv (fun s ↦ m62Slope P c s x) t


structure M62CircleConclusion (F : RicciFlow n M (Set.Icc a b))
    (circumference K0 K1 K2 : ℝ) where
  product : M62.CircleProductData F circumference
  product_identities : M62.CircleProductIdentities product
  bounds : CurveEvolutionAmbientBounds product.flow K0 K1 K2
  curve_theory : M62CurveTheory product.flow
  spacetime_parallel : M62.CircleUnitSpacetimeParallel product curve_theory.spacetime
  slope : ∀ c : ℝ → ℝ → product.charts.Point,
    M62ShrinkingCurve product.flow c → M62SlopeLaws product c K2


structure M62FlowConclusion (F : RicciFlow n M (Set.Icc a b)) where
  K0 : ℝ
  K1 : ℝ
  K2 : ℝ
  nonnegative : 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2
  bounds : CurveEvolutionAmbientBounds F K0 K1 K2
  curve_theory : M62CurveTheory F
  circle_products : ∀ circumference : ℝ, 0 < circumference →
    Nonempty (M62CircleConclusion F circumference K0 K1 K2)


def M62CurvatureService : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus


def M62CurveEvolutionTheory : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] (a b : ℝ)
    (F : RicciFlow n M (Set.Icc a b)),
    IsCompact (Set.univ : Set M) → Nonempty (M62FlowConclusion F)

end PoincareConjecture
