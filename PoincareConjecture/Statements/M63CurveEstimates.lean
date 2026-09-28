import PoincareConjecture.Definitions.M63Ramp










set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}



structure M63AmbientGeometry (F : RicciFlow n M (Set.Icc a b)) where
  K0 : ℝ
  K1 : ℝ
  K2 : ℝ
  nonnegative : 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2
  bounds : CurveEvolutionAmbientBounds F K0 K1 K2
  product : ∀ circumference : ℝ, 0 < circumference →
    M62.CircleProductData F circumference
  product_identities : ∀ circumference (h : 0 < circumference),
    M62.CircleProductIdentities (product circumference h)
  product_bounds : ∀ circumference (h : 0 < circumference),
    CurveEvolutionAmbientBounds (product circumference h).flow K0 K1 K2




structure M63C2CurveEstimates (F : RicciFlow n M (Set.Icc a b))
    (c : ℝ → ℝ → M) (T K0 K1 K2 : ℝ) : Prop where
  length_continuous : ContinuousOn (m62Length F c) (Set.Icc a T)
  total_curvature_continuous : ContinuousOn (m62TotalCurvature F c) (Set.Icc a T)
  regularized_positive : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Icc a T, ∀ x,
    0 < m62RegularizedCurvature F c ε t x
  regularized_time : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Ioo a T, ∀ x,
    DifferentiableAt ℝ (fun s => m62RegularizedCurvature F c ε s x) t
  regularized_bound : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Ioo a T, ∀ x,
    deriv (fun s => m62RegularizedCurvature F c ε s x) t ≤
      m62ArcSecondDerivative F c t (m62RegularizedCurvature F c ε t) x +
        (m62Curvature F c t x) ^ 3 +
        m62C1 K0 K1 K2 * (m62RegularizedCurvature F c ε t x + 1)
  length_derivative : ∀ t ∈ Set.Ioo a T,
    HasDerivAt (m62Length F c)
      (-(∫ x in (0 : ℝ)..curvePeriod,
        (m62CurvatureSquared F c t x + m62TangentRicci F c t x) *
          curveSpeed F c t x)) t
  total_curvature_integral : ∀ s t : ℝ,
    s ∈ Set.Icc a T → t ∈ Set.Icc a T → s ≤ t →
      m62TotalCurvature F c t - m62TotalCurvature F c s ≤
        ∫ r in s..t, (m62C1 K0 K1 K2 + K2) * m62TotalCurvature F c r +
          m62C1 K0 K1 K2 * m62Length F c r
  length_exponential : ∀ s t : ℝ,
    s ∈ Set.Icc a T → t ∈ Set.Icc a T → s ≤ t →
      m62Length F c t ≤ m62Length F c s * Real.exp (K2 * (t - s))
  total_exponential : ∀ s t : ℝ,
    s ∈ Set.Icc a T → t ∈ Set.Icc a T → s ≤ t →
      m62TotalCurvature F c t + m62Length F c t ≤
        (m62TotalCurvature F c s + m62Length F c s) *
          Real.exp ((m62C1 K0 K1 K2 + K2) * (t - s))
  energy_integrable : IntervalIntegrable
    (fun t => ∫ x in (0 : ℝ)..curvePeriod,
      m62CurvatureSquared F c t x * curveSpeed F c t x)
    MeasureTheory.volume a T
  energy_bound : (∫ t in a..T, ∫ x in (0 : ℝ)..curvePeriod,
      m62CurvatureSquared F c t x * curveSpeed F c t x) ≤
    m62Length F c a * Real.exp (K2 * (T - a))


noncomputable def m63RampRatio {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (ε t x : ℝ) : ℝ :=
  m62RegularizedCurvature P.flow c ε t x / m62Slope P c t x



structure M63C2SlopeLaws {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (T K2 : ℝ) : Prop where
  abs_le_one : ∀ t ∈ Set.Icc a T, ∀ x, |m62Slope P c t x| ≤ 1
  evolution : ∀ t ∈ Set.Ioo a T, ∀ x,
    HasDerivAt (fun s => m62Slope P c s x)
      (m62ArcSecondDerivative P.flow c t (m62Slope P c t) x +
        (m62CurvatureSquared P.flow c t x + m62TangentRicci P.flow c t x) *
          m62Slope P c t x) t
  lower_bound : ∀ t ∈ Set.Ioo a T, ∀ x, 0 ≤ m62Slope P c t x →
    m62ArcSecondDerivative P.flow c t (m62Slope P c t) x - K2 * m62Slope P c t x ≤
      deriv (fun s => m62Slope P c s x) t



structure M63RampPreservation {F : RicciFlow n M (Set.Icc a b)}
    {circumference : ℝ} (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (T K0 K1 K2 : ℝ) : Prop where
  positive : ∀ t ∈ Set.Icc a T, M63IsRampAt P (fun x => c x t) t
  lower_slope : ∀ m : ℝ, 0 < m → (∀ x, m ≤ m62Slope P c a x) →
    ∀ t ∈ Set.Icc a T, ∀ x,
      m * Real.exp (-K2 * (t - a)) ≤ m62Slope P c t x
  degree_preserved : ∀ L : M63PositiveDegreeLift P (fun x => c x a),
    ∀ t ∈ Set.Icc a T,
      ∃ Lt : M63PositiveDegreeLift P (fun x => c x t), Lt.degree = L.degree
  ratio_time : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Ioo a T, ∀ x,
    DifferentiableAt ℝ (fun s => m63RampRatio P c ε s x) t
  ratio_evolution : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Set.Ioo a T, ∀ x,
    deriv (fun s => m63RampRatio P c ε s x) t ≤
      m62ArcSecondDerivative P.flow c t (m63RampRatio P c ε t) x +
        2 * m62ArcDerivative P.flow c t (m62Slope P c t) x / m62Slope P c t x *
          m62ArcDerivative P.flow c t (m63RampRatio P c ε t) x +
        (m62C1 K0 K1 K2 + K2) * m63RampRatio P c ε t x +
        m62C1 K0 K1 K2 / m62Slope P c t x
  ratio_bound : ∀ m R0 : ℝ, 0 < m → 0 ≤ R0 →
    (∀ x, m ≤ m62Slope P c a x) → (∀ x, m63RampRatio P c 1 a x ≤ R0) →
      ∀ t ∈ Set.Icc a T, ∀ x,
        m63RampRatio P c 1 t x ≤
          (R0 + m62C1 K0 K1 K2 * Real.exp (K2 * (T - a)) / m * (t - a)) *
            Real.exp ((m62C1 K0 K1 K2 + K2) * (t - a))
  curvature_bound : ∀ m R0 : ℝ, 0 < m → 0 ≤ R0 →
    (∀ x, m ≤ m62Slope P c a x) → (∀ x, m63RampRatio P c 1 a x ≤ R0) →
      ∀ t ∈ Set.Icc a T, ∀ x,
        m62Curvature P.flow c t x ≤
          (R0 + m62C1 K0 K1 K2 * Real.exp (K2 * (T - a)) / m * (t - a)) *
            Real.exp ((m62C1 K0 K1 K2 + K2) * (t - a))



def M63C2RampExistence {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) : Prop :=
  ∀ gamma : ℝ → P.charts.Point,
    Function.Periodic gamma curvePeriod →
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma →
    M63IsRampAt P gamma a →
      ∃ c : ℝ → ℝ → P.charts.Point,
        M63C2ShrinkingCurveOn P.flow c (Set.Icc a b) ∧
        (∀ x, c x a = gamma x) ∧
        M63IntrinsicRegularityOn P.flow c (Set.Icc a b) ∧
        ∀ t ∈ Set.Icc a b, M63IsRampAt P (fun x => c x t) t


def M63SmoothRampExistence {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) : Prop :=
  ∀ gamma : ℝ → P.charts.Point,
    Function.Periodic gamma curvePeriod →
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ gamma →
    M63IsRampAt P gamma a →
      ∃ c : ℝ → ℝ → P.charts.Point,
        M62ShrinkingCurve P.flow c ∧ (∀ x, c x a = gamma x) ∧
        M63IntrinsicRegularityOn P.flow c (Set.Icc a b) ∧
        ∀ t ∈ Set.Icc a b, M63IsRampAt P (fun x => c x t) t




structure M63UniformDerivativeEstimates {F : RicciFlow n M (Set.Icc a b)}
    (G : M63AmbientGeometry F) (L0 Theta0 : ℝ) where
  delta0 : ℝ
  delta0_positive : 0 < delta0
  delta0_lt_one : delta0 < 1
  radius0 : ℝ
  radius0_positive : 0 < radius0
  radius0_le_one : radius0 ≤ 1
  constant : ℕ → ℝ
  constant_nonnegative : ∀ i, 0 ≤ constant i
  local_curvature : ∀ circumference (h : 0 < circumference), circumference < 1 →
    ∀ c : ℝ → ℝ → (G.product circumference h).charts.Point,
      M63C2ShrinkingCurveOn (G.product circumference h).flow c (Set.Icc a b) →
      m62Length (G.product circumference h).flow c a ≤ L0 →
      m62TotalCurvature (G.product circumference h).flow c a ≤ Theta0 →
      ∀ s r : ℝ, a ≤ s → 0 < r → r ≤ radius0 → s + delta0 * r ^ 2 ≤ b →
        r ≤ m62Length (G.product circumference h).flow c s →
        M63SmallSubarcs (G.product circumference h).flow c s r delta0 →
        ∀ t ∈ Set.Ioc s (s + delta0 * r ^ 2), ∀ x,
          m63CurvatureJetSquared (G.product circumference h).flow c 0 t x ≤
            2 / (t - s)
  all_derivatives : ∀ circumference (h : 0 < circumference), circumference < 1 →
    ∀ c : ℝ → ℝ → (G.product circumference h).charts.Point,
      M63C2ShrinkingCurveOn (G.product circumference h).flow c (Set.Icc a b) →
      m62Length (G.product circumference h).flow c a ≤ L0 →
      m62TotalCurvature (G.product circumference h).flow c a ≤ Theta0 →
      ∀ s r : ℝ, a ≤ s → 0 < r → r < 1 →
        s + (delta0 * radius0 ^ 2) * r ^ 2 < b →
        r ≤ m62Length (G.product circumference h).flow c s →
        M63SmallSubarcs (G.product circumference h).flow c s r (delta0 * radius0 ^ 2) →
        ∀ t ∈ Set.Ioo s (s + (delta0 * radius0 ^ 2) * r ^ 2), ∀ i x,
          m63CurvatureJetSquared (G.product circumference h).flow c i t x ≤
            constant i / (t - s) ^ (i + 1)

end PoincareConjecture
